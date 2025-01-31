Require Import Coq.Init.Datatypes.
Require Import Arith.
Require Import ListSet.
Require Import Coq.Lists.List Coq.Lists.ListSet Coq.Bool.Bool Coq.Bool.Sumbool.
Require Import Lia.
Require Import Relations.
Require Import Relations.Relation_Operators.
Require Import RelMinimal.
Import Nat.

Require Import Strands.
Require Import BundleRelations.

Import Coq.Lists.List.ListNotations.

Open Scope list_scope.

Set Implicit Arguments.

Module Type BundleSig
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St).

  Module Export BR := BundleRelations T St SSp.

  Definition is_bundle (C : edge_set__t) :=
    (* 0. C is a subset of ⟶ U ⟹ *)
    is_sub C /\
    (* 1. C is finite *)
    (* comes for free, set is defined inductively *)
    (* 2. if n1 ∈ N_C and term(n1) is negative, then there is a unique n2 s.t. n2 ⟶ n1 in C *)
    (forall n1, is_node_of n1 C -> is_negative n1 -> exists! n2, is_edge_of n2 n1 C /\ interstrand n2 n1) /\
    (* 3. if n1 in N_C and n2 ⟹ n1, then n2 ⟹ n1 in C *)
    (forall n1 n2, is_node_of n1 C -> intrastrand n2 n1 -> is_edge_of n2 n1 C) /\
    (* 4. C is acyclic, i.e., the transitive closure is *not* reflexive! *)
    (forall n, not (C ⊢ n ≺ n)).

  Definition C_is_SS (C : edge_set__t) (SSp : Σ -> Prop) :=
    forall n, is_node_of n C -> SSp (strand n).
  Definition strandspace_bundle (C : edge_set__t) (SSp : Σ -> Prop) :=
    is_bundle C /\ C_is_SS C SSp.

  Section BundleProperties.
    Variable C : edge_set__t.
    Hypothesis C_is_bundle : is_bundle C.

    Lemma bundle_intrastrand_prefix_closed :
    forall n n',
      is_node_of n' C ->
      n ⟹+ n' ->
      is_node_of n C.
    Proof.
    intros n n' Hisnode Hplus.
    destruct C_is_bundle as [_ [_ [Hintrab _]]].
    induction Hplus as [n n' Hintra|n n' n'' Hplus1 IHHplus1 Hplus2 IHHplus2].
    - specialize (Hintrab n' n Hisnode Hintra).
      unfold is_edge_of in Hintrab. specialize (is_edge_of_implies_is_node_of _ _ _ Hintrab) as [Hn Hn']. assumption.
    - apply IHHplus2 in Hisnode. apply IHHplus1. assumption.
    Qed.

    Corollary index_lt_strand_implies_is_node_of:
      forall n n',
        index n < index n' ->
        strand n = strand n' ->
        is_node_of n' C ->
        is_node_of n C.
    Proof.
      intros n n' Hind Hstrand Hin.
      apply (bundle_intrastrand_prefix_closed (n':=n') Hin).
      apply (lt_intrastrand_index _ _ Hind Hstrand).
    Qed.

    Corollary last_node_implies_is_strand_of:
      forall n, index n = length (tr (strand n))-1 ->
        is_node_of n C ->
        is_strand_of (strand n) C.
      Proof.
      intros n Hindex1 Hnodeof.
      unfold is_strand_of. intros m Hstrand Hindex.
      destruct (eq_dec (index m) (length (tr (strand n)) - 1)) as [Hi2|Hother].
      - assert (m=n) by (now rewrite (node_as_pair m), (node_as_pair n), Hstrand, Hi2, Hindex1).
        now subst.
      - rewrite Hstrand in Hindex.
        assert (index m < index n) by lia.
        now apply (index_lt_strand_implies_is_node_of _ _ H Hstrand).
    Qed.

    Lemma bundle_dec: forall n n' C, { is_edge_of n n' C } + { ~ is_edge_of n n' C }.
    Proof.
      intros.
      unfold is_edge_of.
      apply (set_In_dec eq_edge__t_dec (n, n')).
    Qed.
  End BundleProperties.

  Section BundleRelationProperties.
    Variable C : edge_set__t.
    Hypothesis C_is_bundle : is_bundle C.
    (* Under the assumption that C is acyclic, the decidability of bundle_lt can be proved
      using the decidability of bundle_le *)
    Lemma bundle_lt_dec :
      forall n1 n2, { C ⊢ n1 ≺ n2 } + { ~ C ⊢ n1 ≺ n2 }.
    Proof.
      intros n1 n2.
      destruct C_is_bundle as [_ [_ [_ Hacyclic]]].
      destruct (bundle_le_dec C n1 n2) as [Hle|Hnotle].
      - apply bundle_le_then_lt in Hle.
        destruct (eq_node__t_dec n1 n2). subst.
        + right. apply Hacyclic.
        + left. tauto.
      - right. unfold not. intros Hlt. now apply bundle_lt_then_le in Hlt.
    Qed.

    Definition bundle_ltb n n': bool :=
      if bundle_lt_dec n n' then true else false.

    Lemma bundle_ltb_iff_bundle_lt :
      forall n n',
      C ⊢ n ≺ n' <-> bundle_ltb n n' = true.
    Proof.
      intros n n'.
      unfold bundle_ltb.
      destruct (bundle_lt_dec n n'); now easy.
    Qed.

    (* We can now prove Lemma 2.6 in two parts. First, the bundle_le relation is a partial order, i.e., it is a reflexive, antisymmetric and transitive.
    *)
    Lemma bundle_le_antisymm :
      antisymmetric node__t (bundle_le C).
    Proof.
      intros n n' Hlt1 Hlt2.
      destruct C_is_bundle as [_ [_ [_ Hacyclic]]].
      destruct (eq_node__t_dec n n') as [Heq | Hneq].
      - (* n = n' *) assumption.
      - (* n <> n' *)
        apply bundle_le_then_lt in Hlt1.
        destruct Hlt1 as [Heq1 | Hprec1].
        + contradiction.
        + apply bundle_le_then_lt in Hlt2.
          destruct Hlt2 as [Heq2 | Hprec2].
          * symmetry. assumption.
          * specialize (bundle_lt_multi Hprec1 Hprec2) as Hprec. specialize (Hacyclic n). contradiction.
    Qed.

    Definition partialorder T R := reflexive T R /\ antisymmetric T R /\ transitive T R.

    (* First part of Lemma 2.6 of the S&P paper. *)
    Lemma bundle_le_po : partialorder (bundle_le C).
    Proof.
      unfold partialorder.
      split.
      - apply bundle_le_refl.
      - split.
        + apply bundle_le_antisymm.
        + apply bundle_le_trans.
    Qed.

    (** intrastrand and bundle_le facts **)
    Lemma intrastrand_implies_bundle_le :
      forall n0 n1,
        is_node_of n1 C ->
        n0 ⟹+ n1 ->
        C ⊢ n0 ⪯ n1.
    Proof.
      intros n0 n1 Hnode2 Hintra.
      destruct (C_is_bundle) as [_ [_ [Hintrab _]]].
      induction Hintra as [n0 n1 Hintra|n0 n1 n2 Hintra1 IH1 Hintra2 IH2] .
      - specialize (Hintrab _ _ Hnode2 Hintra).
        unfold is_edge_of in Hintrab.
        now apply bundle_le_one.
      - specialize (bundle_intrastrand_prefix_closed C_is_bundle Hnode2 Hintra2) as Hnode1.
        specialize (IH1 Hnode1).
        specialize (IH2 Hnode2).
        now apply (bundle_le_multi (n'':=n1)).
    Qed.

    Corollary index_le_strand_implies_bundle_le :
      forall n0 n1,
        index n0 <= index n1 ->
        strand n0 = strand n1 ->
        is_node_of n1 C ->
        C ⊢ n0 ⪯ n1.
    Proof.
      intros n0 n1 Hind Hstrand Hin.
      destruct (eq_dec (index n0) (index n1)) as [Heqind|Hneqind].
      - rewrite (node_as_pair n0), (node_as_pair n1), Hstrand, Heqind.
        apply (bundle_le_zero).
      - apply (intrastrand_implies_bundle_le Hin).
        assert (index n0 < index n1) as Hind' by lia.
        apply (lt_intrastrand_index _ _ Hind' Hstrand).
    Qed.

    Lemma intrastrand_implies_bundle_lt :
      forall n0 n1,
        is_node_of n1 C ->
        n0 ⟹+ n1 ->
        C ⊢ n0 ≺ n1.
    Proof.
      intros n0 n1 Hnode2 Hintra.
      destruct (C_is_bundle) as [_ [_ [Hintrab _]]].
      induction Hintra as [n0 n1 Hintra|n0 n1 n2 Hintra1 IH1 Hintra2 IH2] .
      - specialize (Hintrab _ _ Hnode2 Hintra).
        unfold is_edge_of in Hintrab.
        now apply bundle_lt_one.
      - specialize (bundle_intrastrand_prefix_closed C_is_bundle Hnode2 Hintra2) as Hnode1.
        specialize (IH1 Hnode1).
        specialize (IH2 Hnode2).
        now apply (bundle_lt_multi (n':=n1)).
    Qed.

    Corollary index_lt_strand_implies_bundle_lt :
      forall n0 n1,
        index n0 < index n1 ->
        strand n0 = strand n1 ->
        is_node_of n1 C ->
        C ⊢ n0 ≺ n1.
    Proof.
      intros n0 n1 Hind Hstrand Hin.
      apply (intrastrand_implies_bundle_lt Hin).
      apply (lt_intrastrand_index _ _ Hind Hstrand).
    Qed.

  End BundleRelationProperties.

  Section BundleMinimal.
    Variable C : edge_set__t.
    Hypothesis C_is_bundle : is_bundle C.

    (* Second part of Lemma 2.6 of S&P paper *)
    Definition sign_closed (N : set node__t) :=
      node_subset_of N C ->
      forall m m',
        is_node_of m C ->
        is_node_of m' C ->
        uns_term m = uns_term m' ->
        (set_In m N <-> set_In m' N).

    (* Lemma 2.7: the minimal element of a sign-closed set of nodes is positive *)
    Lemma minimal_is_positive :
      forall (N : set node__t),
        node_subset_of N C ->
        sign_closed N ->
        forall m, set_In m N ->
            is_minimal (bundle_le C) m N ->
            is_positive m.
    Proof.
      intros N Hsubset Hsign m Hin Hisminimal.
      destruct (C_is_bundle) as [_ [Hb2 _]].
      unfold is_positive.
      destruct (term m) as [tplus|tminus] eqn:Ht.
      - trivial.
      - unfold node_subset_of in Hsubset.
        assert (Hsubset':=Hsubset).
        specialize (Hsubset m Hin).
        assert (is_negative m) as Hnegative. { unfold is_negative. rewrite Ht. trivial. }
        specialize (Hb2 m Hsubset Hnegative).
        destruct Hb2 as [n2 [[Hcontra Hintra] _]].
        unfold is_edge_of in Hcontra.
        specialize (bundle_le_one _ _ _ Hcontra) as Hcontra'.
        unfold interstrand in Hintra.
        destruct (term n2) as [n2plus|n2minus] eqn:Hn2. all: auto.
        rewrite Ht in Hintra.
        unfold sign_closed in Hsign.
        specialize (Hsign Hsubset' n2 m).
        unfold uns_term in Hsign. rewrite Hn2 in Hsign. rewrite Ht in Hsign. apply Hsign in Hintra. destruct Hintra as [_ Hintra]. apply Hintra in Hin as Hin2.
        unfold is_minimal in Hisminimal.
        specialize (Hisminimal Hin n2 Hin2).
        destruct (eq_node__t_dec n2 m) as [Heq|Hneq].
        all: try (apply is_edge_of_implies_is_node_of in Hcontra; destruct Hcontra; assumption).
        + subst. rewrite Hn2 in Ht. discriminate Ht.
        + apply Hisminimal in Hneq. contradiction.
    Qed.

    (* This property is necessary to prove the S&P results. Authors of the original paper missed it *)
    Definition sign_closed_weak (N : set node__t) :=
      node_subset_of N C ->
      forall m,
        set_In m N -> is_negative m ->
        exists m', set_In m' N /\ is_positive m' /\ C ⊢ m' ≺ m.

    (*
      Any negative node is preceded (≺) by a positive node with the same uns_term.
      This lemma is useful to prove sign_closed_weak.
    *)
    Lemma interstrand_exists_prec_positive_lt_uns:
      forall m,
        is_node_of m C -> is_negative m ->
        exists m',
          is_node_of m' C /\ is_positive m' /\ C ⊢ m' ≺ m /\ uns_term m = uns_term m'.
    Proof.
      intros m HinC Hneg.
      destruct (C_is_bundle) as [_ [Hinter _]].
      specialize (Hinter _ HinC Hneg).
      destruct Hinter as [m' [[Hedge Hinter] _]].
      exists m'.
      unfold interstrand in Hinter.
      destruct (term m') as [t'|t'] eqn:Hm'; try contradiction.
      destruct (term m) as [t|t] eqn:Hm; try contradiction.
      repeat split.
      - apply (is_edge_of_implies_is_node_of _ _ _ Hedge).
      - unfold is_positive. now rewrite Hm'.
      - apply (bundle_lt_one _ _ _ Hedge).
      - unfold uns_term. now rewrite Hm', Hm.
    Qed.

    Lemma sign_closed_implies_weak :
    forall N, sign_closed N -> sign_closed_weak N.
    Proof.
      unfold sign_closed.
      intros N Hsignclosed.
      unfold sign_closed_weak.
      intros Hsub m Hin Hneg.
      specialize (Hsignclosed Hsub m).
      assert (Hin_m:=Hin).
      apply Hsub in Hin.
      specialize (interstrand_exists_prec_positive_lt_uns _ Hin Hneg) as Hinter.
      destruct (Hinter) as [m' [Hin_m' [Hpos_m' [Hle Huns]]]].
      exists m'.
      repeat split; try assumption.
      now apply (Hsignclosed _ Hin Hin_m' Huns).
    Qed.

    (* Lemma 2.7 new: the minimal element of a sign-closed-weak set of nodes is positive *)
    Lemma minimal_is_positive_weak :
      forall (N : set node__t),
        node_subset_of N C ->
        sign_closed_weak N ->
        forall m, set_In m N ->
            is_minimal (bundle_le C) m N ->
            is_positive m.
    Proof.
      intros N Hsubset Hsign m Hin Hisminimal.
      assert (Hsubset':=Hsubset).
      unfold is_positive.
      destruct (term m) as [tplus|tminus] eqn:Ht.
      - trivial.
      - unfold node_subset_of in Hsubset.
        specialize (Hsubset m Hin).
        assert (is_negative m) as Hneg. { unfold is_negative. rewrite Ht. trivial. }
        unfold sign_closed_weak in Hsign.
        specialize (Hsign Hsubset' m Hin Hneg).
        destruct Hsign as [m' [Hin' [Hpos' Hmin']]].
        unfold is_minimal in Hisminimal.
        specialize (node_neg_pos_neq Hpos' Hneg) as Hneq.
        specialize (Hisminimal Hin m' Hin' Hneq).
        now apply (bundle_lt_then_le) in Hmin'.
    Qed.

    (* We partially instantiate has_minimal from RelMinimal with bundle stuff *)
    Definition exists_minimal_bundle :=
      exists_minimal eq_node__t_dec (bundle_le_dec C) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (C:=C)).

  End BundleMinimal.

End BundleSig.

(*
  WARNING!
  This Include is potentially dangerous if global assumptions (i.e., Axiom or Parameter) appear inside the Module Type. Always check that's not the case.
*)
Module Bundle
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St) <: BundleSig T St SSp.

  Include BundleSig T St SSp.
End Bundle.

