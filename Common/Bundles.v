From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Arith.
From Stdlib Require Import ListSet.
From Stdlib Require Import Lists.List.
(* From Stdlib Require Import Lists.List Stdlib.Lists.ListSet Stdlib.Bool.Bool Stdlib.Bool.Sumbool. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From Stdlib Require Import Relations.Relation_Operators.
Require Import RelMinimal.
Import Nat.

Require Import Strands.
Require Import BundleRelations.

Import Stdlib.Lists.List.ListNotations.

Open Scope list_scope.

Set Implicit Arguments.

Module Type BundleSig
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St).

  Module Export BR := BundleRelations T St SSp.

  Record bundle_graph := {
    nodes : set node__t;
    intra : edge_set__t;   (* corresponds to n1 ==> n2 *)
    inter : edge_set__t    (* corresponds to n1 --> n2 *)
  }.

  Definition is_node_of n (B : bundle_graph) := set_In n (nodes B).
  Definition is_strand_of s (B : bundle_graph) := forall n,
    strand n = s ->
    index n < length (tr (strand n)) ->
    is_node_of n B.
  Definition edges (B : bundle_graph) := set_union eq_edge__t_dec (intra B) (inter B).
  Definition node_subset_of (N : set node__t) (B : bundle_graph) := 
    forall n, set_In n N -> is_node_of n B.

  Definition is_sub (B : bundle_graph) : Prop :=
    (** 0. edges are resp. subsets of [⟶] and [⟹] *)
    (forall n1 n2, is_edge_of n1 n2 (intra B) -> n1 ⟹ n2) /\
    (forall n1 n2, is_edge_of n1 n2 (inter B) -> n1 ⟶ n2) /\
    (** 0. edges should only relate nodes in [nodes B] *)
    (forall n1 n2, is_edge_of n1 n2 (intra B) -> set_In n1 (nodes B) /\ set_In n2 (nodes B)) /\
    (forall n1 n2, is_edge_of n1 n2 (inter B) -> set_In n1 (nodes B) /\ set_In n2 (nodes B)).

  Definition is_bundle (B : bundle_graph) :=
    (** 1. [B] is finite *)
    (** comes for free, set is defined inductively *)
    is_sub B /\
    (** 2. if [n1 ∈ nodes B] and [term(n1)] is negative, then there is a unique [n2 ∈ nodes B] s.t. n2 ⟶ n1 in [inter B]
    _NOTE_: we omit the [set_In n2 (nodes B)] part since it is implied by [is_edge_of n2 n1 (inter B)] (see above).*)
    (forall n1, set_In n1 (nodes B) -> is_negative n1 -> exists! n2, is_edge_of n2 n1 (inter B)) /\
    (** 3. if [n1] in [nodes B] and [n2 ⟹ n1], then [(n2, n1)] is in [intra B] *)
    (forall n1 n2, set_In n1 (nodes B) -> n2 ⟹ n1 -> is_edge_of n2 n1 (intra B)) /\
    (** 4. the graph is acyclic, i.e., the transitive closure of [edges B] is *not* reflexive! *)
    (forall n, not (edges B ⊢ n ≺ n)).

  Definition bundle_in_SS (B : bundle_graph) (SSp : Σ -> Prop) :=
    forall n, is_node_of n B -> SSp (strand n).
  Definition strandspace_bundle (B : bundle_graph) (SSp : Σ -> Prop) :=
    is_bundle B /\ bundle_in_SS B SSp.

  Section BundleProperties.
    Variable B : bundle_graph.
    Hypothesis B_is_bundle : is_bundle B.

    Lemma bundle_intrastrand_prefix_closed :
    forall n n',
      is_node_of n' B ->
      n ⟹+ n' ->
      is_node_of n B.
    Proof.
    intros n n' Hisnode Hplus.
    destruct B_is_bundle as [[_ [_ [Hintranode _]]] [_ [Hintrab _]]].
    
    induction Hplus as [n n' Hintra|n n' n'' Hplus1 IHHplus1 Hplus2 IHHplus2].
    - specialize (Hintrab n' n Hisnode Hintra).
      unfold is_edge_of in Hintrab. specialize (Hintranode _ _ Hintrab) as [Hn Hn']. assumption.
    - apply IHHplus2 in Hisnode. apply IHHplus1. assumption.
    Qed.

    Corollary index_lt_strand_implies_is_node_of:
      forall n n',
        index n < index n' ->
        strand n = strand n' ->
        is_node_of n' B ->
        is_node_of n B.
    Proof.
      intros n n' Hind Hstrand Hin.
      apply (bundle_intrastrand_prefix_closed (n':=n') Hin).
      apply (lt_intrastrand_index _ _ Hind Hstrand).
    Qed.

    Corollary last_node_implies_is_strand_of:
      forall n, index n = length (tr (strand n))-1 ->
        is_node_of n B ->
        is_strand_of (strand n) B.
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

    Lemma bundle_dec: forall n n' B, { is_edge_of n n' B } + { ~ is_edge_of n n' B }.
    Proof.
      intros.
      unfold is_edge_of.
      apply (set_In_dec eq_edge__t_dec (n, n')).
    Qed.
  End BundleProperties.

  Section BundleRelationProperties.
    Variable B : bundle_graph.
    Hypothesis B_is_bundle : is_bundle B.

    Local Notation E := (edges B).

    (* Under the assumption that E is acyclic, the decidability of bundle_lt can be proved
      using the decidability of bundle_le *)
    Lemma bundle_lt_dec :
      forall n1 n2, { E ⊢ n1 ≺ n2 } + { ~ E ⊢ n1 ≺ n2 }.
    Proof.
      intros n1 n2.
      destruct B_is_bundle as [_ [_ [_ Hacyclic]]].
      destruct (bundle_le_dec E n1 n2) as [Hle|Hnotle].
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
      E ⊢ n ≺ n' <-> bundle_ltb n n' = true.
    Proof.
      intros n n'.
      unfold bundle_ltb.
      destruct (bundle_lt_dec n n'); now easy.
    Qed.

    (* We can now prove Lemma 2.6 in two parts. First, the bundle_le relation is a partial order, i.e., it is a reflexive, antisymmetric and transitive.
    *)
    Lemma bundle_le_antisymm :
      antisymmetric node__t (bundle_le E).
    Proof.
      intros n n' Hlt1 Hlt2.
      destruct B_is_bundle as [_ [_ [_ Hacyclic]]].
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
    Lemma bundle_le_po : partialorder (bundle_le E).
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
        is_node_of n1 B ->
        n0 ⟹+ n1 ->
        E ⊢ n0 ⪯ n1.
    Proof.
      intros n0 n1 Hnode2 Hintra.
      unfold E, edges.
      destruct (B_is_bundle) as [_ [_ [Hintrab _]]].
      induction Hintra as [n0 n1 Hintra|n0 n1 n2 Hintra1 IH1 Hintra2 IH2] .
      - specialize (Hintrab _ _ Hnode2 Hintra).
        unfold is_edge_of in Hintrab.
        apply bundle_le_one. apply set_union_intro1; auto.
      - specialize (bundle_intrastrand_prefix_closed B_is_bundle Hnode2 Hintra2) as Hnode1.
        specialize (IH1 Hnode1).
        specialize (IH2 Hnode2).
        now apply (bundle_le_multi (n'':=n1)).
    Qed.

    Corollary index_le_strand_implies_bundle_le :
      forall n0 n1,
        index n0 <= index n1 ->
        strand n0 = strand n1 ->
        is_node_of n1 B ->
        E ⊢ n0 ⪯ n1.
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
        is_node_of n1 B ->
        n0 ⟹+ n1 ->
        E ⊢ n0 ≺ n1.
    Proof.
      intros n0 n1 Hnode2 Hintra.
      destruct (B_is_bundle) as [_ [_ [Hintrab _]]].
      induction Hintra as [n0 n1 Hintra|n0 n1 n2 Hintra1 IH1 Hintra2 IH2] .
      - specialize (Hintrab _ _ Hnode2 Hintra).
        unfold is_edge_of in Hintrab.
        apply bundle_lt_one.
        apply set_union_intro1; auto.
      - specialize (bundle_intrastrand_prefix_closed B_is_bundle Hnode2 Hintra2) as Hnode1.
        specialize (IH1 Hnode1).
        specialize (IH2 Hnode2).
        now apply (bundle_lt_multi (n':=n1)).
    Qed.

    Corollary index_lt_strand_implies_bundle_lt :
      forall n0 n1,
        index n0 < index n1 ->
        strand n0 = strand n1 ->
        is_node_of n1 B ->
        E ⊢ n0 ≺ n1.
    Proof.
      intros n0 n1 Hind Hstrand Hin.
      apply (intrastrand_implies_bundle_lt Hin).
      apply (lt_intrastrand_index _ _ Hind Hstrand).
    Qed.

  End BundleRelationProperties.

  Section BundleMinimal.
    Variable B : bundle_graph.
    Hypothesis B_is_bundle : is_bundle B.
    Local Notation E := (edges B).
    
    (* Second part of Lemma 2.6 of S&P paper *)
    Definition sign_closed (N : set node__t) :=
      node_subset_of N B ->
      forall m m',
        is_node_of m B ->
        is_node_of m' B ->
        uns_term m = uns_term m' ->
        (set_In m N <-> set_In m' N).

    (* Lemma 2.7: the minimal element of a sign-closed set of nodes is positive *)
    Lemma minimal_is_positive :
      forall (N : set node__t),
        node_subset_of N B ->
        sign_closed N ->
        forall m, set_In m N ->
            is_minimal (bundle_le E) m N ->
            is_positive m.
    Proof.
      intros N Hsubset Hsign m Hin Hisminimal.
      destruct (B_is_bundle) as [[_ [Hclose [_ Hinter]]] [Hb2 _]].
      unfold is_positive.
      destruct (term m) as [tplus|tminus] eqn:Ht.
      - trivial.
      - unfold node_subset_of in Hsubset.
        assert (Hsubset':=Hsubset).
        specialize (Hsubset m Hin).
        assert (is_negative m) as Hnegative. { unfold is_negative. rewrite Ht. trivial. }
        specialize (Hb2 m Hsubset Hnegative).
        destruct Hb2 as [n2 [Hcontra _]].
        unfold is_edge_of in Hcontra.
        specialize (bundle_le_one _ _ _ Hcontra) as Hcontra'.
        specialize (Hclose _ _ Hcontra).
        unfold interstrand in Hclose.
        destruct (term n2) as [n2plus|n2minus] eqn:Hn2. all: auto.
        rewrite Ht in Hclose.
        unfold sign_closed in Hsign.
        specialize (Hsign Hsubset' n2 m).
        unfold uns_term in Hsign. rewrite Hn2 in Hsign. rewrite Ht in Hsign. apply Hsign in Hclose. destruct Hclose as [_ Hintra]. apply Hintra in Hin as Hin2.
        unfold is_minimal in Hisminimal.
        specialize (Hisminimal Hin n2 Hin2).
        destruct (eq_node__t_dec n2 m) as [Heq|Hneq].
        all: try (apply Hinter in Hcontra as [Hcontra _]; auto).
        + subst. rewrite Hn2 in Ht. discriminate Ht.
        + apply Hisminimal in Hneq. apply Hneq. now apply bundle_le_union.
    Qed.

    (* This property is necessary to prove the S&P results. Authors of the original paper missed it *)
    Definition sign_closed_weak (N : set node__t) :=
      node_subset_of N B ->
      forall m,
        set_In m N -> is_negative m ->
        exists m', set_In m' N /\ is_positive m' /\ E ⊢ m' ≺ m.

    (*
      Any negative node is preceded (≺) by a positive node with the same uns_term.
      This lemma is useful to prove sign_closed_weak.
    *)
    Lemma interstrand_exists_prec_positive_lt_uns:
      forall m,
        is_node_of m B -> is_negative m ->
        exists m',
          is_node_of m' B /\ is_positive m' /\ E ⊢ m' ≺ m /\ uns_term m = uns_term m'.
    Proof.
      intros m HinC Hneg.
      destruct (B_is_bundle) as [[_ [Hclose [_ Hintersub]]] [Hinter _]].
      specialize (Hinter _ HinC Hneg).
      destruct Hinter as [m' [Hedge _]].
      exists m'.
      specialize (Hclose _ _ Hedge).
      unfold interstrand in Hclose.
      destruct (term m') as [t'|t'] eqn:Hm'; try contradiction.
      destruct (term m) as [t|t] eqn:Hm; try contradiction.
      repeat split.
      - apply Hintersub in Hedge as [Hedge _]; auto.
      - unfold is_positive. now rewrite Hm'.
      - apply (bundle_lt_one). apply set_union_intro; auto.
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
        node_subset_of N B ->
        sign_closed_weak N ->
        forall m, set_In m N ->
            is_minimal (bundle_le E) m N ->
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
      exists_minimal eq_node__t_dec (bundle_le_dec E) (bundle_le_antisymm B_is_bundle) (bundle_le_trans (E:=E)).

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

