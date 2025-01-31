Require Import Coq.Init.Datatypes.
Require Import Arith.
Require Import ListSet.
Require Import Coq.Lists.List Coq.Lists.ListSet Coq.Bool.Bool Coq.Bool.Sumbool.
Require Import Lia.
Require Import Relations.
Require Import Relations.Relation_Operators.
Require Import RelMinimal.
Import Nat.

Import Coq.Lists.List.ListNotations.

Open Scope list_scope.

Set Implicit Arguments.

(*
  Term signature: a set A with a subterm relation and a special empty term τ
  It is defined as a generic typeclass that can be instantiated as needed.

  NOTE: Most of the Strand theory and theorems do not depend on the particular
  instantiation of TermSig.
*)
Module Type TermSig.
  Parameter A : Set.
  Parameter subterm : A -> A -> Prop.
  Parameter τ : A.  (* a special element of A representing an empty term *)

  (* Decidability requirements *)
  Axiom A_eq_dec : forall a a' : A, { a = a' } + { a <> a'}.
  Axiom A_subterm_dec : forall a a' : A, { subterm a a' } + { ~(subterm a a')}.

  #[export] Hint Resolve A_eq_dec : core.
  #[export] Hint Resolve A_subterm_dec : core.
End TermSig.

Module SignedTerms (Import T : TermSig).
  Notation "a '⊏' a'" := (subterm a a') (at level 50, left associativity).

  (* (Signed) terms carry a sign indicating whether a term is being transmitted (+) or received (-) *)
  Inductive sT  := Plus : A -> sT | Minus : A -> sT.

  Definition uns (t : sT) :=
    match t with
    | Plus m
    | Minus m => m
    end.

  (* Definition is_positive_term_b t := match t with | Plus _ => true | _ => false end. *)
  Definition is_positive_term t :=
    match t with
    | Plus _ => True
    | _ => False
    end.

  Lemma sT_eq_dec : forall a a' : sT, { a = a' } + { a <> a'}.
  Proof.
      repeat (decide equality).
  Defined.

  Notation "'⊕' m" := (Plus m) (at level 90).
  Notation "'⊖' m" := (Minus m) (at level 90).
End SignedTerms.

Module Type StrandSig (Import T : TermSig).
  Module ST := SignedTerms T.
  Export ST.
  Parameter Σ : Set.
  Parameter tr : Σ -> list sT.
  (* Equality between strands must be decidable *)
  Axiom Σ_eq_dec : forall s s' : Σ, { s = s' } + { s <> s'}.
  #[export] Hint Resolve Σ_eq_dec : core.
End StrandSig.

Module Type StrandSpaceSig (Import T : TermSig) (Import St : StrandSig T).
  (*
    A node is a pair (s, i) where s is a strand and i is a natural number called index with the constraints below.
    Intuitively, the index can be used to refer to a particular term within the trace associated to the strand.
  *)
  Definition node__t : Set := Σ * nat.
  (* We can easily extract nodes components: *)
  Definition index (n : node__t) := snd n.
  Definition strand (n : node__t) := fst n.

  Lemma node_as_pair :
    forall n, n = (strand n, index n).
  Proof.
    intros. unfold strand, index.
    repeat rewrite <- surjective_pairing.
    reflexivity.
  Qed.

  Definition term (n : node__t) :=
    List.nth (index n) (tr (strand n)) (⊖ τ).
  (* This is just term, without the sign *)
  Definition uns_term (n : node__t) := uns (term n).

  Definition is_positive n := match term n with | ⊕ _ => True | _ => False end.
  Definition is_negative n := match term n with | ⊖ _ => True | _ => False end.

  Section NodeProperties.
    Lemma node_neg_pos_neq :
      forall n n', is_positive n -> is_negative n' -> n <> n'.
    Proof.
      intros n n' Hpos Hneg.
      unfold not.
      intros Hcontra. subst.
      unfold is_positive, is_negative in *.
      now destruct (term n').
    Qed.

    Lemma term_in_trace :
      forall n, index n < length (tr (strand n)) ->
        In (term n) (tr (strand n)).
    Proof.
      intros n Hlt. unfold term. apply nth_In. assumption.
    Qed.

    Lemma term_overflow :
      forall n,
      index n >= length (tr (strand n)) -> term n = ⊖ τ.
    Proof.
      intros n Hindex.
      unfold term.
      apply nth_overflow.
      lia.
    Qed.

    Lemma term_uns_overflow:
      forall n,
      index n >= length (tr (strand n)) -> uns_term n = τ.
    Proof.
      intros n Hindex.
      unfold uns_term.
      now rewrite (term_overflow n Hindex).
    Qed.

    Lemma node_positive_lt :
      forall n, is_positive n -> index n < length (tr (strand n)).
    Proof.
      intros n Hpos.
      destruct (lt_dec (index n) (length (tr (strand n)))); try easy.
      assert (index n >= length (tr (strand n))) as Hgte by lia.
      apply term_overflow in Hgte.
      unfold is_positive in Hpos; now rewrite Hgte in Hpos.
    Qed.

    Lemma node_pos_in_trace :
      forall n, is_positive n -> In (term n) (tr (strand n)).
    Proof.
      intros n Hpos.
      apply term_in_trace.
      now apply node_positive_lt.
    Qed.

    (* Decidability *)
    Lemma eq_node__t_dec :
      forall n n' : node__t, { n = n' } + { n <> n' }.
    Proof.
      intros. repeat (decide equality).
    Qed.
    Hint Resolve eq_node__t_dec : core.

    Lemma is_positive_dec :
      forall n, {is_positive n} + {~ is_positive n}.
    Proof.
      intros n.
      unfold is_positive.
      destruct (term n); auto.
    Qed.

    Lemma is_negative_dec :
      forall n, {is_negative n} + {~ is_negative n}.
    Proof.
      intros n.
      unfold is_negative.
      destruct (term n); auto.
    Qed.
  End NodeProperties.

  #[export] Hint Resolve Σ_eq_dec eq_node__t_dec : core.

  Section Edges.
    Definition interstrand n1 n2 : Prop :=
      match term n1, term n2 with ⊕ t1, ⊖ t2 => t1 = t2 | _, _ => False end.
    Definition interstrand_trans : node__t -> node__t -> Prop := clos_trans node__t interstrand.
    (* Definition intrastrand n1 n2 : Prop := strand n1 = strand n2 /\ index n1 + 1 = index n2. *)
    Definition intrastrand n1 n2 : Prop := (strand n1, index n1 + 1) = (strand n2, index n2).
    Definition intrastrand_trans : node__t -> node__t -> Prop := clos_trans node__t intrastrand.
    Notation "n1 '⟶' n2" := (interstrand n1 n2) (at level 60).
    Notation "n1 '⟶+' n2" := (interstrand_trans n1 n2) (at level 60).
    Notation "n1 '⟹' n2" := (intrastrand n1 n2) (at level 60).
    Notation "n1 '⟹+' n2" := (intrastrand_trans n1 n2) (at level 50).

    (* At page 2: By abuse of language, we will still treat signed 𝔸s ordinary terms, for instance as having subterms. *)
    Definition occurs t n := t ⊏ (uns_term n).

    (* These definitions are slightly imprecise in the S&P paper:
    - we need to take the transitive closure ⟹+ because when they say precedes they do not intend immediately ...
    *)
    Definition originates (t : A) (n : node__t) :=
      is_positive n /\ occurs t n /\ forall n', n' ⟹+ n -> ~ occurs t n'.
    Definition uniquely_originates (t : A) :=
      exists! n, originates t n.

    Definition edge__t : Set := node__t * node__t.
    Definition edge_set__t := set edge__t.

    Fixpoint nodes_of (C : edge_set__t) : set node__t :=
      match C with
      | [] => []
      | (n, n')::C' => n::n'::(nodes_of C')
      end.
    Definition is_node_of (n : node__t) (C : edge_set__t) :=
      set_In n (nodes_of C).
    Definition node_subset_of (N : set node__t) (C : edge_set__t) :=
      forall n, set_In n N -> is_node_of n C.
    Definition is_edge_of (n1 : node__t) (n2 : node__t) (C : edge_set__t) :=
      set_In (n1, n2) C.
    Definition is_sub C :=
      forall n1 n2, is_edge_of n1 n2 C -> n1 ⟶ n2 \/ n1 ⟹ n2.
    Definition is_strand_of s C := forall n,
      strand n = s ->
      index n < length (tr (strand n)) ->
      is_node_of n C.

    (* relating edges and nodes *)
    Lemma is_edge_of_implies_is_node_of :
      forall C n n',
        is_edge_of n n' C ->
        is_node_of n C /\ is_node_of n' C.
    Proof.
      induction C as [|(n'', n''') C' IHC].
      - intros n n' Hin. auto.
      - intros n n' Hin. apply in_inv in Hin. destruct Hin as [Heq | Hin].
        + inversion Heq. subst. unfold is_node_of. unfold nodes_of. destruct C'.
          * split. all: (simpl; auto).
          * fold nodes_of. simpl. auto.
        + apply IHC in Hin.
          destruct Hin as [Hnode Hnode'].
          destruct C'.
          * contradiction.
          * unfold is_node_of in *. simpl in *. auto.
    Qed.
  End Edges.

  (* Exporting notations *)
  Notation "n1 '⟶' n2" := (interstrand n1 n2) (at level 60).
  Notation "n1 '⟶+' n2" := (interstrand_trans n1 n2) (at level 60).
  Notation "n1 '⟹' n2" := (intrastrand n1 n2) (at level 60).
  Notation "n1 '⟹+' n2" := (intrastrand_trans n1 n2) (at level 50).

  Section IntrastrandProperties.
    Lemma lt_intrastrand_index_0 :
      forall i i' s, i < i' -> (s,i) ⟹+ (s,i').
    Proof with (unfold intrastrand; simpl; rewrite Nat.add_1_r; reflexivity).
      intros. generalize dependent i'. unfold intrastrand_trans.
      induction i' as [|i0 IHN].
      - lia.
      - intros Hlt. destruct (lt_dec i i0) as [Hlt'|Hnlt].
        + apply clos_tn1_trans.
          assert ((s, i0) ⟹ (s, S i0)) as Hstep. { trivial... }
          apply IHN in Hlt'. apply clos_trans_tn1 in Hlt'.
          apply (tn1_trans _ intrastrand (s, i) (s, i0) (s, S i0) Hstep Hlt').
        + assert (i = i0) by lia. apply t_step. subst...
    Qed.

    Lemma lt_intrastrand_index :
      forall n n', index n < index n' -> strand n = strand n' -> n ⟹+ n'.
    Proof.
      intros n n' Hlt Hstrand.
      specialize (lt_intrastrand_index_0 (strand n) Hlt) as H.
      rewrite Hstrand in H at 2.
      unfold strand, index in H.
      repeat rewrite <- surjective_pairing in H.
      assumption.
    Qed.

    Lemma intrastrand_index_lt :
      forall n n', n ⟹+ n' -> index n < index n'.
    Proof.
      intros n n' Hintra.
      unfold intrastrand_trans in Hintra.
      unfold intrastrand in Hintra.
      induction Hintra as [n n' Hindx| n n' n'' Hin1 IHH1 Hin2 IHH2].
      inversion Hindx. all: lia.
    Qed.

    Lemma intrastrand_same :
      forall n n', n ⟹+ n' -> strand n = strand n'.
    Proof.
      intros n n' Hintra.
      unfold intrastrand_trans in Hintra.
      unfold intrastrand in Hintra.
      induction Hintra as [n n' Hindx| n n' n'' Hin1 IHH1 Hin2 IHH2].
      inversion Hindx.
      - reflexivity.
      - rewrite IHH1. rewrite IHH2. reflexivity.
    Qed.

    Lemma intrastrand_irreflexive :
      forall n n', n ⟹+ n' -> n<>n'.
    Proof.
      intros n n' Hintra.
      specialize (intrastrand_index_lt Hintra) as Hlt.
      destruct (eq_node__t_dec n n') as [Heq | Hneq].
      - destruct n. destruct n'.
        inversion Heq.
        subst.
        apply Nat.lt_irrefl in Hlt.
        contradiction.
      - assumption.
    Qed.
  End IntrastrandProperties.

  Section OriginatesProperties.
    Lemma originates_lt:
      forall n t, originates t n -> index n < length (tr (strand n)).
    Proof.
      intros n t Horig. destruct Horig as [Hpos _].
      unfold is_positive, term in Hpos.
      destruct (lt_dec (index n) (length (tr (strand n)))) as [?|Hcontra]; try easy.
      assert (length (tr (strand n)) <= index n) as Hleq by lia.
      specialize (nth_overflow (tr (strand n)) (⊖ τ) Hleq) as Hnth.
      now rewrite Hnth in Hpos.
    Qed.

    Lemma index_0_positive_originates:
      forall n t,
        t ⊏ uns_term n ->
        is_positive n ->
        index n = 0 ->
        originates t n.
    Proof.
      intros n t Hsub Hpos Hi0.
      unfold originates.
      repeat split; try easy.
      intros n' Hintra.
      apply intrastrand_index_lt in Hintra; lia.
    Qed.

    Lemma uniquely_originates_same_strand :
      forall n n' t,
        uniquely_originates t ->
        originates t n ->
        originates t n' ->
        strand n = strand n'.
    Proof.
      intros n n' t Huniq Horign Horign'.
      inversion Huniq as [n'' [_ Huniq']].
      apply Huniq' in Horign.
      apply Huniq' in Horign'.
      rewrite Horign in Horign'.
      rewrite (node_as_pair n) in Horign'.
      rewrite (node_as_pair n') in Horign'.
      now inversion Horign'.
    Qed.
  End OriginatesProperties.

  Section Decidability.
    Lemma eq_edge__t_dec :
      forall e e' : edge__t, { e = e' } + { e <> e' }.
    Proof. decide equality. Qed.

    Lemma interstrand_dec :
      forall n n', { n ⟶ n' } + { ~ n ⟶ n' }.
    Proof.
      intros n n'.
      unfold interstrand in *.
      destruct (term n); destruct (term n'); try now right. apply A_eq_dec.
    Qed.

    Lemma intrastrand_dec :
      forall n n', { n ⟹ n' } + { ~ n ⟹ n' }.
    Proof.
      intros.
      unfold intrastrand in *.
      repeat (decide equality).
    Qed.
  End Decidability.
End StrandSpaceSig.

(*
  WARNING!
  This Include is potentially dangerous if global assumptions (i.e., Axiom or Parameter) appear inside the Module Type. Always check that's not the case.
*)
Module StrandSpace
  (Import T : TermSig)
  (Import St : StrandSig T) <: StrandSpaceSig T St.

  Include StrandSpaceSig T St.
End StrandSpace.






