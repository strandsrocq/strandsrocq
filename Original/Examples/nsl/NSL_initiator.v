From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Require Import NSL_protocol.

Set Implicit Arguments.

Section initiator_guarantees.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : bundle_type.

  Hypothesis s_is_NSL_init : NSL_initiator_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.

  (* A few easy/trivial facts *)
  Property term_of_s0 :
    term (s, 0) = (⊕ ⟨ $Na ⋅ $A ⟩_ PK B).
  Proof.
    now inversion s_is_NSL_init.
  Qed.
  #[local] Hint Rewrite term_of_s0 : core.

  Property uns_term_of_c :
    uns_term (s, 1) = (⟨ ($Na ⋅ $Nb) ⋅ $B ⟩_ PK A).
  Proof.
    now inversion s_is_NSL_init.
  Qed.
  #[local] Hint Rewrite uns_term_of_c : core.

  (* Lemma 4.3 *)
  Lemma Na_originates_in_s0 :
    originates $Na (s, 0).
  Proof.
    apply mpti_then_originates.
    inversion s_is_NSL_init.
    now simplify_prop in |- *.
  Qed.

  Lemma Na_originates_in_n__20 :
    forall t n__2, $Na ⊏ t -> [⊕ t] = tr (strand n__2) -> originates $Na (strand n__2, 0).
  Proof.
    intros t n__2 Hsubterm Htrace.
    apply mpti_then_originates; simpl; now rewrite <- Htrace.
  Qed.

  Lemma originates_Na_implies_s0 :
    originates_at_most_once_in C $Na ->
      forall n, is_node_of n C -> 
        originates $Na n -> n = (s, 0).
  Proof.
    intros Na_originates_at_most_once n Hnode Horig.
    destruct (eq_node__t_dec n (s,0)); try easy.
    specialize (Na_originates_in_s0) as Horig1; st_implication Horig1.
    assert (is_node_of (s, 0) C) as Hnode1 by 
      (inversion s_is_NSL_init;
      apply s_strand_of_C; [easy | simpl;lia]).
    now specialize (Na_originates_at_most_once _ _ Hnode Hnode1 Horig Horig1).
  Qed.

  Corollary originates_Na_implies_regular :
    forall K__P, originates_at_most_once_in C $Na ->
      forall n, is_node_of n C -> originates $Na n -> 
        ~penetrator_strand K__P (strand n).
  Proof.
    intros K__P Na_originates_at_most_once n Hnode Horig.
    apply (originates_Na_implies_s0 Na_originates_at_most_once Hnode) in Horig.
    inversion s_is_NSL_init.
    unfold not. intros Hp.
    now subst.
  Qed.

End initiator_guarantees.

