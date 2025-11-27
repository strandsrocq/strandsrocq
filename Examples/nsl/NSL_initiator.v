From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import NSL_protocol.

Set Implicit Arguments.

Section initiator_guarantees.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.

  Hypothesis s_is_NSL_init : NSL_initiator_strand Tname A B Na Nb s.

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
    uniquely_originates $Na ->
      forall n, originates $Na n -> n = (s, 0).
  Proof.
    intros Na_uniquely_originates n Horig.
    destruct (eq_node__t_dec n (s,0)); try easy.
    specialize (Na_originates_in_s0) as Horig1; st_implication Horig1.
    specialize (Na_uniquely_originates) as [nu [Horignu Huniq]].
    specialize (Huniq _ Horig1) as Horig1'.
    specialize (Huniq _ Horig) as Horig2'.
    now subst.
  Qed.

  Corollary originates_Na_implies_regular :
    forall K__P, uniquely_originates $Na ->
      forall n, originates $Na n -> ~penetrator_strand K__P (strand n).
  Proof.
    intros K__P Na_uniquely_originates n Horig.
    apply (originates_Na_implies_s0 Na_uniquely_originates) in Horig.
    inversion s_is_NSL_init.
    unfold not. intros Hp.
    now subst.
  Qed.

End initiator_guarantees.

