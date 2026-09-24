From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Require Import NSL_protocol.

Set Implicit Arguments.

Section responder_guarantees.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : bundle_type.

  Hypothesis s_is_NSL_resp : NSL_responder_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.

  (* A few easy/trivial facts *)
  Property term_of_c :
    term (s, 1) = (⊕ ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A)).
  Proof.
    now inversion s_is_NSL_resp.
  Qed.
  #[local] Hint Rewrite term_of_c : core.

  Property uns_term_of_c :
    uns_term (s, 1) = ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A).
  Proof.
    now inversion s_is_NSL_resp.
  Qed.
  #[local] Hint Rewrite uns_term_of_c : core.

  (* Lemma 4.3 *)
  Lemma Nb_originates_in_c :
    $Na <> $Nb -> originates $Nb (s, 1).
  Proof.
    intros diff_nonces.
    apply mpti_then_originates.
    inversion s_is_NSL_resp.
    simplify_prop in |- *.
  Qed.

  Lemma Nb_originates_in_n__20 :
    forall t n__2, $Nb ⊏ t ->
    [⊕ t] = tr (strand n__2) ->
    originates $Nb (strand n__2, 0).
  Proof.
    intros t n__2 Hsubterm Htrace.
    apply mpti_then_originates; simpl; now rewrite <- Htrace.
  Qed.

  Lemma originates_Nb_implies_c :
    $Na <> $Nb -> originates_at_most_once_in C $Nb ->
    forall n, is_node_of n C -> originates $Nb n -> n = (s, 1).
  Proof.
    intros diff_nonces Nb_originates_at_most_once n Hnode Horig.
    destruct (eq_node__t_dec n (s,1)); try easy.
    specialize (Nb_originates_in_c diff_nonces) as Horig1.
    assert (is_node_of (s, 1) C) as Hnode1 by 
      (inversion s_is_NSL_resp;
      apply s_strand_of_C; [easy | simpl;lia]).
    now specialize (Nb_originates_at_most_once _ _ Hnode Hnode1 Horig Horig1).
  Qed.

  Corollary originates_Nb_implies_regular :
    forall K__P, $Na <> $Nb -> originates_at_most_once_in C $Nb ->
      forall n, is_node_of n C -> originates $Nb n -> ~penetrator_strand K__P (strand n).
  Proof.
    intros K__P diff_nonces Nb_originates_at_most_once n Hnode Horig.
    apply (originates_Nb_implies_c diff_nonces Nb_originates_at_most_once Hnode) in Horig.
    inversion s_is_NSL_resp.
    unfold not. intros Hp.
    now subst.
  Qed.
End responder_guarantees.

