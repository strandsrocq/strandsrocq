From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.
From Stdlib Require Import Logic.Decidable.

Require Import DefaultInstances.
Require Import Penetrator.

Set Implicit Arguments.

Section kmp_policies.

  Definition KEY_T := T.
  Inductive KEY_DATA_T := D : KEY_DATA_T | KDn : KEY_T -> KEY_DATA_T.
  Inductive label__t := Enc | Dec.

  Coercion KDn : KEY_T >-> KEY_DATA_T.

  Lemma KDn_injective : forall K0 K1, KDn K0 = KDn K1 -> K0 = K1.
  Proof.
    intros.
    destruct K0, K1.
    inversion H.
    reflexivity.
  Qed.

  (* Structure and operations of policies *)
  Definition policy_el__t : Type := (KEY_T * label__t * KEY_DATA_T).
  Definition policy__t : Type := set policy_el__t.

  (* Equalities *)
  Lemma KEY_DATA_T_eq_dec : forall x y : KEY_DATA_T, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Defined.

  Lemma policy__t_el_eq_dec : forall x y : policy_el__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Defined.

  Lemma policy__t_eq_dec : forall x y : policy_el__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Defined.

  Lemma dec_setIn_policy__t : forall (x : policy_el__t) y, decidable (set_In x y).
  Proof.
    red; intros. destruct (set_In_dec policy__t_el_eq_dec x y); subst.
    left; auto. right; auto.
  Defined.
End kmp_policies.

(* Membership notation for policies *)
Notation "π '⊢' K '-[' ℓ ']->' J" := (set_In (K, ℓ, J) π) (at level 70).
#[global] Hint Resolve dec_setIn_policy__t : Terms_decidability.
