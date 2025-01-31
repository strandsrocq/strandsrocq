Require Import Lia.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import ListSet.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import KMP_policies.

Set Implicit Arguments.

Section kmp_closure_improved.

  (* Structure and definition of closures *)
  Definition cl_policy_el__t : Type := (KEY_DATA_T * label__t * KEY_DATA_T).
  Definition cl_policy__t : Type := set cl_policy_el__t.
  Definition reachable_el__t : Type := (KEY_DATA_T * KEY_DATA_T).
  Definition reachable__t : Type := set reachable_el__t.
  Definition closure__t : Type := (cl_policy__t * reachable__t).

  Lemma cl_policy__t_el_eq_dec : forall x y : cl_policy_el__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Qed.

  Lemma cl_policy__t_eq_dec : forall x y : cl_policy__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Qed.

  Lemma reachable__t_el_eq_dec : forall x y : reachable_el__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Qed.

  Lemma reachable__t_eq_dec : forall x y : reachable__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Qed.
  Definition reachable__t_leq := incl.

  Lemma closure__t_eq_dec : forall x y : closure__t, { x = y } + { x <> y }.
  Proof. repeat decide equality; apply U_eq_dec. Qed.

  Definition closure__t_leq (C C' : closure__t) := (incl (fst C) (fst C')) /\ (incl (snd C) (snd C')).

  (* (Local) Notation for closure inclusion and belonging *)
  Notation "C1 '⊴' C2" := (closure__t_leq C1 C2) (at level 40).
  Notation "C '⊢' K '=[' ℓ ']=>' J" := (set_In (K, ℓ, J) (fst C)) (at level 40).
  Notation "C '⊢' K '∈' Z" := (set_In (K, Z) (snd C)) (at level 40).

  Definition is_closure (π : policy__t) (Π : closure__t) : Prop :=
    (* 1. Π includes fst Π *) (forall KT ℓ JT, π ⊢ KT -[ℓ]-> JT -> Π ⊢ (KDn KT) =[ℓ]=> JT) /\
    (* 2. ℜ is reflexive *) (forall (KT : KEY_DATA_T), Π ⊢ KT ∈ KT) /\
    (* 3. (D, ℓ, D) belongs to fst Π *) (Π ⊢ D =[Enc]=> D /\ Π ⊢ D =[Dec]=> D) /\
    (* 4. enc/dec reach. rule *) (forall K J Z, Π ⊢ K =[Enc]=> J /\ Π ⊢ K =[Dec]=> Z -> Π ⊢ Z ∈ J) /\
    (* 5. enc enable *) (forall K J Z W, Π ⊢ K =[Enc]=> J /\ Π ⊢ K ∈ Z /\ Π ⊢ J ∈ W ->
                          Π ⊢ Z =[Enc]=> W) /\
    (* 6. dec enable *) (forall K J Z, Π ⊢ K =[Dec]=> J /\ Π ⊢ K ∈ Z -> Π ⊢ Z =[Dec]=> J).
End kmp_closure_improved.

Notation "C1 '⊴' C2" := (closure__t_leq C1 C2) (at level 40).
Notation "C '⊢' K '=[' ℓ ']=>' J" := (set_In (K, ℓ, J) (fst C)) (at level 40).
Notation "C '⊢' K '∈' Z" := (set_In (K, Z) (snd C)) (at level 40).
