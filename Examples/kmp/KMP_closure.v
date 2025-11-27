From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import KMP_policies.

Set Implicit Arguments.

Section kmp_closure.
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
  Notation "Π1 '⊴' Π2" := (closure__t_leq Π1 Π2) (at level 40).
  Notation "Π '⊢' K '=[' ℓ ']=>' J" := (set_In (K, ℓ, J) (fst Π)) (at level 70).
  Notation "Π '⊢' K '∈' Z" := (set_In (K, Z) (snd Π)) (at level 70).

  (* This definition is taken as-is from the closure definition in the paper *)
  Definition is_closure (π : policy__t) (Π : closure__t) : Prop :=
    (* 1. fst Π includes π *) (forall KT ℓ JT, π ⊢ KT -[ℓ]-> JT -> Π ⊢ (KDn KT) =[ℓ]=> JT) /\
    (* 2. ℜ is reflexive *) (forall (KT : KEY_DATA_T), Π ⊢ KT ∈ KT) /\
    (* 3. (D, ℓ, D) belongs to fst Π *) (Π ⊢ D =[Enc]=> D /\ Π ⊢ D =[Dec]=> D) /\
    (* 4. enc/dec reach. rule *) (forall KT JT ZT, Π ⊢ KT =[Enc]=> JT /\ Π ⊢ KT =[Dec]=> ZT -> Π ⊢ ZT ∈ JT) /\
    (* 5. enc head enable *) (forall KT JT ZT, Π ⊢ KT =[Enc]=> JT /\ (Π ⊢ KT ∈ ZT \/ Π ⊢ ZT ∈ KT) -> Π ⊢ ZT =[Enc]=> JT) /\
    (* 6. enc tail enable *) (forall KT JT ZT, Π ⊢ JT =[Enc]=> KT /\ (Π ⊢ KT ∈ ZT \/ Π ⊢ ZT ∈ KT) -> Π ⊢ JT =[Enc]=> ZT).
End kmp_closure.

(* (Local) Notation for closure inclusion and belonging *)
Notation "Π1 '⊴' Π2" := (closure__t_leq Π1 Π2) (at level 40).
Notation "Π '⊢' K '=[' ℓ ']=>' J" := (set_In (K, ℓ, J) (fst Π)) (at level 70).
Notation "Π '⊢' K '∈' Z" := (set_In (K, Z) (snd Π)) (at level 70).
