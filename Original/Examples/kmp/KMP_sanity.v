(* What the original closure proves about the runs of [KMP_runs]. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.
Require Import KMP_policies.
Require Import KMP_protocol.
Require Import KMP_closure.
Require Import KMP_secrecy.
Require Import KMP_policy_examples.
Require Import KMP_runs.

Set Implicit Arguments.

(** * The honest run *)

(** By computation, which is what keeps [K_m_dec] and [K_d_dec] transparent and
    what makes the reachability hypotheses below convertible. *)
Lemma initial_types_compute :
  initial_type C #k0 = KDn K2 /\ initial_type C #k1 = KDn K1.
Proof. split; reflexivity. Qed.

Lemma k0_never_in_the_clear :
  forall n, is_node_of n C -> #k0 <> uns_term n.
Proof.
  intros n Hn.
  apply (secrecy C_is_bundle C_is_KMP C_fresh_sound hierarchy_policy_is_closed (k := k0));
  [ exact Hn | constructor | exact (proj1 hierarchy_closure_keeps_its_keys) ].
Qed.

Lemma k1_never_in_the_clear :
  forall n, is_node_of n C -> #k1 <> uns_term n.
Proof.
  intros n Hn.
  apply (secrecy C_is_bundle C_is_KMP C_fresh_sound hierarchy_policy_is_closed (k := k1));
  [ exact Hn | constructor | exact (proj2 hierarchy_closure_keeps_its_keys) ].
Qed.

(** * The type confusion run *)

Lemma k0_created_as_a_data_key : initial_type C' #k0 = KDn K2.
Proof. reflexivity. Qed.

(** Not merely inapplicable: [k0] does appear in the clear, at the node
    [k0_appears_in_the_clear] names. *)
Corollary secrecy_unavailable_for_k0 :
  forall Π, is_closure leaky_policy Π -> Π ⊢ D ∈ initial_type C' #k0.
Proof. intros Π HΠ. now apply leaky_policy_reaches_D_from_K2. Qed.

(** And [k1], which [k1_never_in_the_clear_on_the_attack] keeps on this bundle. *)
Corollary secrecy_unavailable_for_k1 :
  forall Π, is_closure leaky_policy Π -> Π ⊢ D ∈ initial_type C' #k1.
Proof. intros Π HΠ. now apply leaky_policy_reaches_D_from_K1. Qed.

(** * The key injection run *)

(** Nothing here: by [secure_templates_reaches_D_from_*] the original closure
    reaches [D] from all the types, so it cannot prove security if any key. *)
