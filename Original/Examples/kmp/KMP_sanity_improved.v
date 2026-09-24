(* The same runs as [KMP_sanity], read through the improved closure. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.
Require Import KMP_policies.
Require Import KMP_protocol.
Require Import KMP_policy_examples.
Require Import KMP_runs.
Require Import KMP_closure_improved.
Require Import KMP_secrecy_closure_improved.
Require Import KMP_policy_examples_improved.

Set Implicit Arguments.

(** * The honest run *)

Lemma k0_never_in_the_clear_improved :
  forall n, is_node_of n C -> #k0 <> uns_term n.
Proof.
  intros n Hn.
  apply (secrecy C_is_bundle C_is_KMP C_fresh_sound hierarchy_policy_is_closed_improved (k := k0));
  [ exact Hn | constructor | exact (proj1 hierarchy_closure_keeps_its_keys) ].
Qed.

Lemma k1_never_in_the_clear_improved :
  forall n, is_node_of n C -> #k1 <> uns_term n.
Proof.
  intros n Hn.
  apply (secrecy C_is_bundle C_is_KMP C_fresh_sound hierarchy_policy_is_closed_improved (k := k1));
  [ exact Hn | constructor | exact (proj2 hierarchy_closure_keeps_its_keys) ].
Qed.

(** * The type confusion run *)

(** [k1] on the bundle where [k0] leaks.  Compare [secrecy_unavailable_for_k1]. *)
Lemma k1_never_in_the_clear_on_the_attack :
  forall n, is_node_of n C' -> #k1 <> uns_term n.
Proof.
  intros n Hn.
  apply (secrecy C'_is_bundle C'_is_KMP C'_fresh_sound
                 leaky_policy_is_closed_improved (k := k1));
  [ exact Hn | constructor | exact K1_survives_the_leaky_policy ].
Qed.

(** * The key injection run *)

(** The device key stays secret although the penetrator got a handle of its own. *)
Lemma k2_never_in_the_clear :
  forall n, is_node_of n C'' -> #k2 <> uns_term n.
Proof.
  intros n Hn.
  apply (secrecy C''_is_bundle C''_is_KMP C''_fresh_sound
                 secure_templates_is_closed (k := k2));
  [ exact Hn | constructor | exact (proj1 (proj2 secure_templates_keeps_its_keys)) ].
Qed.
