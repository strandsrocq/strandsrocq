(* Three example policies, and what the original closure concludes about each. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.
Require Import KMP_policies.
Require Import KMP_protocol.
Require Import KMP_closure.

Set Implicit Arguments.

Definition K1 : KEY_T := Text 1.
Definition K2 : KEY_T := Text 2.
Definition K3 : KEY_T := Text 3.

(* A two level hierarchy: [K1] keys wrap/unwrap [K2] keys, [K2] keys encrypt/decrypt data. *)
Definition hierarchy_policy : policy__t :=
  [ (K1, Enc, KDn K2); (K1, Dec, KDn K2)
  ; (K2, Enc, D);      (K2, Dec, D) ].

(* [ℜ] is the diagonal on the three types in play. *)
Definition hierarchy_closure : closure__t :=
  ( [ (KDn K1, Enc, KDn K2); (KDn K1, Dec, KDn K2)
    ; (KDn K2, Enc, D);      (KDn K2, Dec, D)
    ; (D, Enc, D);           (D, Dec, D) ]
  , [ (D, D); (KDn K2, KDn K2); (KDn K1, KDn K1) ] ).

Ltac closure_case :=
  simpl in *;
  repeat (match goal with
          | H : _ /\ _ |- _ => destruct H
          | H : _ \/ _ |- _ => destruct H
          | H : False |- _ => contradiction
          | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
          | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
          end); subst; simpl;
  repeat first [ left; reflexivity | right ]; auto 10.

Example hierarchy_policy_is_closed : is_closure hierarchy_policy hierarchy_closure.
Proof. repeat split; intros; closure_case. Qed.

(* both key types are secure *)
Example hierarchy_closure_keeps_its_keys :
  ~ hierarchy_closure ⊢ D ∈ KDn K2 /\ ~ hierarchy_closure ⊢ D ∈ KDn K1.
Proof. split; simpl; intuition discriminate. Qed.

(* The protocol can run under it. *)
Example creation_role_inhabited :
  forall k mk, K_d k -> K_m mk ->
    KMP_strand hierarchy_policy (fun a => a = #k) (0, [⊕ ⟨ #k ⋅ $K2 ⟩_mk]).
Proof. intros k mk Hd Hm. apply KMP_C; repeat split; try easy. simpl; auto. Qed.

(* One entry more in the policy: a [K1] key may unwrap at type [K1]. *)
Definition leaky_policy : policy__t :=
  (K1, Dec, KDn K1) :: hierarchy_policy.

(* The new policy leaks [K2] keys *)
Theorem leaky_policy_reaches_D_from_K2 :
  forall Π, is_closure leaky_policy Π -> Π ⊢ D ∈ KDn K2.
Proof.
  intros Π [Hπ [_ [_ [Hreach [Henc _]]]]].
  assert (Π ⊢ KDn K1 =[Enc]=> KDn K2) as Hw by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 =[Dec]=> KDn K1) as Hu by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Dec]=> D)       as Hd by (apply Hπ; simpl; tauto).
  (* wrap a key encryption key, import it as one: the two levels now overlap *)
  assert (Π ⊢ KDn K1 ∈ KDn K2) as Hmix by (apply (Hreach (KDn K1)); tauto).
  (* so whatever wraps keys at the upper level wraps them at the lower one too *)
  assert (Π ⊢ KDn K2 =[Enc]=> KDn K2) as Hw0 by (apply (Henc (KDn K1)); tauto).
  (* and a key that both wraps keys and decrypts data turns keys into data *)
  apply (Hreach (KDn K2)); tauto.
Qed.

(* [K1] as well, which [K1_survives_the_leaky_policy] keeps. *)
Theorem leaky_policy_reaches_D_from_K1 :
  forall Π, is_closure leaky_policy Π -> Π ⊢ D ∈ KDn K1.
Proof.
  intros Π [Hπ [_ [_ [Hreach [Henc Htail]]]]].
  assert (Π ⊢ KDn K1 =[Enc]=> KDn K2) as Hw by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 =[Dec]=> KDn K1) as Hu by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Dec]=> D)       as Hd by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 ∈ KDn K2) as Hmix by (apply (Hreach (KDn K1)); tauto).
  assert (Π ⊢ KDn K2 =[Enc]=> KDn K2) as Hw0 by (apply (Henc (KDn K1)); tauto).
  (* the step the [K2] proof does not need: clause 6 moves the target of that wrap
     up to the key encryption level *)
  assert (Π ⊢ KDn K2 =[Enc]=> KDn K1) as Hw1 by (apply (Htail (KDn K2)); tauto).
  apply (Hreach (KDn K2)); tauto.
Qed.

(* The secure templates policy, as Fig. 3 of the paper draws it, type names
   included: an unwrap always stamps the key it imports with the single type [K2]. *)
Definition secure_templates : policy__t :=
  [ (K1, Enc, KDn K1); (K1, Enc, KDn K2); (K1, Enc, KDn K3)
  ; (K1, Dec, KDn K2)
  ; (K2, Dec, KDn K2); (K2, Enc, D)
  ; (K3, Enc, D);      (K3, Dec, D) ].

(* The policy is secure, but the original closure reaches [D] from all three types.
   The step that does it is clause 6, read backwards. *)
Theorem secure_templates_reaches_D_from_K1 :
  forall Π, is_closure secure_templates Π -> Π ⊢ D ∈ KDn K1.
Proof.
  intros Π [Hπ [_ [[HDe HDd] [Hreach [_ Htail]]]]].
  assert (Π ⊢ KDn K1 =[Enc]=> KDn K1) as Hw1 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 =[Dec]=> KDn K2) as Hu  by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Enc]=> D)       as He2 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Dec]=> KDn K2) as Hu2 by (apply Hπ; simpl; tauto).
  (* an imported key is reachable from a wrap key, and from data *)
  assert (Π ⊢ KDn K2 ∈ KDn K1) as Hm1 by (apply (Hreach (KDn K1)); tauto).
  assert (Π ⊢ KDn K2 ∈ D)       as HmD by (apply (Hreach (KDn K2)); tauto).
  (* so data acquires the right to encrypt imported keys, then wrap keys *)
  assert (Π ⊢ D =[Enc]=> KDn K2) as HD2 by (apply (Htail D); tauto).
  assert (Π ⊢ D =[Enc]=> KDn K1) as HD1 by (apply (Htail (KDn K2)); tauto).
  apply (Hreach D); tauto.
Qed.

Theorem secure_templates_reaches_D_from_K2 :
  forall Π, is_closure secure_templates Π -> Π ⊢ D ∈ KDn K2.
Proof.
  intros Π [Hπ [_ [[HDe HDd] [Hreach [_ Htail]]]]].
  assert (Π ⊢ KDn K2 =[Enc]=> D)       as He2 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Dec]=> KDn K2) as Hu2 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 ∈ D)       as HmD by (apply (Hreach (KDn K2)); tauto).
  assert (Π ⊢ D =[Enc]=> KDn K2) as HD2 by (apply (Htail D); tauto).
  apply (Hreach D); tauto.
Qed.

Theorem secure_templates_reaches_D_from_K3 :
  forall Π, is_closure secure_templates Π -> Π ⊢ D ∈ KDn K3.
Proof.
  intros Π [Hπ [_ [[HDe HDd] [Hreach [_ Htail]]]]].
  assert (Π ⊢ KDn K2 =[Enc]=> D)      as He2 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Dec]=> KDn K2) as Hu2 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 =[Enc]=> KDn K3) as Hw3 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 =[Dec]=> KDn K2) as Hu1 by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 ∈ D)      as HmD by (apply (Hreach (KDn K2)); tauto).
  assert (Π ⊢ KDn K2 ∈ KDn K3) as Hm3 by (apply (Hreach (KDn K1)); tauto).
  assert (Π ⊢ D =[Enc]=> KDn K2) as HD2 by (apply (Htail D); tauto).
  assert (Π ⊢ D =[Enc]=> KDn K3) as HD3 by (apply (Htail (KDn K2)); tauto).
  apply (Hreach D); tauto.
Qed.
