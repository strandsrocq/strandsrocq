(* The same policies against the improved closure, whose clauses 5 and 6 are
   tighter than the original ones. *)
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

From strandsrocq.Original.Instances Require Import DefaultInstances.
Require Import KMP_policies.
Require Import KMP_policy_examples.
Require Import KMP_closure_improved.

Set Implicit Arguments.

Example hierarchy_policy_is_closed_improved : is_closure hierarchy_policy hierarchy_closure.
Proof. repeat split; intros; closure_case. Qed.

(* Tightening clauses 5 and 6 does not rule the collapse out.  It costs one more
   ingredient, the reflexivity of clause 2 on [KDn K2]. *)
Theorem leaky_policy_reaches_D_from_K2_improved :
  forall Π, is_closure leaky_policy Π -> Π ⊢ D ∈ KDn K2.
Proof.
  intros Π [Hπ [Hrefl [_ [Hreach [Henc _]]]]].
  assert (Π ⊢ KDn K1 =[Enc]=> KDn K2) as Hw by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K1 =[Dec]=> KDn K1) as Hu by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 =[Dec]=> D)       as Hd by (apply Hπ; simpl; tauto).
  assert (Π ⊢ KDn K2 ∈ KDn K2) as Hr0 by (apply Hrefl; simpl; tauto).
  (* wrap a key encryption key, import it as one: the two levels now overlap *)
  assert (Π ⊢ KDn K1 ∈ KDn K2) as Hmix by (apply (Hreach (KDn K1)); tauto).
  (* so whatever wraps keys at the upper level wraps them at the lower one too *)
  assert (Π ⊢ KDn K2 =[Enc]=> KDn K2) as Hw0 by (apply (Henc (KDn K1) (KDn K2)); tauto).
  (* and a key that both wraps keys and decrypts data turns keys into data *)
  apply (Hreach (KDn K2)); tauto.
Qed.

(* [K1] survives here, where the original closure loses it.  This closure and the
   next were found by saturating outside Rocq: [is_closure] checks them, and nothing
   claims or needs them to be the least ones. *)
Definition leaky_closure : closure__t :=
  ( [ (KDn K1, Enc, KDn K2); (KDn K1, Enc, D)
    ; (KDn K1, Dec, KDn K2); (KDn K1, Dec, KDn K1)
    ; (KDn K2, Enc, KDn K2); (KDn K2, Enc, D)
    ; (KDn K2, Dec, KDn K2); (KDn K2, Dec, KDn K1); (KDn K2, Dec, D)
    ; (D, Enc, KDn K2);      (D, Enc, D)
    ; (D, Dec, KDn K2);      (D, Dec, KDn K1); (D, Dec, D) ]
  , [ (D, D); (D, KDn K2); (KDn K2, D); (KDn K2, KDn K2)
    ; (KDn K1, D); (KDn K1, KDn K2); (KDn K1, KDn K1) ] ).

Example leaky_policy_is_closed_improved : is_closure leaky_policy leaky_closure.
Proof. repeat split; intros; closure_case. Qed.

Example K1_survives_the_leaky_policy : ~ leaky_closure ⊢ D ∈ KDn K1.
Proof. simpl; intuition discriminate. Qed.

(* Its reachable sets are the four the paper reports. *)
Definition secure_templates_closure : closure__t :=
  ( [ (KDn K1, Enc, KDn K1); (KDn K1, Enc, KDn K2); (KDn K1, Enc, KDn K3)
    ; (KDn K1, Enc, D);  (KDn K1, Dec, KDn K2)
    ; (KDn K2, Enc, D);  (KDn K2, Dec, KDn K2)
    ; (KDn K3, Enc, D);  (KDn K3, Dec, D);      (KDn K3, Dec, KDn K2)
    ; (D, Enc, D);       (D, Dec, D);           (D, Dec, KDn K2) ]
  , [ (D, D); (KDn K1, KDn K1); (KDn K3, KDn K3)
    ; (KDn K2, KDn K2); (KDn K2, KDn K1); (KDn K2, KDn K3); (KDn K2, D) ] ).

Example secure_templates_is_closed : is_closure secure_templates secure_templates_closure.
Proof. repeat split; intros; closure_case. Qed.

Example secure_templates_keeps_its_keys :
  ~ secure_templates_closure ⊢ D ∈ KDn K1
  /\ ~ secure_templates_closure ⊢ D ∈ KDn K2
  /\ ~ secure_templates_closure ⊢ D ∈ KDn K3.
Proof. repeat split; simpl; intuition discriminate. Qed.
