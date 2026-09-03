From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lists.ListSet.
(* From Stdlib Require Import Lists.SetoidList. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import String.

Import Stdlib.Lists.List.ListNotations.
Import Nat.
Open Scope list_scope.
Open Scope string_scope.

From strandsrocq.Common Require Import RelMinimal.

From strandsrocq.CPSA.Instances Require Import DefaultInstances.
Set Implicit Arguments.

Section PenetratorStrands.

  Variable K__P : Mesg -> Prop.
   
  (** Penetrators (i.e., attackers) *)
  Inductive penetrator_strand : Σ -> Prop :=
    | PT_M : forall (m : Mesg) i, isBasic m -> K__P m -> penetrator_strand (i, [⊕ m])
    | PT_C : forall (g h : Mesg) i, penetrator_strand (i, [⊖ g; ⊖ h; ⊕ g⋅h])
    | PT_S : forall (g h : Mesg) i, penetrator_strand (i, [⊖ g⋅h; ⊕ g; ⊕ h])
    | PT_E : forall (k h : Mesg) i, penetrator_strand (i, [⊖ k; ⊖ h; ⊕ ⟨h⟩_k])
    | PT_D : forall (k h : Mesg) i, penetrator_strand (i, [⊖ k⁻¹; ⊖ ⟨h⟩_k; ⊕ h])
    | PT_H : forall (m : Mesg) i, penetrator_strand (i, [⊖ m; ⊕ # m]).


  Lemma strand_trace : forall i t s, (i,t) = s -> t = tr s.
  Proof.
    intros. now rewrite <- H.
  Qed.
  (* Now definitions to define penetrator objects *)
  Definition penetrator_node (n : node__t) := penetrator_strand (strand n).
  (* Definition penetrator_key (k : K) := K__P k. *)

  Definition never_originates_regular m C :=
    forall n, is_node_of n C -> originates m n -> penetrator_node n.
  Definition originates_regular m C :=
    exists n, is_node_of n C /\ originates m n /\ ~ penetrator_node n.

End PenetratorStrands.

Section PenetratorBound.
  Variable B : bundle_type.
  Hypothesis B_is_bundle : is_bundle B.
  Local Notation E := (edges B).

  Proposition penetrator_bound_set :
    forall (K__P : Mesg -> Prop) (k__R : Mesg),
      isBasic k__R ->
      ~ K__P k__R ->
      never_originates_regular K__P k__R B ->
      Nsubt B k__R = nil.
  Proof.
    intros K__P k__R Hbasic Hnpen Hknreg.
    destruct (Nsubt B k__R) eqn:HN; try easy.
    (* by Lemma 2.6 the bundle_type has a minimal element m *)
    assert ((Nsubt B k__R) <> []) as HNsubt_non_empty by (now rewrite HN).
    specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec E) (bundle_le_antisymm B_is_bundle) (bundle_le_trans (E:=E)) HNsubt_non_empty) as [m [Hin0 Horig]].
    (* Lemma 2.8 guarantees that k__R in K originates in m *)
    apply (minimal_then_originates B_is_bundle _ Hin0) in Horig.
    apply (Nsubtiff_inC_p) in Hin0 as [HinC Hp].
    (* as a consequence, m is always a penetrator node by assumption Hnkreg *)
    specialize (Hknreg _ HinC Horig) as Hm_is_penetrator.
    (* apply is_penetrator in Hm_is_penetrator. *)
    (* We now go by cases on the penetrator traces and show that nodes_with_term is always empty *)
    inversion Hm_is_penetrator as [t i Hb Hpen H|g h i H|g h i H|g h i H|g h i H|k i H]; apply strand_trace in H.
    all: specialize (originates_then_mpt H Horig) as Hcontra; simpl in Hcontra.
    all: simplify_prop in Hcontra; try tauto.
    destruct t; simplify_prop in Hand.
  Qed.

  Proposition penetrator_bound :
    forall K__P k__R,
      isBasic k__R ->
      ~ K__P k__R ->
      never_originates_regular K__P k__R B ->
        (forall p, is_node_of p B -> penetrator_node K__P p ->
              ~ (k__R ⊏ (uns_term p))
        ).
  Proof.
      intros K__P k__R Hbasic Hisreg Hnorig p Hisnode Hpennode HcontraS.
      specialize (penetrator_bound_set (K__P:=K__P) Hbasic Hisreg Hnorig) as Hset.
      specialize (Nsubtiff_inC_p B k__R p) as [_ Hr].
      st_implication Hr.
      unfold Nsubt in *.
      now rewrite Hset in Hr.
  Qed.

  (* As corollaries of the penetrator bound, we prove that decryption and
    encryption keys that never originates on regular strands and are not
    penetrator keys can never be learned by the penetrator *)
  Corollary penetrator_never_learn_secure_decryption_key :
    forall K__P s h k k',
      never_originates_regular K__P k'⁻¹ B ->
      penetrator_strand K__P s ->
      [⊖ k⁻¹; ⊖ ⟨h⟩_k; ⊕ h] = tr s ->
      is_node_of (s,0) B ->
      isBasic k'⁻¹->
      ~ K__P k'⁻¹ ->
      k <> k'.
  Proof.
    intros K__P s h k k' Hneverorig Hpen Htrace HinC Hbasic Hnopenkey.
    specialize (penetrator_bound (K__P:=K__P) Hbasic Hnopenkey Hneverorig HinC) as Hbound.
    st_implication Hbound; simplify_term_in Hbound.
    unfold not. intros. subst. apply Hbound. now destruct k'.
  Qed.

  Corollary penetrator_never_learn_secure_encryption_key :
    forall K__P s h k k',
      never_originates_regular K__P k' B ->
      penetrator_strand K__P s ->
      [⊖ k; ⊖ h; ⊕ ⟨h⟩_k] = tr s ->
      is_node_of (s,0) B ->
      isBasic k' ->
      ~ K__P k' ->
      k <> k'.
  Proof.
    intros K__P s h k k' Hneverorig Hpen Htrace HinC Hbasic Hnopenkey.
    specialize (penetrator_bound (K__P:=K__P) Hbasic Hnopenkey Hneverorig HinC) as Hbound.
    st_implication Hbound; simplify_term_in Hbound.
    unfold not; intros; subst; apply Hbound; now destruct k'.
  Qed.

End PenetratorBound.
