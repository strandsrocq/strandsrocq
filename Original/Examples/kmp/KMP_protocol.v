From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ListSet.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Require Import KMP_policies.

Set Implicit Arguments.

Section kmp_protocol.

  Inductive K_m : K -> Prop :=
    | K_master : forall u : U, K_m (SymK u).
  Inductive K_d : K -> Prop :=
    | K_device : forall u : U, K_d (SymK' u).

  Lemma K_m_dec : forall k, {K_m k} + {~K_m k}.
  Proof.
    destruct k. now left. all: now right.
  Defined.

  Lemma K_d_dec : forall k, {K_d k} + {~K_d k}.
  Proof.
    destruct k. 2: now left. all: now right.
  Defined.

  Lemma K_m_then_not_K_d : forall k, K_m k -> ~ K_d k.
  Proof.
    unfold not. intros k Hm Hd. inversion Hm; inversion Hd.
    now subst.
  Qed.

  Lemma K_d_then_not_K_m : forall k, K_d k -> ~ K_m k.
  Proof.
    unfold not. intros k Hm Hd. inversion Hm; inversion Hd.
    now subst.
  Qed.

  (* Penetrator does not know master and device keys *)
  Definition K__P_md k := match k with
    | SymK u =>  False
    | SymK' u => False
    | _ => True
  end.

  Lemma K__P_md_then_not_K_d : forall k, K__P_md k -> ~ K_d k.
  Proof. intros. now destruct k. Qed.
  Lemma K__P_md_then_not_K_m : forall k, K__P_md k -> ~ K_m k.
  Proof. intros. now destruct k. Qed.
  Lemma K_d_then_not_K__P_md : forall k, K_d k -> ~ K__P_md k.
  Proof. intros. now destruct k. Qed.
  Lemma K_m_then_not_K__P_md : forall k, K_m k -> ~ K__P_md k.
  Proof. intros. now destruct k. Qed.

  (** [Fresh] in the following [KMP_strand] definition is a declaration, not a property: it has no meaning in this file. A strand space is intended only when [Fresh] is sound for the bundle under analysis, i.e. satisfies [fresh_sound_for] below; [KMP_secrecy.v] and [KMP_secrecy_closure_improved.v] assume it. *)
  Definition fresh_sound_for (Fresh : 𝔸 -> Prop) (B : bundle_type) : Prop :=
    forall t, Fresh t -> originates_at_most_once_in B t.

  (* The strand space is now defined as follows *)
  Inductive KMP_strand (π : policy__t) (Fresh : 𝔸 -> Prop) : Σ -> Prop :=
  | KMP_C : forall (k mk : K) (KT : KEY_T),
      K_d k /\ K_m mk /\ Fresh #k /\ set_In (KDn KT) (policy_types π) ->
      forall i, KMP_strand π Fresh (i,[⊕ ⟨ #k ⋅ $KT ⟩_mk])
  | KMP_E : forall (k mk : K) (KT : KEY_T) (m : K), K_m mk /\ (π ⊢ KT -[ Enc ]-> D) ->
      forall i, KMP_strand π Fresh (i,[⊖ #m; ⊖ ⟨ #k ⋅ $KT ⟩_mk; ⊕ ⟨ #m ⟩_k])
  | KMP_D : forall (k mk : K) (KT : KEY_T) (m : K), K_m mk /\ (π ⊢ KT -[ Dec ]-> D) ->
      forall i, KMP_strand π Fresh (i,[⊖ ⟨ #m ⟩_k; ⊖ ⟨ #k ⋅ $KT ⟩_mk; ⊕ #m])
  | KMP_W : forall (k1 k2 mk : K) (KT1 KT2 : KEY_T), K_m mk /\ (π ⊢ KT2 -[ Enc ]-> KDn KT1) ->
      forall i, KMP_strand π Fresh (i,[⊖ ⟨ #k1 ⋅ $KT1 ⟩_mk; ⊖ ⟨ #k2 ⋅ $KT2 ⟩_mk; ⊕ ⟨ #k1 ⟩_k2])
  | KMP_U : forall (k1 k2 mk : K) (KT1 KT2 : KEY_T), K_m mk /\ (π ⊢ KT2 -[ Dec ]-> KDn KT1) ->
      forall i, KMP_strand π Fresh (i,[⊖ ⟨ #k1 ⟩_k2; ⊖ ⟨ #k2 ⋅ $KT2 ⟩_mk; ⊕ ⟨ #k1 ⋅ $KT1 ⟩_mk]).

  Inductive KMP_StrandSpace (π : policy__t) (Fresh : 𝔸 -> Prop) : Σ -> Prop :=
    | KMPSS_Api : forall s, KMP_strand π Fresh s -> KMP_StrandSpace π Fresh s
    | KMPSS_Pen  : forall s, penetrator_strand K__P_md s -> KMP_StrandSpace π Fresh s.

  Lemma disjoint_regular_penetrator_strands :
      forall π Fresh s, ~ (KMP_strand π Fresh s /\ penetrator_strand K__P_md s).
  Proof.
      intros π Fresh s [Hr Hp].
      inversion Hr; apply (f_equal tr) in H0; simpl in H0;
      inversion Hp as [t i0 Htrace|g i0 Htrace|g i0 Htrace|g h i0 Htrace|g h i0 Htrace|k0 Hpenkey i0 Htrace|k0 h i0 Htrace|k0 h i0 Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace;
      (* encrypt and decrypt now carry a key, so their traces no longer clash with
         the penetrator's own encrypt and decrypt at the outermost constructor: the
         clash shows up one substitution deeper. *)
      first [ now rewrite <- Htrace in H0
            | (rewrite <- Htrace in H0; inversion H0; subst; discriminate) ].
  Qed.

End kmp_protocol.
