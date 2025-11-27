(*
  Initiator secrecy with a more specific/instantiated set
*)
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import NSL_protocol.
Require Import NSL_responder.
Require Import RelMinimal.
Require Import LogicalFacts.

Set Implicit Arguments.

(* This section covers the responder's guarantee in the NSL protocol *)
Section secrecy_responder_guarantee.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : edge_set__t.

  Definition K__P_AB (k : K) := k <> inv (PK A) /\ k <> inv (PK B).

  Hypothesis s_is_NSL_resp : NSL_responder_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_NSL : C_is_SS C (NSL_StrandSpace Tname K__P_AB).

  Fixpoint protected a :=
    match a with
    | $t => t <> Nb
    | A_τ | #_ => True
    | ⟨g⋅g'⋅h⟩_k =>
        (k = PK A /\ h = $B /\ g = $Na /\ g' = $Nb) \/ (* second protocol message *)
        (protected g /\ protected g' /\ protected h)
    | ⟨g⟩_k =>
        (k = PK B /\ g = $Nb ) \/
        protected g
    | g⋅h => protected g /\ protected h
    end.


  Lemma protected_prop_dec1 : forall (pk k : K) (h p g g' : 𝔸),
    {k = pk /\ h = p /\ g = $Na /\ g' = $Nb} + {~(k = pk /\ h = p /\ g = $Na /\ g' = $Nb) }.
  Proof.
    intros pk k h p g g'.
    destruct (K_eq_dec k pk); destruct (A_eq_dec h p); destruct (A_eq_dec g $Na); destruct (A_eq_dec g' $Nb). now left. all: now right.
  Qed.

  Lemma protected_prop_dec2 : forall (k : K) (t : 𝔸),
  {k = PK B /\ t = $Nb } + {~(k = PK B /\ t = $Nb) }.
  Proof.
    intros k t.
    destruct (K_eq_dec k (PK B)); destruct (A_eq_dec t $Nb); intuition.
  Qed.

  Lemma protected_dec : forall a, {protected a} + {~protected a}.
  Proof.
    induction a; simpl; try tauto. destruct (T_eq_dec t Nb); try tauto.
    destruct a as [|t|t|t k'|g h]; auto.
    - destruct (protected_prop_dec2 k τ); tauto.
    - destruct (protected_prop_dec2 k $t); tauto.
    - destruct (protected_prop_dec2 k #t); tauto.
    - destruct (protected_prop_dec2 k (⟨ k' ⟩_ t)); tauto.
    - destruct g as [|t1|t1|t1 k1|g1 h1];
      unfold protected in *.
      + destruct (protected_prop_dec2 k (τ ⋅ h)); tauto.
      + destruct (protected_prop_dec2 k ($t1 ⋅ h)); tauto.
      + destruct (protected_prop_dec2 k (#t1 ⋅ h)); tauto.
      + destruct (protected_prop_dec2 k ((⟨ k1 ⟩_ t1) ⋅ h)); tauto.
      + destruct (protected_prop_dec1 (PK A) k h $B g1 h1); tauto.
  Qed.
  #[local] Hint Resolve protected_dec : core.

  Definition NSp := fun t => ~protected t.
  #[local] Hint Unfold NSp : core.
  #[local] Hint Unfold uns term uns_term : core.

  (* decidability  *)
  Lemma NSp_dec : forall t, { NSp t } + { ~ NSp t }.
  Proof.
    intros t. unfold NSp.
    destruct (protected_dec t) as [Hsub2|Hsub2]; try now right.
    now left.
  Qed.

  (* The actual set *)
  Definition NS := N NSp C NSp_dec. (* Set S of Lemma 4.4 *)
  Definition NS_iff_inC_NSp := N_iff_inC_p NSp C NSp_dec.

  (* characterization through the MPT library *)
  Definition minimal_NS_then_mpt  := minimal_N_then_mpt NSp C_is_bundle NSp_dec.

  Lemma NSp_encrypt_protected1 :
    forall k h,
    protected h -> protected (⟨ h ⟩_ k).
  Proof.
    intros k h NSph.
    unfold NSp, protected in *. simpl.
    destruct h; try tauto.
    destruct h1; try tauto.
  Qed.
  #[local] Hint Resolve NSp_encrypt_protected1: core.

  Lemma NSp_encrypt_protected2 :
    forall k h,
    ~protected h -> protected (⟨ h ⟩_ k) ->
    k = PK A \/ k = PK B.
  Proof.
    intros k h NSph.
    unfold NSp, protected in *. simpl.
    destruct h; try tauto.
    destruct h1; try tauto.
  Qed.
  #[local] Hint Resolve NSp_encrypt_protected2: core.

  Lemma NS_no_minimal :
    $Na <> $Nb -> uniquely_originates $Nb ->
      forall m, In m NS -> ~is_minimal (bundle_le C) m NS.
  Proof.
    intros diff_nonces Nb_uniquely_originates m Hin Hmin.
    assert (Hin':=Hin).
    apply (NS_iff_inC_NSp) in Hin' as [HinC HNSp].
    pose (C_is_NSL' := C_is_NSL).
    specialize (C_is_NSL' m HinC).
    inversion C_is_NSL' as [s0 Hpen|A0 B0 Na0 Nb0 s0 Hini|A0 B0 Na0 Nb0 s0 Hres].

    - (* penetrator *)
      assert (Hpen':=Hpen).
      inversion Hpen as [t i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k Hpenkey i Htrace|k h i Htrace|k h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace.
      all: specialize (minimal_NS_then_mpt Htrace Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      all: simplify_prop in Hmpti; auto.

      + specialize (Nb_originates_in_n__20 Nb (t:=$Nb) m) as Horig2.
        st_implication Horig2.
        now apply (originates_Nb_implies_regular (K__P:=K__P_AB) s_is_NSL_resp) in Horig2.

      + now apply (NSp_encrypt_protected1 k) in Hand.

      +
        specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,0) m) as Hinm0.
        st_implication Hinm0.
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle(inv_PK_U_never_originates_regular C_is_NSL (U:=A)) Hpen' Htrace Hinm0) as HcontraA.
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle (inv_PK_U_never_originates_regular C_is_NSL (U:=B)) Hpen' Htrace Hinm0) as HcontraB.
        unfold penetrator_key, K__P_AB in *.
        st_implication HcontraA.
        st_implication HcontraB.
        specialize (NSp_encrypt_protected2 k h Hand1 Hand) as Hdec.
        now destruct Hdec.

    - (* initiator *)
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti.
      inversion s_is_NSL_resp; apply (f_equal tr) in H3; simpl in H3.
      autounfold in Hmpti; simpl in Hmpti.
      (* next destructs identify when Nb is subterm of (m,0) *)
      (* push not in Hmpti using Terms_decidability. *)
      simplify_prop in Hmpti; try tauto.
      destruct (T_eq_dec A0 Nb); subst; try easy.
      destruct (T_eq_dec Na0 Nb); try tauto.
      (* instead of the two destructs we could do
        simplify_prop in Hand using decidability but this generates
        two cases instead of one *)
      specialize (mpti_then_originates $Nb m) as Horig.
      simplify_term_in Horig.
      st_implication Horig.
      apply (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig.
      rewrite (node_as_pair m) in Horig.
      inversion Horig as [Hstrand]. rewrite Hstrand in H0.
      rewrite <-H3 in H0. inversion H0; subst. all: auto.
    - (* responder *)
      inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti.
      inversion s_is_NSL_resp; apply (f_equal tr) in H3; simpl in H3.
      autounfold in Hmpti; simpl in Hmpti.
      (* push not in Hmpti using Terms_decidability. *)
      simplify_prop in Hmpti.
      push not in Hand2 using Terms_decidability.
      intuition idtac; push not in H5 using Terms_decidability.
      (* next destructs identify when Nb is subterm of (m,1) *)

      specialize (mpti_then_originates $Nb m) as Horig.
      simplify_term_in Horig.
      (* push not in Hand0 using Terms_decidability. *)
      st_implication Horig.
      apply (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig.
      rewrite (node_as_pair m) in Horig.
      inversion Horig as [Hstrand]. rewrite Hstrand in H0.
      rewrite <-H3 in H0. inversion H0; subst. all: auto.
  Qed.

  Proposition responder_secrecy:
    $Na <> $Nb  -> uniquely_originates $Nb ->
    forall m, is_node_of m C ->
      $Nb ⊏ uns_term m ->
        protected (uns_term m).
  Proof.
    intros diff_nonces Nb_uniquely_originates m Hin Hmin.
    destruct (protected_dec (uns_term m)); auto.
    assert (In m NS). { apply (N_iff_inC_p). auto. }
    specialize (NS_no_minimal) as Hnomin.
    assert ({NS = nil} + {NS <> nil}) as NS_empty_dec by (repeat decide equality).
    destruct NS_empty_dec as [Hemp | Hnemp].
    - (* empty *) now rewrite Hemp in H.
    - (* nonempty *)
      specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec C) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (C:=C)) Hnemp) as [m' [Hin' Hmin']].
      now specialize (Hnomin diff_nonces Nb_uniquely_originates m' Hin').
  Qed.

  Corollary secrecy_of_Nb_neq:
    $Na <> $Nb  -> uniquely_originates $Nb ->
      forall m,
        is_node_of m C ->
            $Nb ⊏ uns_term m ->
              $Nb <> uns_term m.
  Proof.
    intros diff_nonces Nb_uniquely_originates m Hin Hmin HNa_eq_m.
    specialize (responder_secrecy diff_nonces Nb_uniquely_originates m Hin Hmin) as Hsub.
    all: rewrite <- HNa_eq_m in Hsub.
    all: now simpl in Hsub.
  Qed.

End secrecy_responder_guarantee.
