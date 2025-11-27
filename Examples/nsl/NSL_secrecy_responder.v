From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import NSL_protocol.
Require Import NSL_responder.
Require Import RelMinimal.

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
    | A_τ | $_ | #_ => False
    | ⟨(g ⋅ g') ⋅ h⟩_(k) =>
        (k = PK A /\ h = $B /\ g' = $Nb /\ g = $Na) \/ (* second protocol message *)
        protected g \/  protected g' \/ protected h
    | ⟨g⟩_(k) =>
        (k = PK B /\ g = $Nb ) \/ (* third protocol message *)
        protected g
    | g⋅h => protected g \/ protected h
    end.

  Lemma protected_prop_dec1 : forall (pk k : K) (h p g g' : 𝔸),
    {k = pk /\ h = p /\ g = $Nb /\ g' = $Na } + {~(k = pk /\ h = p /\ g = $Nb /\ g' = $Na) }.
  Proof.
    intros pk k h p g g'.
    destruct (K_eq_dec k pk); destruct (A_eq_dec h p); destruct (A_eq_dec g $Nb). destruct (A_eq_dec g' $Na). now left. all: now right.
  Qed.

  Lemma protected_prop_dec2 : forall (k : K) (t : 𝔸),
    {k = PK B /\ t = $Nb } + {~(k = PK B /\ t = $Nb) }.
  Proof.
    intros k t.
    destruct (K_eq_dec k (PK B)); destruct (A_eq_dec t $Nb); intuition.
  Qed.

  Lemma protected_prop_dec3 : forall (pk k : K) (h g h : 𝔸),
    {k = pk /\ g ⋅ h = $Nb} + {~(k = pk /\ g ⋅ h = $Nb) }.
  Proof.
    intros.
    destruct (K_eq_dec k pk); destruct (A_eq_dec (g⋅h) $Nb). now left. all: now right.
  Qed.

  Lemma protected_dec : forall a, {protected a} + {~protected a}.
  Proof.
    induction a; simpl; try now right.
    - destruct a as [|t|t|t k'|g h]; auto.
      destruct (protected_prop_dec2 k τ); tauto.
      + destruct (protected_prop_dec2 k $t); tauto.
      + destruct (protected_prop_dec2 k #t); tauto.
      + destruct (protected_prop_dec2 k (⟨ k' ⟩_ t)); tauto.
      + destruct g as [|t1|t1|t1 k1|g1 h1].
        * destruct (protected_prop_dec3 (PK B) k h τ h); tauto.
        * destruct (protected_prop_dec3 (PK B) k h $t1 h); tauto.
        * destruct (protected_prop_dec3 (PK B) k h #t1 h); tauto.
        * destruct (protected_prop_dec3 (PK B) k h (⟨ k1 ⟩_ t1) h); tauto.
        * destruct (protected_prop_dec1 (PK A) k h $B h1 g1); unfold protected in *; tauto.
    - destruct IHa1; destruct IHa2; try (left; tauto); right; tauto.
  Qed.

  Definition NSp := fun t =>
    ($Nb ⊏ t) /\ (~protected t).
  #[local] Hint Unfold NSp : core.
  #[local] Hint Unfold uns term uns_term : core.

  (* decidability  *)
  Lemma NSp_dec : forall t, { NSp t } + { ~ NSp t }.
  Proof.
    intros t. unfold NSp.
    destruct (A_subterm_dec $Nb t) as [Hsub1|Hsub1];
    destruct (protected_dec t) as [Hsub2|Hsub2]; try now right.
    now left.
  Qed.

  (* The actual set *)
  Definition NS := N NSp C NSp_dec. (* Set S of Lemma 4.4 *)
  Definition NS_iff_inC_NSp := N_iff_inC_p NSp C NSp_dec.

  (* charaterization through the MPT library *)
  Definition minimal_NS_then_mpt  := minimal_N_then_mpt NSp C_is_bundle NSp_dec.

  Lemma pair_not_regular_NSp_r :
    pair_not_regular_h C_is_bundle K__P_AB (fun t => (~protected t) ) /\
    pair_not_regular_g C_is_bundle K__P_AB (fun t => (~protected t) ).
  Proof.
    unfold pair_not_regular_h, pair_not_regular_g.
    split;
    intros g h n n' Hproph Hin Hmin; autounfold in Hproph;
    specialize (NW_iff_inC_p (p_pair g h) C_is_bundle (p_pair_dec g h) n' n) as [HinNW _]; specialize (HinNW Hin);
    destruct HinNW as [HinC _];
    specialize (C_is_NSL _ HinC);
    inversion C_is_NSL as [Hpen|A0 B0 Na0 Nb0 s0 Hinires|A0 B0 Na0 Nb0 s0 Hinires]; try easy;
    inversion Hinires; unfold NWp_pair in *;
    apply (f_equal tr) in H0; simpl in H0;
    specialize (minimal_NWp_pair_then_mpt C_is_bundle g h n' H0 Hin Hmin) as Hmpti;
    unfold p_pair in Hmpti; simpl in Hmpti;
    simplify_prop in Hmpti;
    simplify_prop in Hproph.
  Qed.

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
      all: simplify_prop in Hmpti; try tauto.

      + (* Case M *)
        specialize (Nb_originates_in_n__20 Nb (t:=$Nb) m) as Horig2.
        st_implication Horig2.
        apply (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig2.
        all: try easy.

      + (* Case S (1) *)
        assert (protected h) as Hinh. {
          destruct (protected_dec h); tauto.
        }
        specialize (penetrator_pair_not_minimal_g (C:=C) (C_is_bundle:=C_is_bundle) NSp_dec Hpen Htrace) as Hpen_g.
        specialize (pair_not_regular_NSp_r) as [Hnotreh _].
        rewrite <-Hand2 in Hpen_g. rewrite <-(node_as_pair) in Hpen_g.
        now st_implication Hpen_g.

      + (* Case S (2) *)
        assert (protected g) as Hinh. {
          destruct (protected_dec g); tauto.
        }
        specialize (penetrator_pair_not_minimal_h (C:=C) (C_is_bundle:=C_is_bundle) NSp_dec Hpen Htrace) as Hpen_g.
        specialize (pair_not_regular_NSp_r) as [_ Hnotreh].
        rewrite <-Hand3 in Hpen_g. rewrite <-(node_as_pair) in Hpen_g.
        now st_implication Hpen_g.

      + (* Case E *)
        destruct h; auto; destruct h1; auto.
        unfold protected in *; tauto.

      + (* Case D *)
        specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,0) m) as Hinm0. st_implication Hinm0.
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle(inv_PK_U_never_originates_regular C_is_NSL (U:=A)) Hpen' Htrace Hinm0) as HcontraA.
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle (inv_PK_U_never_originates_regular C_is_NSL (U:=B)) Hpen' Htrace Hinm0) as HcontraB.
        unfold penetrator_key, K__P_AB in *.
        st_implication HcontraA.
        st_implication HcontraB.
        destruct h.
        1,2,3,4: intuition.
        unfold protected in *; destruct h1; intuition.

    - (* initiator *)
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti.
      inversion s_is_NSL_resp; apply (f_equal tr) in H3; simpl in H3.
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti; try tauto.
      specialize (mpti_then_originates $Nb m) as Horig.
      simplify_term_in Horig. st_implication Horig.
      apply (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig; try easy.
      rewrite (node_as_pair m) in Horig.
      inversion Horig as [Hstrand]. rewrite Hstrand in H0.
      rewrite <-H3 in H0. inversion H0.

    - (* responder *)
      inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti.
      inversion s_is_NSL_resp; apply (f_equal tr) in H3; simpl in H3.
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti; try tauto.
      simplify_prop in Hand using decidability.

      assert (originates $Nb m) as Horig. {
        apply (mpti_then_originates $Nb m).
        simplify_term. simplify_prop in |- *.
      }
      apply (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig.
      all: try easy.
      rewrite (node_as_pair m) in Horig.
      inversion Horig as [Hstrand]. rewrite Hstrand in H0. rewrite <-H0 in H3. inversion H3. subst. auto.
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
