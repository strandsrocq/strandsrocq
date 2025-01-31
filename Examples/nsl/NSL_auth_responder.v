Require Import Lia.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import NSL_protocol.
Require Import NSL_responder.
Require Import RelMinimal.

Set Implicit Arguments.

(* This section covers the responder's guarantee in the NSL protocol *)
Section auth_responder_guarantee.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : edge_set__t.

  Definition K__P_A (k : K) := k <> inv (PK A).

  Hypothesis s_is_NSL_resp : NSL_responder_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_NSL : C_is_SS C (NSL_StrandSpace Tname K__P_A).

  (*
    We define set NS in term of a characteristic NSp Prop. This set corresponds
    to set S of Lemma 4.4. We explit the MPT library that provides a
    characterization of minimal elements as a single Prop which can be easily
    destructed and analyzed.

    NSp is split in two components: (Nb ⊏ t) and (~ c ⊏ t). This is useful to
    apply a lemma over pairs g ⋅ h that permits to prove that the second and
    third nodes of the pentrator trace [⊖ g ⋅ h; ⊕ g; ⊕ h] cannot be minimal.
    This corresponds to the treatment of case S in lemma 4.4. In fact, the
    non-minimality lemma holds when g ⋅ h pairs in which (~ c ⊏ t) does not
    hold over g or h, i.e. (c ⊏ g) or (c ⊏ h), can never be generated on
    regular strands. (see lemma pair_not_regular_NSp_r below)
  *)

  Notation c := (⟨ ($Na ⋅ $Nb) ⋅ $B ⟩_ PK A).

  (* S characteristic Prop defined as left and right parts *)
  Definition NSp := fun t => ($Nb ⊏ t) /\ (~ c ⊏ t).
  #[local] Hint Unfold NSp : core.
  #[local] Hint Unfold uns term uns_term : core.

  (* decidability  *)
  Lemma NSp_dec : forall t, { NSp t } + { ~ NSp t }.
  Proof.
    intros t. unfold NSp.
    destruct (A_subterm_dec $Nb t) as [Hsub1|Hsub1];
    destruct (A_subterm_dec c t) as [Hsub2|Hsub2]; try now right.
    now left.
  Qed.

  (* The actual set *)
  Definition NS := N NSp C NSp_dec. (* Set S of Lemma 4.4 *)
  Definition NS_iff_inC_NSp := N_iff_inC_p NSp C NSp_dec.

  (* charaterization through the MPT library *)
  Definition minimal_NS_then_mpt  := minimal_N_then_mpt NSp C_is_bundle NSp_dec.

  (* first part of Lemma 4.4 - S has a minimal node *)
  Lemma NS_non_empty :
    NS <> nil.
  Proof.
    unfold NS.
    specialize (uns_term_of_c s_is_NSL_resp) as Hutc.
    assert (NSp (uns_term (s,2))) as Hc. {
      autounfold.
      inversion s_is_NSL_resp.
      now simplify_prop in |- *.
    }
    specialize (s_strand_of_C (s,2)) as HinC; simpl in HinC.
    inversion s_is_NSL_resp.
    specialize (NS_iff_inC_NSp (s,2)) as [_ Hin].
    specialize (in_nil (a:=(s,2))) as Hcontra.
    st_implication HinC.
    intros Heq. rewrite Heq in Hin. intuition.
  Qed.

  Definition NS_has_minimal := exists_minimal eq_node__t_dec (bundle_le_dec C) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (C:=C)) (NS_non_empty).

  (* lemma for the g ⋅ h case *)
  Lemma pair_not_regular_NSp_r :
    pair_not_regular_h C_is_bundle K__P_A (fun t => ~ c ⊏ t) /\
    pair_not_regular_g C_is_bundle K__P_A (fun t => ~ c ⊏ t).
  Proof.
    unfold pair_not_regular_h, pair_not_regular_g.
    split.
    all:  intros g h n n' Hproph Hin Hmin; autounfold in Hproph;
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

  (* Proposition 4.2 *)
  Proposition noninjective_agreement :
    $Na <> $Nb -> uniquely_originates $Nb ->
      exists s : Σ,
        NSL_initiator_strand Tname A B Na Nb s /\
        is_strand_of s C.
  Proof.
    intros diff_nonces Nb_uniquely_originates.
    specialize (NS_has_minimal) as [m [Hin Hmin]]; try easy.
    assert (Hin':=Hin).
    apply (NS_iff_inC_NSp) in Hin' as [HinC HNSp].
    pose (C_is_NSL' := C_is_NSL).
    specialize (C_is_NSL' m HinC).
    inversion C_is_NSL' as [s0 Hpen|A0 B0 Na0 Nb0 s0 Hini|A0 B0 Na0 Nb0 s0 Hres].

    - (* Penetrator *)
      assert (Hpen':=Hpen).
      inversion Hpen as [t i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k Hpenkey i Htrace|k h i Htrace|k h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace.
      all: specialize (minimal_NS_then_mpt Htrace Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      all: simplify_prop in Hmpti; try tauto.
      (* Cases F, T, C, K, E of lemma 4.4 are solved automatically *)

      + (* Case M of lemma 4.4 : [⊕ t] *)
        specialize (Nb_originates_in_n__20 Nb (t:=$Nb) m) as Horig2.
        now apply (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig2.

      + (* Case S of lemma 4.4: [⊖ g ⋅ h; ⊕ g; ⊕ h], and ⊕ g is the minimal element *)
        assert (c ⊏ h) as Hinh. { destruct (A_subterm_dec c h); try easy.
        st_implication Hand. }
        specialize (penetrator_pair_not_minimal_g (C:=C) (C_is_bundle:=C_is_bundle) NSp_dec Hpen Htrace) as Hpen_g.
        specialize pair_not_regular_NSp_r as [Hnotreh _].
        rewrite <-Hand2 in Hpen_g. rewrite <-(node_as_pair) in Hpen_g.
        now st_implication Hpen_g.

      + (* Case S of lemma 4.4: [⊖ g ⋅ h; ⊕ g; ⊕ h], and ⊕ h is the minimal element *)
        assert (c ⊏ g) as Hinh. { destruct (A_subterm_dec c g); try easy.
        st_implication Hand. }
        specialize (penetrator_pair_not_minimal_h (C:=C) (C_is_bundle:=C_is_bundle) NSp_dec Hpen Htrace) as Hpen_h.
        specialize (pair_not_regular_NSp_r) as [_ Hnotreh].
        rewrite <-Hand3 in Hpen_h. rewrite <-(node_as_pair) in Hpen_h.
        now st_implication Hpen_h.

      + (* Case D of lemma 4.4: [⊖ inv k; ⊖ ⟨ h ⟩_ k; ⊕ h] *)
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle (inv_PK_U_never_originates_regular C_is_NSL (U:=A)) Hpen' Htrace) as Hcontra.
        specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,0) m) as Hinm0. st_implication Hinm0.
        st_implication Hcontra; now subst.

    - (* initiator: this corresponds to lemmas 4.4, 4.6 and 4.7 together *)
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      inversion s_is_NSL_resp.
      pose (s' := s).
      simplify_prop in Hmpti.
      + (*  here the first initiator message has Nb in the first position.
            So Nb originates in that node which contradicts the Definition of
            being uniquely originating in c  *)
        assert ($Nb ⊏ uns_term m) as Hsub by simplify_term.
        assert (is_positive m) as Hpos by (unfold is_positive; simplify_term).
        specialize (index_0_positive_originates m Hsub Hpos Hand0) as Horig.
        apply (originates_Nb_implies_c (s:=s') (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig.
        all: try easy. now subst.
      + destruct (A_eq_dec c (⟨ ($Na ⋅ $Nb) ⋅ $B ⟩_ PK A)) as [Hok|Hfail].
        * (* the trace is the expected one we prove the thesis *)
          simplify_prop in Hok.
          destruct (T_eq_dec Na Na0);
          destruct (T_eq_dec B B0);
          destruct (T_eq_dec A A0); try tauto; subst.
          exists (strand m). split.
          -- rewrite surjective_pairing. unfold tr in H0. now rewrite<-H0.
          -- apply (last_node_implies_is_strand_of);
              try rewrite <-H0; repeat easy.
        * (* the other case is trivially impossible *)
          simplify_prop in Hfail.

    - (* responder *)
      inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      inversion s_is_NSL_resp.
      pose (s' := s).
      all: simplify_prop in Hmpti.
      (* push not in * using Terms_decidability. *)
      destruct (T_eq_dec Nb Na) as [Heq|Hneq]; try tauto.
      assert (originates $Nb m) as Horig. {
        apply (mpti_then_originates).
        simplify_term.
        simplify_prop in |- *.
      }
      apply (originates_Nb_implies_c (s:=s') (A:=A) (B:=B) (Na:=Na) (Tname:=Tname)) in Horig.
      (* rewrite <-H5 in H0.  *)
      apply (f_equal uns_term) in Horig.
      unfold uns_term, term in Horig.
      simplify_term_in Horig.
      simplify_prop in Horig. all: try tauto.
  Qed.

  (* Proposition 4.8 - injective agreement as in the original strand spaces paper **)
  Proposition injective_agreement_original :
    $Na <> $Nb -> 
      uniquely_originates $Nb ->
      uniquely_originates $Na ->
      exists !s : Σ,
        NSL_initiator_strand Tname A B Na Nb s /\
        is_strand_of s C.
  Proof.
    intros diff_nonces Nb_uniquely_originates Na_uniquely_originates.
    specialize (noninjective_agreement) as [s0 [Hinis Hstrand]]. all: try easy.
    exists s0. unfold unique. split; try easy.
    intros s' [Hinis' Hstrand'].
    pose (s0' := s0).
    pose (s'' := s').
    destruct Hinis.
    destruct Hinis'.
    specialize (index_0_positive_originates (s'',0) (t:=$Na)) as Horig'.
    specialize (index_0_positive_originates (s0',0) (t:=$Na)) as Horig.
    assert ($Na ⊏ uns_term (s'', 0) /\ $Na ⊏ uns_term (s0', 0) /\ is_positive (s'',0) /\ is_positive (s0',0) /\ index (s'',0) = 0 /\ index (s0',0) = 0). {
      unfold is_positive. repeat simplify_term. tauto.
    }
    st_implication Horig; st_implication Horig'.
    inversion Na_uniquely_originates as [? Huni].
    destruct Huni as [_ Horigx].
    assert (Horigx' := Horigx).
    specialize (Horigx' (s'',0) Horig'); specialize (Horigx (s0',0) Horig).
    subst. now inversion Horigx'.
  Qed.

  (* We now prove standard injective agreement with no extra assumptions
     with respect to non-injective agreement *)
  Proposition injectivity :
    $Na <> $Nb -> 
    uniquely_originates $Nb ->
      forall U U' s',
        NSL_responder_strand Tname U U' Na Nb s' ->
        s' = s.
  Proof.
    intros Hdiff Huorig U U' s' Hini'.
    specialize s_is_NSL_resp as Hini.
    inversion Huorig as [n [_ Horigx]].
    assert (Horigx' := Horigx).

    pose (s1 := s).
    pose (s1' := s').
    destruct Hini.
    destruct Hini'.
    assert (originates $Nb (s1, 1)) as Horig. {
      apply (mpti_then_originates $Nb (s1,1)).
      simplify_term. split. unfold not. intros.
      simplify_prop in H1; subst. split; auto 10.
    }
    assert (originates $Nb (s1', 1)) as Horig'. {
      apply (mpti_then_originates $Nb (s1',1)).
      simplify_term. split. unfold not. intros.
      simplify_prop in H1; subst. split; auto 10.
    }
    specialize (Horigx _ Horig); specialize (Horigx' _ Horig'); subst.
    now inversion Horigx'.
  Qed.
 
  Corollary injective_agreement :
    $Na <> $Nb -> uniquely_originates $Nb ->
    (
      exists s : Σ,
        NSL_initiator_strand Tname A B Na Nb s /\
        is_strand_of s C
    )
    /\
    (
      forall s',
        NSL_responder_strand Tname A B Na Nb s' ->
        s' = s
    ).
  Proof.
   intros Huniq. split.
   - now apply noninjective_agreement.
   - now apply injectivity.
  Qed.
 
End auth_responder_guarantee.
