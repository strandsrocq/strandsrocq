From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

From Stdlib Require Import Logic.Decidable.
Require Import LogicalFacts.

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

    Let c := (⟨ ($Na ⋅ $Nb) ⋅ $B ⟩_ PK A).
    This new technique does not require the property that regular strands never
    originate pairs [g ⋅ h] such that [c ⊏ h] or [c ⊏ g] as done in the original
    strand paper. The techniques leverage the fact that Nb is secret before s2.
  *)

  Fixpoint protected a :=
    match a with
    | $t => t <> Nb
    | A_τ | #_ => True
    | ⟨(g ⋅ g') ⋅ h⟩_(k) =>
        (k = PK A /\ h = $B /\ g = $Na /\ g' = $Nb) \/ (protected g /\ protected g' /\ protected h)
    | ⟨g⟩_(k) => protected g
    | g⋅h => protected g /\ protected h
    end.

  Definition NSp := fun t => ~protected t.
  #[local] Hint Unfold NSp : core.
  #[local] Hint Unfold uns term uns_term : core.

  Lemma protected_dec : forall t, { protected t } + { ~ protected t }.
  Proof.
    intros t.
    induction t; simpl; try tauto.
    - destruct (T_eq_dec t Nb); subst; tauto.
    - destruct t; simpl; try tauto.
      + destruct (T_eq_dec t Nb); subst; tauto.
      + destruct t1; simpl; simpl in IHt; try tauto.
        destruct IHt; try tauto.
        destruct (K_eq_dec k (PK A));
        destruct (A_eq_dec t2 $B);
        destruct (A_eq_dec t1_1 $Na);
        destruct (A_eq_dec t1_2 $Nb); subst;
        try (right; tauto). left; tauto.
  Defined.

  Lemma dec_protected : forall t, decidable ( protected t ).
  Proof.
    red; intros t. destruct (protected_dec t). now left. now right.
  Qed.
  #[local] Hint Resolve dec_protected : Terms_decidability.

  Lemma NSp_dec : forall t, { NSp t } + { ~ NSp t }.
  Proof.
    intros t. unfold NSp. destruct (protected_dec t).
    right; auto. now left.
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
    specialize uns_term_of_c as Hc.
    specialize (C_is_bundle) as Hbundle.
    specialize (s_strand_of_C) as Hstrace.
    pose (C_is_NSL' := C_is_NSL).
    specialize (C_is_NSL' m HinC).
    inversion C_is_NSL' as [s0 Hpen|A0 B0 Na0 Nb0 s0 Hini|A0 B0 Na0 Nb0 s0 Hres].

    - (* Penetrator *)
      assert (Hpen':=Hpen).
      inversion Hpen as [t i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k Hpenkey i Htrace|k h i Htrace|k h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace.
      all: specialize (minimal_NS_then_mpt Htrace Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      all: simplify_prop in Hmpti; try tauto.

      + simplify_prop in Hand using decidability.
        specialize (index_0_positive_originates m (t:=$Nb)) as Horig1.
        unfold is_positive in Horig1; st_implication Horig1.
        specialize (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Nb:=Nb) (Tname:=Tname) s_is_NSL_resp diff_nonces Nb_uniquely_originates Horig1)  as Horigs.
        rewrite Horigs in Htrace; simpl in Htrace.
        inversion s_is_NSL_resp. apply (f_equal tr) in H0; simpl in H0.
        now rewrite <-Htrace in H0.

      + simplify_prop in Hand using decidability.
        destruct h; try tauto; destruct h1;
        unfold protected in *; try tauto.

      + destruct h; try tauto; destruct h1; try tauto.
        push not in Hand using Terms_decidability.
        simplify_prop in Hand using decidability;
        try (unfold protected in *; tauto).

        specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,0) m) as Hnodeof;
        st_implication Hnodeof.

        (** we eliminate this case by expoiting the fact that the penetrator can never learn a secure symmetric key *)

        specialize (inv_PK_U_never_originates_regular C_is_NSL (U:=A)) as Hnever.
        specialize
          (penetrator_never_learn_secure_decryption_key
            C_is_bundle Hnever Hpen' Htrace Hnodeof) as Hkey.
        st_implication Hkey.
    -
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      inversion s_is_NSL_resp. pose (s' := s).
      simplify_prop in Hmpti using decidability.

      + specialize (index_0_positive_originates m (t:=$Nb)) as Horig1.
        unfold is_positive in Horig1; st_implication Horig1.
        specialize (originates_Nb_implies_c (s:=s') (A:=A) (B:=B) (Na:=Na) (Nb:=Nb) (Tname:=Tname) s_is_NSL_resp diff_nonces Nb_uniquely_originates Horig1) as Horigs.
        st_implication Horigs; specialize (Horigs m Horig1).
      + exists (strand m). split; try tauto.
        specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof. rewrite <-H0 in Hsof.
        st_implication Hsof.

    - inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      inversion s_is_NSL_resp. pose (s' := s).
      simplify_prop in Hmpti.
      simplify_prop in Hand using decidability.
      intuition idtac.
      simplify_prop in H4 using decidability.

      specialize (mpti_then_originates ($ Nb) m) as Horig1.
      simplify_term_in Horig1. st_implication Horig1. intuition.
      specialize (originates_Nb_implies_c (s:=s') (A:=A) (B:=B) (Na:=Na) (Nb:=Nb) (Tname:=Tname) s_is_NSL_resp diff_nonces Nb_uniquely_originates) as Horigs.
      specialize (Horigs m Horig1).
      rewrite Horigs in H0; simpl in H0.
      inversion H0; subst; tauto.
  Qed.

  (* Proposition 4.8 -  injective agreement as in the original strand spaces paper **)
  Proposition injective_agreement_orig :
    $Na <> $Nb ->
    uniquely_originates $Nb ->
    uniquely_originates $Na ->
      exists !s : Σ,
        NSL_initiator_strand Tname A B Na Nb s /\
        is_strand_of s C.
  Proof.
    intros diff_nonces Nb_uniquely_originates Huorig.
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
    inversion Huorig as [? Huni].
    destruct Huni as [_ Horigx].
    assert (Horigx' := Horigx).
    specialize (Horigx' (s'',0) Horig'); specialize (Horigx (s0',0) Horig).
    subst. now inversion Horigx'.
  Qed.

  (* We now prove standard injective agreement with no extra assumptions
     with respect to non-injective agreement *)
  Proposition injectivity :
    $Na <> $Nb -> uniquely_originates $Nb ->
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
