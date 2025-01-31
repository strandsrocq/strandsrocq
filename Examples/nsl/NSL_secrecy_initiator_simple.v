(*
  Initiator secrecy with a more specific/instantiated set
*)
Require Import Lia.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import NSL_protocol.
Require Import NSL_initiator.
Require Import RelMinimal.
Require Import LogicalFacts.

Set Implicit Arguments.

(* This section covers the responder's guarantee in the NSL protocol *)
Section secrecy_initiator_guarantee.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : edge_set__t.

  Definition K__P_AB (k : K) := k <> inv (PK A) /\ k <> inv (PK B).

  Hypothesis s_is_NSL_init : NSL_initiator_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_NSL : C_is_SS C (NSL_StrandSpace Tname K__P_AB).

  Fixpoint protected a :=
    match a with
    | $t => t <> Na
    | A_τ | #_ => True
    | ⟨g⋅g'⋅h⟩_k =>
        (k = PK A /\ h = $B /\ g = $Na) \/ (* second protocol message *)
        (protected g /\ protected g' /\ protected h)
    | ⟨g⋅h⟩_k =>
        (k = PK B /\ h = $A /\ g = $Na) \/ (* first protocol message *)
        (protected g /\ protected h)
    | ⟨g⟩_k =>
        (k = PK B /\ g = $Na ) \/ (* third protocol message with N0__b = Na *)
        protected g
    (* The above is needed to cover the case in which the responder is
       using Na as a nonce which is not excluded by the hypotheses even
       if assuming Nb originates in the responder would automatically exclude
       it *)
    | g⋅h => protected g /\ protected h
    end.


  Lemma protected_prop_dec1 : forall (pk k : K) (h p g : 𝔸),
    {k = pk /\ h = p /\ g = $Na } + {~(k = pk /\ h = p /\ g = $Na) }.
  Proof.
    intros pk k h p g.
    destruct (K_eq_dec k pk); destruct (A_eq_dec h p); destruct (A_eq_dec g $Na). now left. all: now right.
  Qed.

  Lemma protected_prop_dec2 : forall (k : K) (t : 𝔸),
  {k = PK B /\ t = $Na } + {~(k = PK B /\ t = $Na) }.
  Proof.
    intros k t.
    destruct (K_eq_dec k (PK B)); destruct (A_eq_dec t $Na); intuition.
  Qed.

  Lemma protected_dec : forall a, {protected a} + {~protected a}.
  Proof.
    induction a; simpl; try tauto. destruct (T_eq_dec t Na); try tauto.
    destruct a as [|t|t|t k'|g h]; auto.
    - destruct (protected_prop_dec2 k τ); tauto.
    - destruct (protected_prop_dec2 k $t); tauto.
    - destruct (protected_prop_dec2 k #t); tauto.
    - destruct (protected_prop_dec2 k (⟨ k' ⟩_ t)); tauto.
    - destruct g as [|t1|t1|t1 k1|g1 h1];
      unfold protected in IHa.
      + destruct (protected_prop_dec1 (PK B) k h $A τ); tauto.
      + destruct (protected_prop_dec1 (PK B) k h $A $t1); tauto.
      + destruct (protected_prop_dec1 (PK B) k h $A #t1); tauto.
      + destruct (protected_prop_dec1 (PK B) k h $A (⟨ k1 ⟩_ t1)); tauto.
      + destruct (protected_prop_dec1 (PK A) k h $B g1); tauto.
  Qed.
  #[local] Hint Resolve protected_dec : core.

  Definition NSp := fun t =>
  (* (Na ⊏ t) /\ (~protected t). *)
  ~protected t.
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
  Definition minimal_NS_then_mpt  := minimal_N_then_mpt  NSp C_is_bundle NSp_dec.

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
    uniquely_originates $Na ->
      forall m, In m NS -> ~is_minimal (bundle_le C) m NS.
  Proof.
    intros Na_uniquely_originates m Hin Hmin.
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

      + specialize (Na_originates_in_n__20 Na (t:=$Na) m) as Horig2.
        st_implication Horig2.
        apply (originates_Na_implies_s0 (s:=s) (A:=A) (B:=B) (Nb:=Nb) (Tname:=Tname)) in Horig2; try easy.
        inversion Horig2. rewrite H0 in Htrace. now destruct s_is_NSL_init.

      + now apply (NSp_encrypt_protected1 k) in Hand.

      + specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,0) m) as Hinm0. st_implication Hinm0.
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle(inv_PK_U_never_originates_regular C_is_NSL (U:=A)) Hpen' Htrace Hinm0) as HcontraA.
        specialize (penetrator_never_learn_secure_decryption_key C_is_bundle (inv_PK_U_never_originates_regular C_is_NSL (U:=B)) Hpen' Htrace Hinm0) as HcontraB.
        unfold penetrator_key, K__P_AB in *.
        st_implication HcontraA.
        st_implication HcontraB.
        destruct h; try tauto.
        unfold protected in *; destruct h1; tauto.

    - (* initiator *)
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti.
      inversion s_is_NSL_init; apply (f_equal tr) in H3; simpl in H3.
      autounfold in Hmpti; simpl in Hmpti.
      (* push not in Hmpti using Terms_decidability. *)
      simplify_prop in Hmpti; try tauto.
      (* destruct (T_eq_dec A0 Na); subst; try easy.
      destruct (T_eq_dec Na0 Na); try tauto. *)
      specialize (mpti_then_originates $Na m) as Horig.
      simplify_term_in Horig. st_implication Horig.
      apply (originates_Na_implies_s0 (s:=s) (A:=A) (B:=B) (Nb:=Nb) (Tname:=Tname)) in Horig; try easy.
      rewrite (node_as_pair m) in Horig.
      inversion Horig as [Hstrand]. rewrite Hstrand in H0.
      rewrite <-H3 in H0. inversion H0. subst; auto.
      simplify_prop in Hand using decidability.
    - (* responder *)
      inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti.
      inversion s_is_NSL_init; apply (f_equal tr) in H3; simpl in H3.
      autounfold in Hmpti; simpl in Hmpti.
      (* push not in Hmpti using Terms_decidability. *)
      simplify_prop in Hmpti.
      push not in Hand2 using Terms_decidability.
      intuition idtac; push not in H7 using Terms_decidability.
      specialize (mpti_then_originates $Na m) as Horig.
      simplify_term_in Horig.
      (* push not in Hand0 using Terms_decidability. *)
      st_implication Horig.
      apply (originates_Na_implies_s0 (s:=s) (A:=A) (B:=B) (Nb:=Nb) (Tname:=Tname)) in Horig.
      rewrite (node_as_pair m) in Horig.
      inversion Horig as [Hstrand]. rewrite Hstrand in H0.
      rewrite <-H0 in H3. inversion H3. all: auto.
  Qed.

  Proposition initiator_secrecy:
    uniquely_originates $Na ->
    forall m, is_node_of m C ->
      $Na ⊏ uns_term m ->
        protected (uns_term m).
  Proof.
    intros Na_uniquely_originates m Hin Hmin.
    destruct (protected_dec (uns_term m)); auto.
    assert (In m NS). { apply (N_iff_inC_p). auto. }
    specialize (NS_no_minimal) as Hnomin.
    assert ({NS = nil} + {NS <> nil}) as NS_empty_dec by (repeat decide equality).
    destruct NS_empty_dec as [Hemp | Hnemp].
    - (* empty *) now rewrite Hemp in H.
    - (* nonempty *)
      specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec C) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (C:=C)) Hnemp) as [m' [Hin' Hmin']].
      now specialize (Hnomin Na_uniquely_originates m' Hin').
  Qed.

  Corollary secrecy_of_Na_neq:
    uniquely_originates $Na ->
      forall m,
        is_node_of m C ->
            $Na ⊏ uns_term m ->
              $Na <> uns_term m.
  Proof.
    intros Na_uniquely_originates m Hin Hmin HNa_eq_m.
    specialize (initiator_secrecy Na_uniquely_originates m Hin Hmin) as Hsub.
    all: rewrite <- HNa_eq_m in Hsub.
    all: now simpl in Hsub.
  Qed.

End secrecy_initiator_guarantee.
