Require Import Lia.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Coq.Arith.PeanoNat.
Import Nat.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import NSL_protocol.
Require Import NSL_initiator.
Require Import RelMinimal.
Require Import NSL_secrecy_initiator_simple.

Set Implicit Arguments.

(* This section covers the responder's guarantee in the NSL protocol *)
Section auth_initiator_guarantee.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : edge_set__t.

  Definition K__P_AB (k : K) := k <> inv (PK A) /\ k <> inv (PK B).

  Hypothesis s_is_NSL_init : NSL_initiator_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_NSL : C_is_SS C (NSL_StrandSpace Tname K__P_AB).

  (*
    We define set NS in term of a characteristic NSp Prop. This set corresponds
    to set S of Lemma 4.4. We exploit the MPT library that provides a
    characterization of minimal elements as a single Prop which can be easily
    destructed and analyzed.

    This authentication proof is based on the secrecy of nonces as in the paper so the technique is different wrt the responder authentication.
  *)

  Notation c := (⟨ ($Na ⋅ $Nb) ⋅ $B ⟩_ PK A).
  Definition NSp := fun t => c ⊏ t.
  #[local] Hint Unfold NSp : core.
  #[local] Hint Unfold uns term uns_term : core.

  (* decidability  *)
  Lemma NSp_dec : forall t, { NSp t } + { ~ NSp t }.
  Proof.
    intros t. unfold NSp.
    destruct (A_subterm_dec c t) as [Hsub2|Hsub2]; try now right.
    now left.
  Qed.

  (* The actual set *)
  Definition NS := N NSp C NSp_dec. (* Set S of Lemma 4.4 *)
  Definition NS_iff_inC_NSp := N_iff_inC_p NSp C NSp_dec.

  (* characterization through the MPT library *)
  Definition minimal_NS_then_mpt  := minimal_N_then_mpt  NSp C_is_bundle NSp_dec.

  (* first part of Lemma 4.4 - S has a minimal node *)
  Lemma NS_non_empty :
    NS <> nil.
  Proof.
    unfold NS.
    specialize (uns_term_of_c s_is_NSL_init) as Hutc.
    assert (NSp (uns_term (s,1))) as Hc. {
      autounfold.
      inversion s_is_NSL_init.
      now simplify_prop in |- *.
    }
    specialize (s_strand_of_C (s,1)) as HinC; simpl in HinC.
    inversion s_is_NSL_init.
    specialize (NS_iff_inC_NSp (s,1)) as [_ Hin].
    specialize (in_nil (a:=(s,1))) as Hcontra.
    st_implication HinC.
    intros Heq. rewrite Heq in Hin. intuition.
  Qed.

  Definition NS_has_minimal := exists_minimal eq_node__t_dec (bundle_le_dec C) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (C:=C)) (NS_non_empty).

  (* Proposition 4.2 *)
  Proposition noninjective_agreement :
    uniquely_originates $Na ->
      exists s : Σ,
        NSL_responder_strand Tname A B Na Nb s /\
        forall i, i < 2 -> is_node_of (s,i) C.
  Proof.
    intros Na_uniquely_originates.
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
      all: simplify_prop in Hmpti using decidability.
      (* We use the nonce secrecy as in the paper *)
      specialize (initiator_secrecy s_is_NSL_init s_strand_of_C C_is_bundle C_is_NSL Na_uniquely_originates (strand m, 1)) as Hsecrecy.
      specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,1) m) as Hnodeof.
      st_implication Hnodeof.
      simplify_term_in Hsecrecy.
      now st_implication Hsecrecy.

    - (* initiator *)
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      all: simplify_prop in Hmpti.

    - (* responder *)
      inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti.
      exists (strand m). split; auto.
      intros i0 Hlt.
      specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,i0) m) as Hisnode. simpl in Hisnode. rewrite Hand0 in Hisnode.
      destruct (eq_dec i0 1).
      + subst. rewrite <-Hand0. now rewrite <-node_as_pair.
      + now st_implication Hisnode.
  Qed.

  (* injective agreement as done in the original strand spaces paper for the responder **)
  Proposition injective_agreement_orig :
    $Na <> $Nb -> 
    uniquely_originates $Na ->
    uniquely_originates $Nb ->
      exists !s : Σ,
        NSL_responder_strand Tname A B Na Nb s /\
        forall i, i < 2 -> is_node_of (s,i) C.
  Proof.
    intros diff_nonces Na_uniquely_originates Nb_uniquely_originates.
    specialize (noninjective_agreement) as [s0 [Hinis Hstrand]]. all: try easy.
    exists s0. unfold unique. split; try easy.
    intros s' [Hinis' Hstrand'].
    pose (s0' := s0).
    pose (s'' := s').
    destruct Hinis.
    destruct Hinis'.
    specialize (diff_nonces) as Hdiff.
    assert (originates $Nb (s0', 1)) as Horig. {
      apply (mpti_then_originates $Nb (s0',1)).
      simplify_term. split. unfold not. intros.
      simplify_prop in H1; subst; now rewrite Hor in *. split; auto 10.
    }
    assert (originates $Nb (s'', 1)) as Horig'. {
      apply (mpti_then_originates $Nb (s'',1)).
      simplify_term. split. unfold not. intros.
      simplify_prop in H1; subst; now rewrite Hor in *. split; auto 10.
    }
    inversion Nb_uniquely_originates as [? Huni].
    destruct Huni as [_ Horigx].
    assert (Horigx' := Horigx).
    specialize (Horigx' (s'',1) Horig'); specialize (Horigx (s0',1) Horig).
    subst; now inversion Horigx'.
  Qed.

  (* We now prove standard injective agreement with no extra assumptions
     with respect to non-injective agreement *)
  Proposition injectivity :
      uniquely_originates $Na ->
        forall U U' Nb' s',
          NSL_initiator_strand Tname U U' Na Nb' s' ->
          s' = s.
  Proof.
    intros Huorig U U' Nb' s' Hini'.
    inversion Hini' as [i' Htrace'].
    specialize s_is_NSL_init as Hini.
    inversion Hini as [i Htrace].
    inversion Huorig as [n [_ Horigx]].
    assert (Horigx' := Horigx).

    specialize (Horigx (s, 0)); specialize (Horigx' (s', 0)).
    specialize (mpti_then_originates $Na (s, 0)) as Horig.
    specialize (mpti_then_originates $Na (s', 0)) as Horig'.
    simplify_term_in Horig; st_implication Horig.
    simplify_term_in Horig'; st_implication Horig'.
    specialize (Horigx Horig); specialize (Horigx' Horig'); subst.
    now inversion Horigx'.
  Qed.

  Corollary injective_agreement :
      uniquely_originates $Na ->
      (
        exists s : Σ,
          NSL_responder_strand Tname A B Na Nb s /\
          forall i, i < 2 -> is_node_of (s,i) C
      )
      /\
      (
        forall s',
          NSL_initiator_strand Tname A B Na Nb s' ->
          s' = s
      ).
  Proof.
    intros Huniq. split.
    - now apply noninjective_agreement.
    - now apply injectivity.
  Qed.

End auth_initiator_guarantee.
