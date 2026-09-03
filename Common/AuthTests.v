From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.

Require Import Strands.
Require Import Bundles.
Require Import MinimalMPT.
Require Import RelMinimal.

Import Stdlib.Lists.List.ListNotations.

Set Implicit Arguments.

Module AuthTests
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St)
  (Import B : BundleSig T St SSp).

  Module Import AT_MPT := MPT T St SSp B.

  Definition strand_minimal (p : A -> Prop) (n : node__t) : Prop :=
    p (uns_term n) /\
    forall n',
      strand n' = strand n ->
      index n' < index n ->
      ~ p (uns_term n').

  Definition auth_test_has_minimal
    (B : bundle_type) (B_is_bundle : is_bundle B) :=
    exists_minimal_bundle B_is_bundle.

  Lemma auth_test :
    forall B,
      is_bundle B ->
      forall p,
        (forall t, {p t} + {~ p t}) ->
        forall n,
          is_node_of n B ->
          p (uns_term n) ->
          is_negative n ->
          exists n',
            is_node_of n' B /\
            is_positive n' /\
            strand_minimal p n' /\
            mpt n' (length (tr (strand n'))) (tr (strand n')) p /\
            edges B ⊢ n' ≺ n.
  Proof.
    intros B B_is_bundle p p_dec n Hnode Hpn Hneg.
    pose proof
      (interstrand_exists_prec_positive_lt_uns B_is_bundle n Hnode Hneg)
      as [np [Hnode_np [Hpos_np [Hlt_np Huns]]]].
    pose proof
      (proj2 (NW_iff_inC_p p B_is_bundle p_dec n np))
      as Hchar.
    rewrite <- Huns in Hchar.
    assert (Hin_np :
      In np (NW p B_is_bundle p_dec n)).
    {
      apply Hchar.
      repeat split; assumption.
    }
    assert (Hnonempty : NW p B_is_bundle p_dec n <> []).
    {
      intros Hnil.
      rewrite Hnil in Hin_np.
      contradiction.
    }
    destruct (auth_test_has_minimal B_is_bundle Hnonempty)
      as [nm [Hin_nm Hmin_nm]].
    exists nm.
    pose proof
      (proj1 (NW_iff_inC_p p B_is_bundle p_dec n nm) Hin_nm)
      as [HinC [Hp_nm Hlt_nm]].
    repeat split; try assumption.
    - assert (Hsubset : node_subset_of (NW p B_is_bundle p_dec n) B).
      {
        intros m Hin.
        now apply (proj1 (NW_iff_inC_p p B_is_bundle p_dec n m)) in Hin
          as [HinB [_ _]].
      }
      apply
        (minimal_is_positive_weak Hsubset
          (NW_is_weak_sign_closed p B_is_bundle p_dec n)
          Hin_nm Hmin_nm).
    - intros n' Hstrand Hindex.
      specialize (Hmin_nm Hin_nm n').
      destruct (p_dec (uns_term n')) as [Hp_n' | Hnot]; [| exact Hnot].
      assert (Hnode_n' : is_node_of n' B).
      {
        eapply (index_lt_strand_implies_is_node_of B_is_bundle).
        - exact Hindex.
        - exact Hstrand.
        - exact HinC.
      }
      assert (Hlt_n'_nm : edges B ⊢ n' ≺ nm).
      {
        eapply (index_lt_strand_implies_bundle_lt B_is_bundle).
        - exact Hindex.
        - exact Hstrand.
        - exact HinC.
      }
      pose proof (bundle_lt_multi Hlt_n'_nm Hlt_nm) as Hlt_n'_n.
      pose proof
        (proj2 (NW_iff_inC_p p B_is_bundle p_dec n n')
          (conj Hnode_n' (conj Hp_n' Hlt_n'_n)))
        as Hin_n'.
      assert (Hneq : n' <> nm).
      {
        intros Heq.
        subst n'.
        simpl in Hindex.
        lia.
      }
      specialize (Hmin_nm Hin_n' Hneq).
      exfalso.
      apply Hmin_nm.
      eapply (index_le_strand_implies_bundle_le B_is_bundle).
      + lia.
      + exact Hstrand.
      + exact HinC.
    - exact (minimal_NW_then_mpt p B_is_bundle p_dec
        n eq_refl Hin_nm Hmin_nm).
  Qed.

End AuthTests.
