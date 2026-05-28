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

Require Import RelMinimal.

Require Import DefaultInstances.
Set Implicit Arguments.

Section PenetratorStrands.
  Variable K__P : K -> Prop.
  (** Penetrators (i.e., attackers) *)
  Inductive penetrator_strand : Σ -> Prop :=
    | PT_M : forall (t : T) i, penetrator_strand (i, [⊕ $t])
    | PT_F : forall (g : 𝔸) i, penetrator_strand (i, [⊖ g])
    | PT_T : forall (g : 𝔸) i, penetrator_strand (i, [⊖ g; ⊕ g; ⊕ g])
    | PT_C : forall (g h : 𝔸) i, penetrator_strand (i, [⊖ g; ⊖ h; ⊕ g⋅h])
    | PT_S : forall (g h : 𝔸) i, penetrator_strand (i, [⊖ g⋅h; ⊕ g; ⊕ h])
    | PT_K : forall (k : K) i, K__P k -> penetrator_strand (i,[⊕ #k])
    | PT_E : forall (k : K) (h : 𝔸) i, penetrator_strand (i, [⊖ #k; ⊖ h; ⊕ ⟨h⟩_k])
    | PT_D : forall (k : K) (h : 𝔸) i, penetrator_strand (i, [⊖ #k⁻¹; ⊖ ⟨h⟩_k; ⊕ h]).

  Lemma strand_trace : forall i t s, (i,t) = s -> t = tr s.
  Proof.
    intros. now rewrite <- H.
  Qed.
  (* Now definitions to define penetrator objects *)
  Definition penetrator_node (n : node__t) := penetrator_strand (strand n).
  Definition penetrator_key (k : K) := K__P k.

  Definition never_originates_regular k E :=
    forall n, is_node_of n E -> originates #k n -> penetrator_node n.
  Definition originates_regular k E :=
    exists n, is_node_of n E /\ originates #k n /\ ~ penetrator_node n.

End PenetratorStrands.

Section PenetratorBound.
  Variable B : bundle_graph.
  Hypothesis B_is_bundle : is_bundle B.
  Local Notation E := (edges B).

  Proposition penetrator_bound_set :
    forall (K__P : K -> Prop) (k__R : K),
      ~ penetrator_key K__P k__R ->
      never_originates_regular K__P k__R B ->
      Nsubt B #k__R = nil.
  Proof.
    intros K__P k__R Hnpen Hknreg.
    destruct (Nsubt B #k__R) eqn:HN; try easy.
    (* by Lemma 2.6 the bundle has a minimal element m *)
    assert ((Nsubt B #k__R) <> []) as HNsubt_non_empty by (now rewrite HN).
    specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec E) (bundle_le_antisymm B_is_bundle) (bundle_le_trans (E:=E)) HNsubt_non_empty) as [m [Hin0 Horig]].
    (* Lemma 2.8 guarantees that k__R in K originates in m *)
    apply (minimal_then_originates B_is_bundle _ Hin0) in Horig.
    apply (Nsubtiff_inC_p) in Hin0 as [HinC Hp].
    (* as a consequence, m is always a penetrator node by assumption Hnkreg *)
    specialize (Hknreg _ HinC Horig) as Hm_is_penetrator.
    (* apply is_penetrator in Hm_is_penetrator. *)
    (* We now go by cases on the penetrator traces and show that nodes_with_term is always empty *)
    inversion Hm_is_penetrator as [t i H|g i H|g i H|g h i H|g h i H|k Hpenkey i H|k h|k h]; apply strand_trace in H.
    all: specialize (originates_then_mpt H Horig) as Hcontra; simpl in Hcontra.
    all: simplify_prop in Hcontra; try tauto.
  Qed.

  Proposition penetrator_bound :
    forall K__P k__R,
      ~ penetrator_key K__P k__R ->
      never_originates_regular K__P k__R B ->
        (forall p, is_node_of p B -> penetrator_node K__P p ->
              ~ (#k__R ⊏ (uns_term p))
        ).
  Proof.
      intros K__P k__R Hisreg Hnorig p Hisnode Hpennode HcontraS.
      specialize (penetrator_bound_set (K__P:=K__P) Hisreg Hnorig) as Hset.
      specialize (Nsubtiff_inC_p B #k__R p) as [_ Hr].
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
      [⊖ #k⁻¹; ⊖ ⟨h⟩_k; ⊕ h] = tr s ->
      is_node_of (s,0) B ->
      ~ penetrator_key K__P k'⁻¹ ->
      k <> k'.
  Proof.
    intros K__P s h k k' Hneverorig Hpen Htrace HinC Hnopenkey.
    specialize (penetrator_bound (K__P:=K__P) Hnopenkey Hneverorig HinC) as Hbound.
    st_implication Hbound; simplify_term_in Hbound.
    unfold not. intros. now subst.
  Qed.

  Corollary penetrator_never_learn_secure_encryption_key :
    forall K__P s h k k',
      never_originates_regular K__P k' B ->
      penetrator_strand K__P s ->
      [⊖ #k; ⊖ h; ⊕ ⟨h⟩_k] = tr s ->
      is_node_of (s,0) B ->
      ~ penetrator_key K__P k' ->
      k <> k'.
  Proof.
    intros K__P s h k k' Hneverorig Hpen Htrace HinC Hnopenkey.
    specialize (penetrator_bound (K__P:=K__P) Hnopenkey Hneverorig HinC) as Hbound.
    st_implication Hbound; simplify_term_in Hbound.
    unfold not; intros; now subst.
  Qed.

End PenetratorBound.

Section PenBoundPairs.
  Variable B : bundle_graph.
  Hypothesis B_is_bundle : is_bundle B.
  Local Notation E := (edges B).

  Variable K__P : K->Prop.

  Variable p1 : 𝔸 -> Prop.
  Variable p2 : 𝔸 -> Prop.

  Definition p1_and_p2 := fun t => p1 t /\ p2 t.
  Hypothesis p1_and_p2_dec : forall t, { p1_and_p2 t } + { ~ p1_and_p2 t }.

  Definition Np1_and_p2 := N p1_and_p2 B p1_and_p2_dec.
  Definition Np1_and_p2_iff_inC_p1_and_p2 := N_iff_inC_p p1_and_p2 B p1_and_p2_dec.

  Definition p_pair g h t := (g ⋅ h) ⊏ t.
  #[local] Hint Unfold p_pair : core.

  Lemma p_pair_dec : forall g h t, { p_pair g h t } + { ~ p_pair g h t }.
  Proof.
    intros. unfold p_pair. destruct (A_subterm_dec (g ⋅ h) t0); eauto.
  Qed.
  Definition NWp_pair g h := NW (p_pair g h) B_is_bundle (p_pair_dec g h).
  Definition NWp_pair_dec g h := NW (p_pair g h) B_is_bundle (p_pair_dec g h).
  Definition NWp_pair_iff_inC_NWp_pair g h := NW_iff_inC_p (p_pair g h) B_is_bundle (p_pair_dec g h).

  Lemma NWp_pair_is_weak_sign_closed :
    forall g h n, sign_closed_weak B (NWp_pair g h n).
  Proof.
    intros g h n. unfold sign_closed_weak. intros Hsub m Hin Hneg.
    specialize (Hsub _ Hin).
    specialize (interstrand_exists_prec_positive_lt_uns B_is_bundle m) as Hexists.
    st_implication Hexists.
    destruct Hexists as [m' [Hnode [Hpos [Hect Huns]]]].
    exists m'.
    unfold set_In in Hin. rewrite (NWp_pair_iff_inC_NWp_pair g h n) in Hin.
    repeat split; try easy.
    unfold set_In.
    rewrite (NWp_pair_iff_inC_NWp_pair g h n).
    repeat split; try easy.
    - unfold p_pair, uns_term in *. now rewrite <-Huns.
    - now apply (bundle_lt_multi Hect).
  Qed.

  Definition minimal_NWp_pair_then_mpt g h n := minimal_NW_then_mpt (p_pair g h) B_is_bundle (p_pair_dec g h) n.

  Definition pair_not_regular_g p :=
    forall g h n n',
    ~p g ->
    set_In n (NWp_pair g h n') ->
    is_minimal (bundle_le E) n (NWp_pair g h n') ->
    penetrator_node K__P n.

  Definition pair_not_regular_h p :=
    forall g h n n',
    ~p h ->
    set_In n (NWp_pair g h n') ->
    is_minimal (bundle_le E) n (NWp_pair g h n') ->
    penetrator_node K__P n.

  Lemma penetrator_pair_not_minimal_g :
    forall g h s, penetrator_strand K__P s ->
    [⊖ g ⋅ h; ⊕ g; ⊕ h] = tr s ->
    is_node_of (s,1) B ->
    p1 g /\ p2 g /\ ~p2 h ->
    pair_not_regular_h p2 ->
    ~is_minimal (bundle_le E) (s,1) Np1_and_p2.
  Proof.
    intros g h s Hpen Htrace Hin Hc1 Hnotregular.
    specialize (B_is_bundle) as Hbundle.
    assert ( set_In (s, 1) Np1_and_p2 ) as Hs1in. {
      rewrite Np1_and_p2_iff_inC_p1_and_p2.
      unfold p1_and_p2. simplify_term.
    }

    assert ( In (s, 0) (NWp_pair g h (s,1))) as HinNWsub. {
      apply (NWp_pair_iff_inC_NWp_pair). repeat split.
      - apply (index_lt_strand_implies_is_node_of B_is_bundle (s,0) (s,1)); simpl; try lia; repeat easy.
      - unfold p_pair. simplify_term.
      - apply (index_lt_strand_implies_bundle_lt); simpl; try lia; repeat easy.
      }
    assert ((NWp_pair g h (s,1)) <> []) as NW_non_empty by (destruct (NWp_pair g h (s,1)); try easy).

    specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec E) (bundle_le_antisymm B_is_bundle) (bundle_le_trans (E:=E)) NW_non_empty) as [m0 [Hin0 Hmin0]].
    specialize (Hnotregular g h m0 (s,1)) as HP.
    st_implication HP.
    unfold penetrator_node in HP.
    assert (Hpentrace0:=HP).
    inversion Hpentrace0 as [t i Htrace0|g0 i Htrace0|g0 i Htrace0|g0 h0 i Htrace0|g0 h0 i Htrace0|k Hpenkey i Htrace0|k h0 i Htrace0|k h0 i Htrace0]; apply strand_trace in Htrace0.
    all: specialize (minimal_NWp_pair_then_mpt g h (s,1) Htrace0 Hin0 Hmin0) as Hmpti; unfold p_pair in Hmpti; simpl in Hmpti.
    all: simplify_prop in Hmpti.
    intro Hcontra.
    assert (Hin0':=Hin0).
    apply (NWp_pair_iff_inC_NWp_pair) in Hin0' as [Hin1 [_ Hect]].
    specialize (index_lt_strand_implies_bundle_lt B_is_bundle ((strand m0),0) m0) as Hect1. simpl in Hect1. st_implication Hect1.
    specialize (bundle_lt_multi Hect1 Hect) as Hect2.
    assert (set_In ((strand m0),0) (Np1_and_p2)) as Hinm00. {
      unfold set_In. apply (Np1_and_p2_iff_inC_p1_and_p2).
      split.
      - apply (index_lt_strand_implies_is_node_of B_is_bundle (strand m0, 0) m0); simpl; try lia; easy.
      - unfold p1_and_p2. subst. simplify_term.
      }
    assert (((strand m0),0) <> (s,1)) as H00neq by easy.
    unfold is_minimal in Hcontra.
    st_implication Hcontra.
    specialize (Hcontra _ Hinm00). st_implication Hcontra.
    now apply (bundle_lt_then_le) in Hect2.
  Qed.

  Lemma penetrator_pair_not_minimal_h :
    forall g h s, penetrator_strand K__P s ->
    [⊖ g ⋅ h; ⊕ g; ⊕ h] = tr s ->
    is_node_of (s,2) B ->
    p1 h /\ p2 h /\ ~p2 g ->
    pair_not_regular_g p2 ->
    ~is_minimal (bundle_le E) (s,2) Np1_and_p2.
  Proof.
    intros g h s Hpen Htrace Hin Hc1 Hnotregular.
    specialize (B_is_bundle) as Hbundle.
    assert ( set_In (s, 2) Np1_and_p2 ) as Hs1in. {
      rewrite Np1_and_p2_iff_inC_p1_and_p2.
      unfold p1_and_p2. simplify_term.
    }
    assert ( In (s, 0) (NWp_pair g h (s,2))) as HinNWsub. {
          apply (NWp_pair_iff_inC_NWp_pair). repeat split.
          - apply (index_lt_strand_implies_is_node_of B_is_bundle _ (s,2)); simpl; try lia; repeat easy.
          - unfold NWp_pair, p_pair; simplify_term.
          - apply (index_lt_strand_implies_bundle_lt); simpl; try lia; repeat easy.
        }
    assert ((NWp_pair g h (s,2)) <> []) as NW_non_empty by (destruct (NWp_pair g h (s,2)); try easy).

    specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec E) (bundle_le_antisymm B_is_bundle) (bundle_le_trans (E:=E)) NW_non_empty) as [m0 [Hin0 Hmin0]].
    specialize (Hnotregular g h m0 (s,2)) as HP.
    st_implication HP;
    unfold penetrator_node in HP.
    inversion HP as [t i Htrace0|g0 i Htrace0|g0 i Htrace0|g0 h0 i Htrace0|g0 h0 i Htrace0|k Hpenkey i Htrace0|k h0 i Htrace0|k h0 i Htrace0]; apply strand_trace in Htrace0.
    all: specialize (minimal_NWp_pair_then_mpt g h (s,2) Htrace0 Hin0 Hmin0) as Hmpti; unfold p_pair in Hmpti; simpl in Hmpti.
    all: simplify_prop in Hmpti.
    intro Hcontra.
    assert (Hin0':=Hin0).
    apply (NWp_pair_iff_inC_NWp_pair) in Hin0' as [Hin1 [_ Hect]].
    specialize (index_lt_strand_implies_bundle_lt B_is_bundle ((strand m0), 1) m0) as Hect1. simpl in Hect1. st_implication Hect1.
    specialize (bundle_lt_multi Hect1 Hect) as Hect2.
    assert (set_In ((strand m0),1) (Np1_and_p2)) as Hinm00. {
      unfold set_In. apply (Np1_and_p2_iff_inC_p1_and_p2).
      split.
      - apply (index_lt_strand_implies_is_node_of B_is_bundle (strand m0, 1) m0); simpl; try lia; easy.
      - unfold p1_and_p2. subst. simplify_term.
    }
    assert (((strand m0),1) <> (s,2)) as H00neq by easy.
    unfold is_minimal in Hcontra.
    st_implication Hcontra.
    specialize (Hcontra _ Hinm00).
    st_implication Hcontra.
    now apply (bundle_lt_then_le) in Hect2.
  Qed.

End PenBoundPairs.
