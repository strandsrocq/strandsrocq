From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import LogicalFacts.
From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Set Implicit Arguments.

From Stdlib Require Import Logic.Decidable.

Section SimpleAuthSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  ** This protocol adds [B] in the clear in the first message. This breaks the property that regular strands never originate pairs [g ⋅ h] such that [c ⊏ h] or [c ⊏ g] since, in fact, the initiator exactly generates such a pair. (c is ⟨ $Na ⋅ $A ⟩_(SK A B)). So we cannot use the techniques used in the original strand paper and we use our new protected predicate technique as explained in Section IV.E of the StrandsRocq paper.

  [[
  A -> B :  B ⋅⟨ Na ⋅ A ⟩_(SK A B)
  B -> A :  Na
  ]]
  *)

  (* ========================================================== *)
  (** * Protocol Specification   **)

  (* ========================================================== *)
  (**  ** Protocol Roles **)
  Inductive SA_initiator_strand (A B Na : T) : Σ -> Prop :=
  | SAS_Init : forall i,
    SA_initiator_strand A B Na (i, [ ⊕ $B ⋅ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊖ $Na ]).

  Inductive SA_responder_strand (A B Na : T) : Σ -> Prop :=
  | SAS_Resp : forall i,
    SA_responder_strand A B Na (i, [ ⊖ $B ⋅⟨ $Na ⋅ $A ⟩_(SK A B); ⊕ $Na ]).

  Definition K__P_AB (A B : T) (k : K) := k <> SK A B.

  Inductive SA_StrandSpace (K__P : K -> Prop) : Σ -> Prop :=
    | SASS_Pen  : forall s, penetrator_strand K__P s -> SA_StrandSpace K__P s
    | SASS_Init : forall (A B Na : T) s, SA_initiator_strand A B Na s -> SA_StrandSpace K__P s
    | SASS_Resp : forall (A B Na : T) s, SA_responder_strand A B Na s -> SA_StrandSpace K__P s.

  Lemma SK_AB_never_originates_regular :
    forall C K__P, strandspace_bundle C (SA_StrandSpace K__P) ->
      forall U U', never_originates_regular K__P (SK U U') C.
  Proof.
    intros C K__P [C_is_bundle His_SA] U U' n Hnodeof Horig.
    specialize (His_SA n Hnodeof).
    inversion His_SA as [s Hpen|A B Na s Hinires|A B Na s Hinires]; try easy;
    rewrite <-H in Hinires;
    destruct Hinires; apply strand_trace in H;
    inversion H as [Htrace];
    apply (originates_then_mpt Htrace) in Horig;
    unfold mpt in Horig; now simplify_prop in Horig.
  Qed.

  Lemma SK_AB_npen : forall A B, ~ penetrator_key (K__P_AB A B) (SK A B).
  Proof. now unfold penetrator_key, K__P_AB. Qed.
End SimpleAuthSpec.

Section SimpleAuthSecurity.
  Variable s : Σ.
  Variable C : bundle_type.

  Variable A B : T.
  Variable Na : T.

  Hypothesis s_is_SA_init : SA_initiator_strand A B Na s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_SA_bundle : strandspace_bundle C (SA_StrandSpace (K__P_AB A B)).

  (* Some facts, for easier use of C_is_SA_bundle *)
  Proposition C_is_bundle : is_bundle C.
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  Proposition C_is_SA :
    forall n, is_node_of n C -> SA_StrandSpace (K__P_AB A B) (strand n).
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  (** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective  *)

  (* ============================================================ *)
  (** ** Non-injective agreement: new proof technique  *)
  Fixpoint protected a :=
    match a with
    | $t => t <> Na
    | A_τ | #_ => True
    | ⟨g ⋅ h⟩_(k) =>
        (k = SK A B /\ g = $Na /\ h = $A) \/
        (protected g /\ protected h)
    | ⟨g⟩_(k) => protected g
    | g⋅h => protected g /\ protected h
    end.

  Definition Ncp := fun t => ~protected t.
  #[local] Hint Unfold Ncp : core.
  #[local] Hint Unfold uns term uns_term : core.

  Lemma protected_dec : forall t, { protected t } + { ~ protected t }.
  Proof.
    induction t; simpl; try tauto.
    - destruct (T_eq_dec t Na); subst; tauto.
    - destruct t; simpl; try tauto.
      + destruct (T_eq_dec t Na); subst; tauto.
      + simpl in IHt. destruct IHt; try tauto.
        destruct (K_eq_dec k (SK A B));
        destruct (A_eq_dec t1 $Na);
        destruct (A_eq_dec t2 $A); subst;
        try (right; tauto). left; tauto.
  Defined.

  Lemma dec_protected : forall t, decidable ( protected t ).
  Proof.
    red; intros t. destruct (protected_dec t). now left. now right.
  Qed.
  #[local] Hint Resolve dec_protected : Terms_decidability.

  Lemma Ncp_dec : forall t, { Ncp t } + { ~ Ncp t }.
  Proof.
    intros t. unfold Ncp. destruct (protected_dec t).
    right; auto. now left.
  Qed.

  Definition Nc := N Ncp C Ncp_dec. (* Set S of Lemma 4.4 *)
  Definition Nc_iff_inC_Ncp := N_iff_inC_p Ncp C Ncp_dec.
  Definition minimal_Nc_then_mpt := minimal_N_then_mpt Ncp C_is_bundle Ncp_dec.

  Lemma Nc_non_empty :
    Nc <> nil.
  Proof.
    unfold Nc.
    (* specialize (uns_term_of_c) as Hutc. *)
    assert (Ncp (uns_term (s, 1))) as Hc. {
      autounfold; simpl.
      specialize (s_is_SA_init) as Htrace. now destruct Htrace.
    }
    specialize (s_strand_of_C (s, 1)) as HinC;
    specialize (Nc_iff_inC_Ncp (s, 1)) as [_ Hin].
    specialize (in_nil (a:=(s,1))) as Hcontra.

    simpl in HinC.
    specialize (s_is_SA_init) as Htrace; destruct Htrace; simpl in HinC.
    st_implication HinC.
    intros Heq. rewrite Heq in Hin. tauto.
  Qed.

  Definition Nc_has_minimal :=
    exists_minimal_bundle C_is_bundle Nc_non_empty.

  Lemma Na_originates_only_in_s_0:
    uniquely_originates $Na ->
      forall n, originates $Na n -> strand n = s.
  Proof.
    intros Huniq n Horig.
    specialize (index_0_positive_originates (s,0) (t:=$Na)) as Horig'.
    autounfold in *. unfold is_positive, term in *; simpl in *.
    specialize (s_is_SA_init) as Htrace. destruct Htrace; simpl in *.
    st_implication Horig'.
    inversion Huniq as [n' [Horig'' Huniq']].
    assert (Huniq'':=Huniq').
    specialize (Huniq' _ Horig).
    specialize (Huniq'' _ Horig'). now subst.
  Qed.


  (** NOTE: We need the additional assumption that B <> Na since B is sent in the clear in the first message. So if B = Na, the nonce is leaked. *)
  Proposition noninjective_agreement :
    uniquely_originates $Na ->
    B <> Na ->
      exists s' : Σ,
        SA_responder_strand A B Na s' /\
        is_strand_of s' C.
  Proof.
    intros Huniq NaDiffPrincipals.
    specialize (exists_minimal_bundle C_is_bundle Nc_non_empty) as [m [Hin Hmin]].
    assert (Hin':=Hin).
    apply (Nc_iff_inC_Ncp) in Hin' as [HinC HNcp].
    specialize (C_is_bundle) as Hbundle.
    specialize (s_is_SA_init) as Hstrace.
    inversion Hstrace as [i Hstrace0].
    specialize (C_is_SA m HinC) as His_SA.
    inversion His_SA as [s' Hpen|A0 B0 N0__a s' Hini|A0 B0 N0__a s' Hres].

    (** _Penetrator case_ *)
    - assert (Hpen':=Hpen).
      inversion Hpen as [t j Htrace|g j Htrace|g j Htrace|g h j Htrace|g h j Htrace|k Hpenkey j Htrace| k h j Htrace|k h j Htrace].

      all: apply (f_equal tr) in Htrace; specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.

      pose (s0:=s).
      specialize (Na_originates_only_in_s_0 Huniq) as Horigs.
      all: simplify_prop in Hmpti; try tauto.

      + simplify_prop in Hand using decidability.
        specialize (index_0_positive_originates m (t:=$Na)) as Horig1.
        unfold is_positive in Horig1; st_implication Horig1.
        rewrite Horigs in Htrace.
        inversion Htrace. assumption.

      + simplify_prop in Hand using decidability. destruct h; try tauto.

      + destruct h; try tauto.
        push not in Hand using Terms_decidability.
        destruct Hand; try now unfold protected in *.
        specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m, 0) m) as Hnodeof;
        st_implication Hnodeof.

        specialize (SK_AB_never_originates_regular C_is_SA_bundle A B) as Hnever.
        specialize (SK_AB_npen (A:=A) (B:=B)) as HSK_AB_npen.
        rewrite (SK_symmetric) in HSK_AB_npen.
        rewrite (SK_symmetric) in Hnever.
        now specialize
          (penetrator_never_learn_secure_decryption_key
            C_is_bundle Hnever Hpen' Htrace Hnodeof HSK_AB_npen) as Hkey.

    (** _Initiator case_:  *)
    - inversion Hini as [j Htrace].
      apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.

      specialize (Na_originates_only_in_s_0 Huniq) as Horigs.
      pose (s0:=s).

      simplify_prop in Hmpti.
      push not in Hand using Terms_decidability.
      intuition idtac.
      push not in H using Terms_decidability.

      specialize (index_0_positive_originates m (t:=$Na)) as Horig1.
      unfold subterm, uns_term, term, is_positive in Horig1.
      simplify_term_in Horig1.
      st_implication Horig1.
      rewrite Horigs in Htrace.
      symmetry in Htrace.
      inversion Htrace; subst.
      tauto. assumption.

    (** _Responder case_: *)
    - pose (s0:=s).
      inversion Hres as [j Htrace].
      apply (f_equal tr) in Htrace.

      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti; try rewrite Hand2.

      exists (strand m); split.
      + simplify_prop in Hand using decidability;
      now rewrite Hand6 in *.
      + specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof;
      st_implication Hsof.
  Qed.

  (* ============================================================ *)
  (** ** Injective agreement   *)

  Proposition injectivity :
    uniquely_originates $Na ->
      forall s' : Σ,
        SA_initiator_strand A B Na s' ->
          s' = s.
  Proof.
    intros Huorig s' Hini'.
    inversion Hini' as [i' Htrace'].
    specialize s_is_SA_init as Hini.
    inversion Hini as [i Htrace].
    inversion Huorig as [n [_ Horigx]].
    assert (Horigx' := Horigx).
    specialize (mpti_then_originates $Na (s, 0)) as Horig.
    specialize (mpti_then_originates $Na (s', 0)) as Horig'.
    pose (s0:=s); pose (s0':=s').
    simplify_term_in Horig; simplify_term_in Horig'.

    st_implication Horig'. st_implication Horig. st_implication Horig'.
    simplify_term_in Horig; st_implication Horig.

    specialize (Horigx' (s0', 0) Horig').
    specialize (Horigx (s0, 0) Horig); subst.
    now inversion Horigx'.
  Qed.

  (** From [noninjective_agreement] and [injectivity] we obtain injective agreement as a corollary: *)
  Corollary injective_agreement :
   uniquely_originates $Na ->
    B <> Na ->
        uniquely_originates $Na ->
        (
          exists s' : Σ,
            SA_responder_strand A B Na s' /\
            is_strand_of s' C
        )
        /\
        (
          forall s'' : Σ,
            SA_initiator_strand A B Na s'' ->
            s'' = s
        ).
    Proof.
    intros Huniq. split.
    - now apply noninjective_agreement.
    - now apply injectivity.
  Qed.

End SimpleAuthSecurity.
