From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Set Implicit Arguments.

Section SimpleAuthSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  ** NOTE: This is a variant of [SimpleAuth.v] where [Na] is a general term in [𝔸].
  [[
  A -> B :  A ⋅ B ⋅ Na
  B -> A :  ⟨ Na ⋅ A ⟩_(SK A B)
  ]]
  *)

  (*
    Since we have [Na : 𝔸] we need to be sure that
      - [Na] does not leak [SK U U'], i.e., [forall U U',  ~ #(SK U U') ⊏ Na]
      - [Na] does not forge a valid ciphertext, i.e.
        [forall N U U', ~ (⟨ N ⋅ U ⟩_(SKA U U')) ⊏ Na]
  *)
  Inductive SA_initiator_strand (A B : T) (Na : 𝔸) : Σ -> Prop :=
    | SAS_Init : forall i,
      (forall U U', ~ #(SK U U') ⊏ Na) ->
      (forall N U U', ~ (⟨ N ⋅ $U ⟩_(SK U U')) ⊏ Na) ->
      SA_initiator_strand A B Na (i, [ ⊕ $A ⋅ $B ⋅ Na; ⊖ ⟨ Na ⋅ $A ⟩_(SK A B) ]).

  Inductive SA_responder_strand (A B : T) (Na : 𝔸) : Σ -> Prop :=
    | SAS_Resp : forall i,
      (forall U U', ~ #(SK U U') ⊏ Na) ->
      (forall N U U', ~ (⟨ N ⋅ $U ⟩_(SK U U')) ⊏ Na) ->
      SA_responder_strand A B Na (i, [ ⊖ $A ⋅ $B ⋅ Na; ⊕ ⟨ Na ⋅ $A ⟩_(SK A B) ]).

  Definition K__P_AB (A B : T) (k : K) := k <> SK A B.

  Inductive SA_StrandSpace (K__P : K -> Prop) : Σ -> Prop :=
    | SASS_Pen  : forall s, penetrator_strand K__P s -> SA_StrandSpace K__P s
    | SASS_Init : forall (A B : T) (Na : 𝔸) s,
        SA_initiator_strand A B Na s -> SA_StrandSpace K__P s
    | SASS_Resp : forall (A B : T) (Na : 𝔸) s,
        SA_responder_strand A B Na s -> SA_StrandSpace K__P s.

  (* ============================================================ *)
  (**
      We prove that no symmetric key [SK U U'], for any [U] and [U'], ever originates on regular strands, i.e., neither the initiator nor the responder send symmetric keys as protocol messages.
  *)
  Lemma SK_AB_never_originates_regular :
    forall C K__P, strandspace_bundle C (SA_StrandSpace K__P) ->
      forall U U', never_originates_regular K__P (SK U U') C.
  Proof.
    intros C K__P [C_is_bundle His_SA] U U' n Hnodeof Horig.
    specialize (His_SA n Hnodeof).
    inversion His_SA as [s Hpen|A B Na s HH H|A B Na s HH H]; try easy;
    inversion HH as [i Hsub Hcipher Hinires];
    rewrite <-H in Hinires;
    destruct Hinires; apply strand_trace in H;
    inversion H as [Htrace];
    apply (originates_then_mpt Htrace) in Horig;
    unfold mpt in Horig; simplify_prop in Horig; now specialize (Hsub U U').
  Qed.

  (**
    Given the definition of [K__P_AB], we can also prove that the attacker has no knowledge of the session key.
  *)
  Lemma SK_AB_npen : forall A B, ~ penetrator_key (K__P_AB A B) (SK A B).
  Proof. now unfold penetrator_key, K__P_AB. Qed.
End SimpleAuthSpec.

Section SimpleAuthSecurity.
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : bundle_type.

  Variable A B : T.
  Variable Na : 𝔸.

  Hypothesis s_is_SA_init : SA_initiator_strand A B Na s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_SA_bundle : strandspace_bundle C (SA_StrandSpace (K__P_AB A B)).

  (* Some facts, for easier use of C_is_SA_bundle *)
  Proposition C_is_bundle : is_bundle C.
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  Proposition C_is_SA :
    forall n, is_node_of n C -> SA_StrandSpace (K__P_AB A B) (strand n).
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  (** * Proof of Security *)

  Definition Ncp (t : 𝔸) := (⟨ Na ⋅ $A ⟩_(SK A B)) ⊏ t.
  #[local] Hint Unfold Ncp uns term uns_term : core.

  Lemma Ncp_dec : forall t, { Ncp t } + { ~ Ncp t }.
  Proof.
    intros t;
    destruct (A_subterm_dec (⟨ Na ⋅ $A ⟩_(SK A B)) t);
    (try now right); (try now left).
  Qed.

  Definition Nc := N Ncp C Ncp_dec.
  Definition Nc_iff_inC_Ncp := N_iff_inC_p Ncp C Ncp_dec.
  Definition minimal_Nc_then_mpt := minimal_N_then_mpt Ncp C_is_bundle Ncp_dec.

  (** We now prove that [Nc] is not empty. This trivially comes from the fact that the term of second node of the initiator strand is indeed equal to [c] *)
  Lemma Nc_non_empty :
    Nc <> nil.
  Proof.
    unfold Nc.
    specialize (s_is_SA_init) as Ht.
    inversion Ht as [i Htrs].
    specialize (s_strand_of_C (s, 1)) as HinC;
    specialize (Nc_iff_inC_Ncp (s, 1)) as [_ Hin].
    st_implication HinC.
    intros Heq; rewrite Heq in Hin.
    destruct Hin; split; try easy.
    autounfold. simplify_term.
  Qed.

  (** We now prove noninjective agreement. *)
  Proposition noninjective_agreement :
    exists s' : Σ,
      SA_responder_strand A B Na s' /\
        is_strand_of s' C.
  Proof.
    specialize (exists_minimal_bundle C_is_bundle Nc_non_empty) as [m [Hin Hmin]].
    assert (Hin':=Hin).
    apply (Nc_iff_inC_Ncp) in Hin' as [HinC HNcp].
    inversion s_is_SA_init as [i Hstrace0].
    specialize (C_is_SA m HinC) as His_SA.
    inversion His_SA as [s' Hpen|A' B' Na' s' HH|A' B' Na' s' HH].

    (** _Penetrator case_ *)
    - inversion Hpen as
        [t j Htrace|g j Htrace|g j Htrace|g h j Htrace|g h j Htrace|k Hpenkey j Htrace|
         k h j Htrace|k h j Htrace].


      all: apply (f_equal tr) in Htrace; specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.

      all: simplify_prop in Hmpti; try tauto.
      specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m, 0) m) as Hnodeof;
      st_implication Hnodeof.

      now specialize
        (penetrator_never_learn_secure_encryption_key C_is_bundle
          (SK_AB_never_originates_regular C_is_SA_bundle A B)
          Hpen Htrace Hnodeof (SK_AB_npen (A:=A) (B:=B))) as Hkey.

    (** _Initiator case_: this is trivially solved by the [simplify_prop] tactic *)
    -
      inversion HH as [j Hsub Hcipher Htrace].
      apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti. now specialize (Hcipher Na A B).

    (** _Responder case_: *)
    - inversion HH as [j Hsub Hcipher Htrace]. apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti; try rewrite Hand2.

      all: exists (strand m); split; auto;
      specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof;
      st_implication Hsof; now rewrite Hand1 in *.
  Qed.

  (* ============================================================ *)
  (** ** Injective agreement *)
  Proposition injectivity :
      uniquely_originates Na ->
        forall U U' s',
          SA_initiator_strand U U' Na s' ->
          s' = s.
  Proof.
    intros Huorig U U' s' Hini'.
    inversion Hini' as [i' Hsub' Hcipher' Htrace'].
    specialize s_is_SA_init as Hini.
    inversion Hini as [i Hsub Hcipher Htrace].
    inversion Huorig as [n [_ Horigx]].
    assert (Horigx' := Horigx).

    specialize (Horigx (s, 0)); specialize (Horigx' (s', 0)).
    specialize (mpti_then_originates Na (s, 0)) as Horig.
    specialize (mpti_then_originates Na (s', 0)) as Horig'.
    specialize (eq_then_sub Na) as Hsubeq.
    simplify_term_in Horig; st_implication Horig.
    simplify_term_in Horig'; st_implication Horig'.
    specialize (Horigx Horig); specialize (Horigx' Horig'); subst.
    now inversion Horigx'.
  Qed.

  (** From [noninjective_agreement] and [injectivity] we obtain injective agreement as a corollary: *)
  Corollary injective_agreement :
      uniquely_originates Na ->
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
