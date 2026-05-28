From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Set Implicit Arguments.

Section SimpleAuthSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  ** NOTE: This is a FLAWED variant of [SimpleAuth.v] with no id in the payload.
  [[
  A -> B :  A ⋅ B ⋅ Na
  B -> A :  ⟨ Na ⟩_(SK A B)
  ]]
  *)

  Inductive SA_initiator_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Init : forall i,
      SA_initiator_strand A B Na (i, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⟩_(SK A B) ]).

  Inductive SA_responder_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Resp : forall i,
      SA_responder_strand A B Na (i, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ ⟨ $Na ⟩_(SK A B) ]).

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
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : bundle_graph.

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
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

  (* ============================================================ *)
  (** ** Non-injective agreement
  *)
  Definition Ncp := fun t => (⟨ $Na ⟩_(SK A B)) ⊏ t.
  #[local] Hint Unfold Ncp uns term uns_term : core.

  Lemma Ncp_dec : forall t, { Ncp t } + { ~ Ncp t }.
  Proof.
    intros t;
    destruct (A_subterm_dec (⟨ $Na ⟩_(SK A B)) t);
    (try now right); (try now left).
  Qed.

  Definition Nc := N Ncp C Ncp_dec.
  Definition Nc_iff_inC_Ncp := N_iff_inC_p Ncp C Ncp_dec.
  Definition minimal_Nc_then_mpt := minimal_N_then_mpt Ncp C_is_bundle Ncp_dec.

  Lemma Nc_non_empty :
    Nc <> nil.
  Proof.
    unfold Nc.
    specialize (s_is_SA_init) as Ht; inversion Ht as [Htrs].
    specialize (s_strand_of_C (s, 1)) as HinC.
    specialize (Nc_iff_inC_Ncp (s, 1)) as [_ Hin].
    st_implication HinC.
    intros Heq; rewrite Heq in Hin.
    destruct Hin; split; try easy.
    autounfold. simplify_term.
  Qed.

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
    inversion His_SA as [s' Hpen|A' B' Na' s' Hini|A' B' Na' s' Hres].

    (** _Penetrator case_ *)
    - inversion Hpen as
        [t j Htrace|g j Htrace|g j Htrace|g h j Htrace|g h j Htrace|k Hpenkey j Htrace|
         k h j Htrace|k h j Htrace].

      (** we now use the [minimal_Nc_then_mpt] lemma which provides a characterization of the minimal element of Nc in terms of a Prop covering all the possible cases.

      For example, for the first case, which is the output of an atomic term [t] written [[⊕ $ t]] we obtain the following Prop [False \/ c = $ t /\ True /\ index m = 0], stating that [c = $ t], which is clearly false since [c] is a ciphertext.

      In other cases the [Prop] is more complicate. For example, for pair generation [[⊖ g; ⊖ h; ⊕ g ⋅ h]] we obtain
      [[
        ((False \/ subterm c g /\ False /\ index m = 0) \/
        ~ subterm c g /\ subterm c h /\ False /\ index m = 1) \/
        ~ subterm c g /\ ~ subterm c h /\
        (c = g ⋅ h \/ subterm c g \/ subterm c h) /\
        True /\ index m = 2
      ]]
      that is less trivial to analyze by hand. *)
      all: apply (f_equal tr) in Htrace; specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.

      (** the [simplify_prop] tactic eliminates all cases except the interesting one, i.e., the encryption case: [[⊖ # (SK A B); ⊖ $ Na ⋅ $ A; ⊕ c]]. *)

      all: simplify_prop in Hmpti; try tauto.
      specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m, 0) m) as Hnodeof;
      st_implication Hnodeof.

      (** We eliminate this case by exploiting the fact that the penetrator can never learn a secure symmetric key *)
      now specialize
        (penetrator_never_learn_secure_encryption_key C_is_bundle
          (SK_AB_never_originates_regular C_is_SA_bundle A B)
          Hpen Htrace Hnodeof (SK_AB_npen (A:=A) (B:=B))) as Hkey.

    (** _Initiator case_: this is trivially solved by the [simplify_prop] tactic *)
    - inversion Hini as [j Htrace]; apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti.

    (** _Responder case_: *)
    - inversion Hres as [j Htrace]. apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      (* simplify_prop derives that A0 = A, B0 = B, Na__0 = Na and performs the substitution *)
      simplify_prop in Hmpti; try rewrite Hand1.
      all: exists (strand m); split; auto;
      specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof;
      st_implication Hsof.

      (** Here, in our hypotheses, we encounter [SA_responder_traces B A Na [⊖ ($ A ⋅ $ B) ⋅ $ Na; ⊕ ⟨ $ Na ⟩_ SK A B]], indicating a well-known reflection attack where [(⟨ $Na ⟩_(SK A B))] is generated by [A] itself acting as the responder. Proving the expected agreement [SA_responder_traces A B Na [⊖ ($ B ⋅ $ A) ⋅ $ Na; ⊕ (⟨ $Na ⟩_(SK A B))]] with [A] and [B] swapped is not possible, unless we are in the specific scenario where [A = B]. In this particular case, [A] is persuaded to communicate with [A], which holds true even if the attacker reflects messages between two distinct sessions.

      In fact, the proof could be closed forcing [A=B] assumption as follows:
      *)

      assert (A=B) as Hself by give_up.
      rewrite Hself in *. tauto.
  Abort. (* this proof is not valid, the protocol is flawed *)

End SimpleAuthSecurity.
