Require Import Lia.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Set Implicit Arguments.

Section SimpleAuthSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

    We consider a simple unilateral authentication protocol based on nonces. The initiator [A] sends a fresh nonce [Na] to the responder [B] who encrypts it together with [A]'s identifier under a symmetric key [SK A B] shared with [A]. The protocol in the Alice/Bob notation follows:
    [[
    A -> B :  A ⋅ B ⋅ Na
    B -> A :  ⟨ Na ⋅ A ⟩_(SK A B)
    ]]
    We use [⟨ M ⟩_k] to note the encryption of [M] under key [k] and [M1 ⋅ M2] to denote the concatenation of [M1] and [M2].
  *)

  (* ============================================================ *)
  (** * Protocol Specification
    Typically honest principals have a single trace quantified over parameters and payload values. In general, however, a principal might execute more than one trace. For example, the penetrator executes different possible traces. Even when we model APIs, we have a single principal/device that implements a variety of functionalities each modeled by a different trace. For this reason, we specify the protocol roles by providing, inductively all the possible traces they can execute.  **)

  (* ============================================================ *)
  (**  ** Protocol Roles **)
  (** The initiator sends a fresh nonce [Na] as output and reads the expected answer [⟨ Na ⋅ A ⟩_(SK A B)] from the responder. Since the type of [Na] is [T], representing atomic terms, we write [$Na] to represent its value as generic term of type [A]. [⊕] represents an output node, thus the corresponding trace is [[ ⊕ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]].
  *)
  Inductive SA_initiator_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Init : forall i,
      SA_initiator_strand A B Na (i, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).

  Inductive SA_responder_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Resp : forall i,
      SA_responder_strand A B Na (i, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).

  Definition K__P_AB (A B : T) (k : K) := k <> SK A B.

  Inductive SA_StrandSpace (K__P : K -> Prop) : Σ -> Prop :=
    | SASS_Pen  : forall s, penetrator_strand K__P s -> SA_StrandSpace K__P s
    | SASS_Init : forall (A B Na : T) s, SA_initiator_strand A B Na s -> SA_StrandSpace K__P s
    | SASS_Resp : forall (A B Na : T) s, SA_responder_strand A B Na s -> SA_StrandSpace K__P s.

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
    inversion His_SA as [s Hpen|A B Na s Hinires|A B Na s Hinires]; try easy;
    rewrite <-H in Hinires;
    destruct Hinires; apply strand_trace in H;
    inversion H as [Htrace];
    apply (originates_then_mpt Htrace) in Horig;
    unfold mpt in Horig; now simplify_prop in Horig.
  Qed.

  (**
    Given the definition of [K__P_AB], we can also (trivially) prove that the attacker has no knowledge of the session key.
  *)
  Lemma SK_AB_npen : forall A B, ~ penetrator_key (K__P_AB A B) (SK A B).
  Proof. now unfold penetrator_key, K__P_AB. Qed.
End SimpleAuthSpec.

Section SimpleAuthSecurity.
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : edge_set__t.

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
  The first security property states that the initiator is guaranteed that the responder run the protocol and agreed on parameters [A], [B] and [Na]. Formally:
  [[
    exists s' : Σ,
      SA_responder_strand A B Na (tr s') /\
      is_strand_of s' C.
  ]]
  The proof revolves around showing that only the responder, with parameters [A], [B] and [Na], can generate the expected ciphertext [⟨ $Na ⋅ $A ⟩_(SK A B)] that we note [c] in the following:
  *)

  (** We now define the set of nodes belonging to bundle C, that have c as subterm.
  First, we define a function [Ncp] from terms to [Prop] that checks if [c ⊏ t] and we prove its decidability.
  Then, we partially instantiate [N], [N_iff_inC_p] and [minimal_N_then_mpt] from MinimalMPT.v in order to respectively define
  - [Nc] : the set of nodes whose term satisfy [Ncp];
  - [Nc_iff_inC_Ncp] : the logical characterization of nodes belonging to [Nc], i.e., [In n (nodes_of C) /\ Ncp (uns_term n)]
  - [minimal_Nc_then_mpt] : a lemma that allows to characterize the minimal of [Nc] as a Prop.
  *)

  Definition Ncp (t : 𝔸) := (⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ t.
  #[local] Hint Unfold Ncp uns term uns_term : core.

  Lemma Ncp_dec : forall t, { Ncp t } + { ~ Ncp t }.
  Proof.
    intros t;
    destruct (A_subterm_dec (⟨ $Na ⋅ $A ⟩_(SK A B)) t);
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

  (** We now prove noninjective agreement. The proof is based on lemma [exists_minimal_bundle] stating that each nonempty subset of nodes has a minimal with respect to the [bundle_le] ([⪯]) relation. We apply the lemma to [Nc]. This minimal node is, intuitively, the one that performs the encryption in [c]. We reason by cases and we prove that this minimal node cannot lie neither on a Penetrator nor on an Initiator strand. It lies instead on a Responder strand whose parameters can be proved to be exactly [A], [B] and [Na], as required by the agreement property. Notice, in fact, that [c] contains [A], [Na] in the payload and [B], implicitly, in the key [SK A B]. *)
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
      simplify_prop in Hmpti; try rewrite Hand2.

      (** Here we have two cases depending whether A and B are equal or not. Both cases are solved trivially as they provide a valid binding for the protocol parameters. *)

      all: exists (strand m); split; auto;
      specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof;
      st_implication Hsof.
  Qed.

  (* ============================================================ *)
  (** ** Injective agreement
  The second security property additionally states that each responder session correspond to different initiator session, i.e., that authentication is injective and cannot be reused in a replay attack. This property only holds if [Na] is freshly generated which, in the strand spaces model, is captured by the [uniquely_originates] definition. Formally:
  [[
    uniquely_originates $Na ->
    (
      exists s' : Σ,
        SA_responder_strand A B Na (tr s') /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        SA_initiator_strand A B Na (tr s'') ->
        s'' = s
    ).
  ]]
  We first prove injectivity alone, i.e., if [Na] uniquely originates then there's a unique initiator trace agreeing on [Na]. This is somehow trivial and the proofs just applies the definition on [uniquely_originates]:
  *)
  Proposition injectivity :
      uniquely_originates $Na ->
        forall U U' s',
          SA_initiator_strand U U' Na s' ->
          s' = s.
  Proof.
    intros Huorig U U' s' Hini'.
    inversion Hini' as [i' Htrace'].
    specialize s_is_SA_init as Hini.
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

  (** From [noninjective_agreement] and [injectivity] we obtain injective agreement as a corollary: *)
  Corollary injective_agreement :
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
