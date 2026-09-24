From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

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

(** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

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

  (** We now define the set of nodes belonging to bundle_type C, that have c as subterm.
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
  The second security property additionally states that each responder session correspond to different initiator session, i.e., that authentication is injective and cannot be reused in a replay attack. This property only holds if [Na] is freshly generated which, in the strand spaces model, is captured by unique origination as defined in the S&P paper. In StrandsRocq this property is split in two parts and localized to a bundle. Typically we only require the relevant one [originates_at_most_once_in C] which tells that a given term cannot originate twice in bundle C, i.e., is fresh. The actual origination does not matter for injectivity. Formally:
  [[
    originates_at_most_once_in C $Na ->
    (
      exists s' : Σ,
        SA_responder_strand A B Na (tr s') /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        is_strand_of s'' C ->
        SA_initiator_strand A B Na (tr s'') ->
        s'' = s
    ).
  ]]
  We first prove injectivity alone, i.e., if [Na] originates at most once in [C] then there is a unique initiator trace agreeing on [Na]. This is fairly trivial and the proof just applies the definition of [originates_at_most_once_in C]:
  *)
  Proposition injectivity :
    originates_at_most_once_in C $Na ->
      forall U U' s',
        is_strand_of s' C ->
        SA_initiator_strand U U' Na s' ->
        s' = s.
  Proof.
    intros Huorig U U' s' Hstrand' Hini'.
    inversion Hini' as [i' Htrace'].
    specialize s_is_SA_init as Hini.
    inversion Hini as [i Htrace].
    pose (s0 := s).
    pose (s0' := s').
    specialize (mpti_then_originates $Na (s, 0)) as Horig.
    specialize (mpti_then_originates $Na (s', 0)) as Horig'.
    simplify_term_in Horig; st_implication Horig.
    simplify_term_in Horig'; st_implication Horig'.
    assert (is_node_of (s0,0) C) as Hnode by (apply s_strand_of_C; [easy | simpl; lia]).
    assert (is_node_of (s0',0) C) as Hnode' by (apply Hstrand'; [easy | simpl; lia]).
    specialize (Huorig _ _ Hnode Hnode' Horig Horig').
    inversion Huorig; now subst.
  Qed.

  (** From [noninjective_agreement] and [injectivity] we obtain injective agreement as a corollary: *)
  Corollary injective_agreement :
    originates_at_most_once_in C $Na ->
    (
      exists s' : Σ,
        SA_responder_strand A B Na s' /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        is_strand_of s'' C ->
        SA_initiator_strand A B Na s'' ->
        s'' = s
    ).
  Proof.
    intros Huniq. split.
    - now apply noninjective_agreement.
    - now apply injectivity.
  Qed.

End SimpleAuthSecurity.

Section SimpleAuthSanity.
  (** * Sanity check: an honest run
    We exhibit an honest protocol execution as a sanity check: the protocol executes and satisfies all of the assumptions of the security lemmas.
  *)

  Notation A := (Text 0).
  Notation B := (Text 1).
  Notation Na := (Text 2).
  
  Notation s_ini := (0, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  Notation s_res := (1, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).

  (** A single honest session: [A] sends its name, [B]'s name and the nonce, [B] answers with the nonce encrypted under the shared key.  The three lists are reversed because each [IndBundle] constructor conses onto their heads, so they are written in reverse construction order. *)
  Definition C : bundle_type :=
    {|
      nodes := rev [
        (s_ini,0);
        (s_res,0);
        (s_res,1);
        (s_ini,1)
      ];
      intra := rev [
        ((s_res,0),(s_res,1));
        ((s_ini,0),(s_ini,1))
        ];
      inter := rev [
        ((s_ini,0),(s_res,0));   (* A -> B : $A ⋅ $B ⋅ $Na         *)
        ((s_res,1),(s_ini,1))    (* B -> A : ⟨ $Na ⋅ $A ⟩_(SK A B) *)
        ]
    |}.

  (** The two strands are legitimate roles of the protocol. *)
  Lemma s_ini_SA : SA_initiator_strand A B Na s_ini.
  Proof. solve_role. Qed.

  Lemma s_res_SA : SA_responder_strand A B Na s_res.
  Proof. solve_role. Qed.

  Create HintDb sanity.
  #[local] Hint Constructors SA_StrandSpace : sanity.
  #[local] Hint Resolve s_ini_SA s_res_SA : sanity.
  
  (** [C] is a bundle and every strand of [C] belongs to the strand space, so nothing in it is outside the protocol or the penetrator model. Together: [C] is a valid execution of SimpleAuth. *)
  Lemma C_is_strandspace_bundle: 
    strandspace_bundle C (SA_StrandSpace (K__P_AB A B)).
  Proof. solve_strandspace_bundle. Qed.

  (** [s_ini] is a strand of C. This is the initiator point of view in the security lemma. *)
  Lemma s_ini_strand_C : 
    is_strand_of s_ini C.
  Proof. solve_is_strand_of. Qed.

  (** [Na] is originated at most once (in fact exactly once in [s_ini]) *)
  Lemma C_Na_at_most_once : 
    originates_at_most_once_in C $ Na.
  Proof. solve_at_most_once_in. Qed.
    
  (** The conclusion is what we already know by construction since we have exactly one initiator and one responder in [C]. So, the important part is that the term typechecks, which is possible only if the four hypotheses of [injective_agreement] hold at once, i.e., the guarantee is not vacuous. *)
  Lemma injective_agreement_sanity :
    (
      exists s' : Σ,
        SA_responder_strand A B Na s' /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        is_strand_of s'' C ->
        SA_initiator_strand A B Na s'' ->
        s'' = s_ini
    ).
  Proof.
    exact (
      injective_agreement 
        s_ini_SA 
        s_ini_strand_C
        C_is_strandspace_bundle 
        C_Na_at_most_once
      ).
  Qed.

End SimpleAuthSanity.

Section SimpleAuthReplay.
  (** * Sanity check: a replay attack
    We exhibit an attack as a second sanity check: the guarantee fails exactly when its freshness hypothesis does, so the hypothesis is not decoration.
  *)

  Notation A := (Text 0).
  Notation B := (Text 1).
  Notation Na := (Text 2).

  Notation s_res  := (1, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  Notation s_ini1 := (0, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  Notation s_ini2 := (2, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  (** The replay attack: *)
  Notation s_pen  := (3, [ ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).

  (** [A] opens two sessions with the same nonce, [B] answers once, and the penetrator tees the answer to both. *)
  Definition C' : bundle_type :=
    {|
      nodes := rev [
        (s_ini1,0);
        (s_res,0);
        (s_res,1);
        (s_pen,0);
        (s_pen,1);
        (s_pen,2);
        (s_ini1,1);
        (s_ini2,0);   (* A.2 message is ignored, nobody receives it *)
        (s_ini2,1)
      ];
      intra := rev [
        ((s_res,0),(s_res,1));
        ((s_pen,0),(s_pen,1));
        ((s_pen,1),(s_pen,2));
        ((s_ini1,0),(s_ini1,1));
        ((s_ini2,0),(s_ini2,1))
        ];
      inter := rev [
        ((s_ini1,0),(s_res,0));   (* A.1 -> B   : $A ⋅ $B ⋅ $Na         *)
        ((s_res,1),(s_pen,0));    (* B   -> P   : ⟨ $Na ⋅ $A ⟩_(SK A B) *)
        ((s_pen,1),(s_ini1,1));   (* P   -> A.1 : ⟨ $Na ⋅ $A ⟩_(SK A B) *)
        ((s_pen,2),(s_ini2,1))    (* P   -> A.2 : ⟨ $Na ⋅ $A ⟩_(SK A B) *)
        ]
    |}.

  Create HintDb sanity.
  #[local] Hint Constructors SA_StrandSpace SA_initiator_strand SA_responder_strand
                             penetrator_strand : sanity.

  (** Nothing here breaks the rules: [C'] is a bundle and every strand of it, the penetrator's included, belongs to the strand space. *)
  Lemma C'_is_strandspace_bundle:
    strandspace_bundle C' (SA_StrandSpace (K__P_AB A B)).
  Proof. solve_strandspace_bundle. Qed.

  Lemma s_ini1_strand_C' : is_strand_of s_ini1 C'.
  Proof. solve_is_strand_of. Qed.

  Lemma s_ini2_strand_C' : is_strand_of s_ini2 C'.
  Proof. solve_is_strand_of. Qed.

  (** [B] ran once: any responder strand of [C'] is [s_res]. *)
  Lemma one_responder_only :
    forall s, is_strand_of s C' -> SA_responder_strand A B Na s -> s = s_res.
  Proof. solve_unique_strand. Qed.

  (** The hypothesis that fails: [$Na] originates twice, once per initiator session. *)
  Lemma Na_not_at_most_once :
    ~ originates_at_most_once_in C' $Na.
  Proof. refute_at_most_once_in (s_ini1,0) (s_ini2,0). Qed.

  (** And the conjunct that freshness protects does fail: the initiator session is not unique.  Compare [injective_agreement_sanity], where the same conjunct holds because [$Na] originates once. *)
  Lemma injectivity_fails :
    ~ (forall s'', is_strand_of s'' C' -> SA_initiator_strand A B Na s'' -> s'' = s_ini1).
  Proof.
    intro H. specialize (H s_ini2 s_ini2_strand_C' (SAS_Init A B Na 2)). discriminate.
  Qed.

End SimpleAuthReplay.
