From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Set Implicit Arguments.

Section SimpleAuthSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  NOTE: This is a variant of [SimpleAuth.v] where [Na] is a general term in [𝔸].
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

(** * Proof of Security *)

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
      originates_at_most_once_in C Na ->
        forall U U' s',
          is_strand_of s' C ->
          SA_initiator_strand U U' Na s' ->
          s' = s.
  Proof.
    intros Huorig U U' s' Hstrand' Hini'.
    inversion Hini' as [i' Hsub' Hcipher' Htrace'].
    specialize s_is_SA_init as Hini.
    inversion Hini as [i Hsub Hcipher Htrace].
    pose (s0 := s).
    pose (s0' := s').
    specialize (mpti_then_originates Na (s, 0)) as Horig.
    specialize (mpti_then_originates Na (s', 0)) as Horig'.
    specialize (eq_then_sub Na) as Hsubeq.
    simplify_term_in Horig; st_implication Horig.
    simplify_term_in Horig'; st_implication Horig'.
    assert (is_node_of (s0,0) C) as Hnode by (apply s_strand_of_C; [easy | simpl; lia]).
    assert (is_node_of (s0',0) C) as Hnode' by (apply Hstrand'; [easy | simpl; lia]).
    specialize (Huorig _ _ Hnode Hnode' Horig Horig').
    inversion Huorig; now subst.
  Qed.

  (** From [noninjective_agreement] and [injectivity] we obtain injective agreement as a corollary: *)
  Corollary injective_agreement :
      originates_at_most_once_in C Na ->
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
  Lemma s_ini_SA : SA_initiator_strand A B $Na s_ini.
  Proof. solve_role. Qed.

  Lemma s_res_SA : SA_responder_strand A B $Na s_res.
  Proof. solve_role. Qed.

  Create HintDb sanity.
  #[local] Hint Constructors SA_StrandSpace : sanity.
  #[local] Hint Resolve s_ini_SA s_res_SA : sanity.

  (** [C] is a bundle and every strand of [C] belongs to the strand space, so nothing in it is outside the protocol or the penetrator model. Together: [C] is a valid execution of SimpleAuthUntyped. *)
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
        SA_responder_strand A B $Na s' /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        is_strand_of s'' C ->
        SA_initiator_strand A B $Na s'' ->
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

Section SimpleAuthKeyLeak.
  (** * Sanity check: a key leak
    We exhibit an attack as a second sanity check: the guarantee fails when a regular strand violates the first premise of the roles, [~ #(SK U U') ⊏ Na], by choosing the long-term key as its nonce.  The penetrator learns the key and forges the answer [A] waits for.  No responder strand of [B] towards [A] occurs in the bundle.
  *)

  Notation A  := (Text 0).
  Notation B  := (Text 1).
  Notation Na := (Text 2).
  Notation D  := (Text 3).
  Notation k  := (SK A B).

  (** The roles without their premises, i.e., only the shape of the traces. *)
  Inductive SA_raw_initiator_strand (A B : T) (Na : 𝔸) : Σ -> Prop :=
    | SAR_Init : forall i,
      SA_raw_initiator_strand A B Na (i, [ ⊕ $A ⋅ $B ⋅ Na; ⊖ ⟨ Na ⋅ $A ⟩_(SK A B) ]).

  Inductive SA_raw_responder_strand (A B : T) (Na : 𝔸) : Σ -> Prop :=
    | SAR_Resp : forall i,
      SA_raw_responder_strand A B Na (i, [ ⊖ $A ⋅ $B ⋅ Na; ⊕ ⟨ Na ⋅ $A ⟩_(SK A B) ]).

  (** The strand space of the roles without premises. *)
  Inductive SA_RawStrandSpace (K__P : K -> Prop) : Σ -> Prop :=
    | SARS_Pen  : forall s, penetrator_strand K__P s -> SA_RawStrandSpace K__P s
    | SARS_Init : forall (A B : T) (Na : 𝔸) s,
        SA_raw_initiator_strand A B Na s -> SA_RawStrandSpace K__P s
    | SARS_Resp : forall (A B : T) (Na : 𝔸) s,
        SA_raw_responder_strand A B Na s -> SA_RawStrandSpace K__P s.

  Notation s_ini   := (0, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_k ]).
  (* [B] opens a session with [D] using the key as nonce; only its first node occurs *)
  Notation s_leak  := (1, [ ⊕ $B ⋅ $D ⋅ #k; ⊖ ⟨ #k ⋅ $B ⟩_(SK B D) ]).
  (* the penetrator extracts the key, extracts [Na], and encrypts [Na ⋅ A] itself *)
  Notation s_sepk  := (2, [ ⊖ $B ⋅ $D ⋅ #k; ⊕ $B ⋅ $D; ⊕ #k ]).
  Notation s_sepNa := (3, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ $A ⋅ $B; ⊕ $Na ]).
  Notation s_A     := (4, [ ⊕ $A ]).
  Notation s_cat   := (5, [ ⊖ $Na; ⊖ $A; ⊕ $Na ⋅ $A ]).
  Notation s_enc   := (6, [ ⊖ #k; ⊖ $Na ⋅ $A; ⊕ ⟨ $Na ⋅ $A ⟩_k ]).

  Definition C' : bundle_type :=
    {|
      nodes := rev [
        (s_ini,0);
        (s_leak,0);
        (s_sepk,0);  (s_sepk,1);  (s_sepk,2);
        (s_sepNa,0); (s_sepNa,1); (s_sepNa,2);
        (s_A,0);
        (s_cat,0);   (s_cat,1);   (s_cat,2);
        (s_enc,0);   (s_enc,1);   (s_enc,2);
        (s_ini,1)
      ];
      intra := rev [
        ((s_sepk,0),(s_sepk,1));   ((s_sepk,1),(s_sepk,2));
        ((s_sepNa,0),(s_sepNa,1)); ((s_sepNa,1),(s_sepNa,2));
        ((s_cat,0),(s_cat,1));     ((s_cat,1),(s_cat,2));
        ((s_enc,0),(s_enc,1));     ((s_enc,1),(s_enc,2));
        ((s_ini,0),(s_ini,1))
        ];
      inter := rev [
        ((s_leak,0),(s_sepk,0));   (* B -> P : $B ⋅ $D ⋅ #k        *)
        ((s_ini,0),(s_sepNa,0));   (* A -> P : $A ⋅ $B ⋅ $Na       *)
        ((s_sepNa,2),(s_cat,0));   (* P -> P : $Na                 *)
        ((s_A,0),(s_cat,1));       (* P -> P : $A                  *)
        ((s_sepk,2),(s_enc,0));    (* P -> P : #k                  *)
        ((s_cat,2),(s_enc,1));     (* P -> P : $Na ⋅ $A            *)
        ((s_enc,2),(s_ini,1))      (* P -> A : ⟨ $Na ⋅ $A ⟩_k      *)
        ]
    |}.

  Create HintDb sanity.
  #[local] Hint Constructors SA_RawStrandSpace SA_raw_initiator_strand SA_raw_responder_strand
                             penetrator_strand : sanity.

  (** [C'] is a bundle of the roles without premises. *)
  Lemma C'_is_raw_strandspace_bundle :
    strandspace_bundle C' (SA_RawStrandSpace (K__P_AB A B)).
  Proof. solve_strandspace_bundle. Qed.

  (** The premise that fails: the nonce of [s_leak] is the key itself. *)
  Lemma s_leak_not_SA : forall U U' N, ~ SA_initiator_strand U U' N s_leak.
  Proof.
    intros U U' N H; inversion H as [i Hsub Hcipher].
    apply (Hsub A B). simplify_term.
  Qed.

  Lemma s_ini_strand_C' : is_strand_of s_ini C'.
  Proof. solve_is_strand_of. Qed.

  (** And [B] is absent: no responder strand of [C'] has [B] answering [A]. *)
  Lemma no_responder_for_B :
    ~ (exists s, SA_responder_strand A B $Na s /\ is_strand_of s C').
  Proof. solve_no_strand. Qed.

  (** So the premises are what excludes [C']: in [SA_StrandSpace], [noninjective_agreement] would give the missing responder. *)
  Lemma premises_exclude_C' :
    ~ strandspace_bundle C' (SA_StrandSpace (K__P_AB A B)).
  Proof.
    intro H. apply no_responder_for_B.
    exact (noninjective_agreement s_ini_SA s_ini_strand_C' H).
  Qed.

End SimpleAuthKeyLeak.
