From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Set Implicit Arguments.

Section SimpleAuthDualSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  This protocol is the "dual" of [SimpleAuth.v]: it sends the [Na] and [A] encrypted and expects [Na] in the clear. This version does not send [B] in the clear in the first message. This allows us to use the same proof technique used in the original strand space paper.

  [[
  A -> B :  ⟨ Na ⋅ A ⟩_(SK A B)
  B -> A :  Na
  ]]
  *)

  (* ========================================================= *)
  (** * Protocol specification and roles  **)
  Inductive SA_initiator_strand (A B Na : T) : Σ -> Prop :=
  | SAS_Init : forall i,
    SA_initiator_strand A B Na (i, [ ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊖ $Na ]).

  Inductive SA_responder_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Resp : forall i,
      SA_responder_strand A B Na (i, [ ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊕ $Na ]).

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
End SimpleAuthDualSpec.

(** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective  *)

Section SimpleAuthDualSecurity.
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

  (* ========================================================== *)
  (** ** Non-injective agreement *)

  (* This technique is used in the original strand space paper *)
  Definition Ncp := fun t => $Na ⊏ t /\ ~ (⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ t.
  #[local] Hint Unfold Ncp uns term uns_term : core.

  Lemma Ncp_dec : forall t, { Ncp t } + { ~ Ncp t }.
  Proof.
    intros t;
    autounfold.
    destruct (A_subterm_dec (⟨ $Na ⋅ $A ⟩_(SK A B)) t);
    destruct (A_subterm_dec $Na t);
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
  Qed.

  (** The following lemma states that regular strands never originate pairs [g ⋅ h] such that [(⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ h] or [(⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ g]

  This allows for eliminating the pair destruction case of the penetrator, basically because the penetrator is the only one that might have generated the problematic pairs that contains [(⟨ $Na ⋅ $A ⟩_(SK A B))] in one element and [Na] in the other. These are problematic in general because we could have cases such as [Ncp g], [(⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ h] which imply [~Ncp (g ⋅ h)].

  Notice that this really depends on the protocol syntax and it has nothing to do with its security. Protocols that violates this property cannot be proved using this technique.
  *)
  Lemma pair_not_regular_Ncp_r :
        pair_not_regular_h C_is_bundle (K__P_AB A B) (fun t => ~ (⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ t) /\
        pair_not_regular_g C_is_bundle (K__P_AB A B) (fun t => ~ (⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ t).
  Proof.
    unfold pair_not_regular_h, pair_not_regular_g.
    unfold NWp_pair. unfold p_pair. simpl.
    split.
    all: intros g h n n' Hproph Hin Hmin;
      autounfold in Hproph;
      specialize (NW_iff_inC_p (fun t : 𝔸 => subterm (g ⋅ h) t) C_is_bundle (p_pair_dec g h) n' n) as [HinNW _]; specialize (HinNW Hin);
      specialize (C_is_SA n) as His_SA; st_implication His_SA;
      inversion His_SA as [s' Hpen|A' B' Na' s' Hinires|A' B' Na' s' Hinires]; try easy;
      inversion Hinires as [i Htrace]; apply (f_equal tr) in Htrace;
      unfold NWp_pair in *;
      specialize (minimal_NWp_pair_then_mpt C_is_bundle g h n' Htrace Hin Hmin) as Hmpti;
      unfold p_pair in Hmpti; simpl in Hmpti;
      simplify_prop in Hmpti;
      simplify_prop in Hproph.
  Qed.

  Proposition noninjective_agreement :
    originates_at_most_once_in C $Na ->
        exists s' : Σ,
        SA_responder_strand A B Na s' /\
        is_strand_of s' C.
  Proof.
    intros Huniq.
    specialize (exists_minimal_bundle C_is_bundle Nc_non_empty) as [m [Hin Hmin]].
    assert (Hin':=Hin).
    apply (Nc_iff_inC_Ncp) in Hin' as [HinC HNcp].
    inversion s_is_SA_init as [i Hstrace0].
    specialize (C_is_SA m HinC) as His_SA.
    inversion His_SA as [s' Hpen|A0 B0 N0__a s' Hini|A0 B0 N0__a s' Hres].

    (** _Penetrator case_ *)
    - inversion Hpen as
        [t j Htrace|g j Htrace|g j Htrace|g h j Htrace|g h j Htrace|k Hpenkey j Htrace|
         k h j Htrace|k h j Htrace].
      all: apply (f_equal tr) in Htrace; specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      pose (s0:=s).
      all: simplify_prop in Hmpti; try tauto.

      + specialize
        (index_0_positive_originates m (t:=$Na)) as Horig1.
        specialize (index_0_positive_originates (s0, 0) (t:=$Na)) as Horig2.
        unfold is_positive in Horig1; st_implication Horig1.
        simplify_term_in Horig2; unfold is_positive in Horig2; st_implication Horig2.
        assert (is_node_of (s0,0) C) as Hnode by (apply s_strand_of_C; [easy | simpl; lia]).
        specialize (Huniq _ _ HinC Hnode Horig1 Horig2).
        inversion Huniq; now subst.

      + (* pair case h *)
        assert ((⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ h) as Hinh. { destruct (A_subterm_dec (⟨ $Na ⋅ $A ⟩_(SK A B)) h);
          try easy. st_implication Hand. }
        specialize (penetrator_pair_not_minimal_g (B:=C) (B_is_bundle:=C_is_bundle) Ncp_dec Hpen Htrace) as Hpen_g.
        specialize (pair_not_regular_Ncp_r) as [Hnotreh _].
        rewrite <-Hand2 in Hpen_g. rewrite <-(node_as_pair) in Hpen_g.
        st_implication Hpen_g.

      + (* pair case g *)
        assert ((⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ g) as Hinh. { destruct (A_subterm_dec (⟨ $Na ⋅ $A ⟩_(SK A B)) g);
          try easy. st_implication Hand. }
        specialize (penetrator_pair_not_minimal_h (B:=C) (B_is_bundle:=C_is_bundle) Ncp_dec Hpen Htrace) as Hpen_h.
        specialize (pair_not_regular_Ncp_r) as [_ Hnotreh].
        rewrite <-Hand3 in Hpen_h. rewrite <-(node_as_pair) in Hpen_h.
        st_implication Hpen_h.

      + specialize (index_lt_strand_implies_is_node_of  C_is_bundle (strand m, 0) m) as Hnodeof;
        st_implication Hnodeof.

        (** we eliminate this case by exploiting the fact that the penetrator can never learn a secure symmetric key *)

        specialize (SK_AB_never_originates_regular C_is_SA_bundle A B) as Hnever.
        specialize (SK_AB_npen (A:=A) (B:=B)) as HSK_AB_npen.
        rewrite (SK_symmetric) in HSK_AB_npen.
        rewrite (SK_symmetric) in Hnever.
        specialize
          (penetrator_never_learn_secure_decryption_key
            C_is_bundle Hnever Hpen Htrace Hnodeof HSK_AB_npen) as Hkey.
        destruct Hand; split; try easy.
        simplify_prop in |- *.

    (** _Initiator case_ *)
    - inversion Hini as [j Htrace].
      apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      pose (s0:=s).
      simplify_prop in Hmpti.

      all: specialize (index_0_positive_originates m (t:=$Na)) as Horig1;
      unfold is_positive in Horig1; st_implication Horig1;
      specialize (index_0_positive_originates (s0, 0) (t:=$Na)) as Horig2;
      simplify_term_in Horig2; unfold is_positive in Horig2; st_implication Horig2;
      assert (is_node_of (s0,0) C) as Hnode by (apply s_strand_of_C; [easy | simpl; lia]);
      specialize (Huniq _ _ HinC Hnode Horig1 Horig2);
      inversion Huniq; subst;
      symmetry in Htrace;
      inversion Htrace; subst;
      simplify_prop in H1; try tauto.

    (** _Responder case_: *)
    - inversion Hres as [j Htrace].
      apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti; try rewrite Hand2.

      (** Here we have two cases depending whether A and B are equal or not. Both cases are solved trivially as they provide a valid bindings for the protocol parameters. *)
      all: exists (strand m); split; auto;
      specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof;
      st_implication Hsof.
      destruct (T_eq_dec A A0); destruct (T_eq_dec B B0); subst;
      simplify_prop in Hand. destruct Hand. intros.
      simplify_prop in H.
  Qed.

  (* ============================================================ *)
  (** ** Injective agreement  *)

  Proposition injectivity :
    originates_at_most_once_in C $Na ->
      forall s' : Σ,
        is_strand_of s' C ->
        SA_initiator_strand A B Na s' ->
        s' = s.
  Proof.
    intros Huorig s' Hstrand' Hini'.
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
End SimpleAuthDualSecurity.

Section SimpleAuthDualSanity.
  (** * Sanity check: an honest run
    We exhibit an honest protocol execution as a sanity check: the protocol executes and satisfies all of the assumptions of the security lemmas.
  *)

  Notation A := (Text 0).
  Notation B := (Text 1).
  Notation Na := (Text 2).
  
  Notation s_ini := (0, [ ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊖ $Na ]).
  Notation s_res := (1, [ ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊕ $Na ]).

  (** A single honest session: [A] sends the nonce and its name encrypted under the shared key, [B] answers with the nonce in the clear, i.e., the dual of [SimpleAuth], where the plaintext comes first. The three lists are reversed because each [IndBundle] constructor conses onto their heads, so they are written in reverse construction order. *)
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
        ((s_ini,0),(s_res,0));   (* A -> B : ⟨ $Na ⋅ $A ⟩_(SK A B) *)
        ((s_res,1),(s_ini,1))    (* B -> A : $Na                   *)
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
  
  (** [C] is a bundle and every strand of [C] belongs to the strand space, so nothing in it is outside the protocol or the penetrator model. Together: [C] is a valid execution of SimpleAuthDual. *)
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

End SimpleAuthDualSanity.

Section SimpleAuthDualImpersonation.
  (** * Sanity check: an impersonation
    We exhibit an attack as a second sanity check: the guarantee fails exactly when its freshness hypothesis does, so the hypothesis is not decoration. Here it fails harder than in [SimpleAuth]: what breaks is agreement itself, not only its injectivity.
  *)

  Notation A := (Text 0).
  Notation B := (Text 1).
  Notation Na := (Text 2).

  Notation s_ini := (0, [ ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B); ⊖ $Na ]).
  (** The impersonation: the reply is [$Na] in the clear, so producing it needs no key at all, only knowledge of [$Na], which [PT_M] mints. In [SimpleAuth] the reply is [⟨ $Na ⋅ $A ⟩_(SK A B)] and the penetrator can only relay one that a responder produced; here it can speak for [B] outright. *)
  Notation s_pen := (1, [ ⊕ $Na ]).

  (** [A] opens a session and the penetrator answers it directly. Nobody reads the first message: the penetrator never needed to decrypt it. *)
  Definition C' : bundle_type :=
    {|
      nodes := rev [
        (s_ini,0);    (* A's message is ignored, nobody receives it *)
        (s_pen,0);
        (s_ini,1)
      ];
      intra := rev [
        ((s_ini,0),(s_ini,1))
        ];
      inter := rev [
        ((s_pen,0),(s_ini,1))    (* P -> A : $Na *)
        ]
    |}.

  Create HintDb sanity.
  #[local] Hint Constructors SA_StrandSpace SA_initiator_strand SA_responder_strand
                             penetrator_strand : sanity.

  (** Nothing here breaks the rules: [C'] is a bundle and every strand of it, the penetrator's included, belongs to the strand space. *)
  Lemma C'_is_strandspace_bundle:
    strandspace_bundle C' (SA_StrandSpace (K__P_AB A B)).
  Proof. solve_strandspace_bundle. Qed.

  Lemma s_ini_strand_C' : is_strand_of s_ini C'.
  Proof. solve_is_strand_of. Qed.

  (** The hypothesis that fails: [$Na] originates twice, once where [A] sends it and once where the penetrator mints it. This is what freshness rules out, and it is why the hypothesis carries secrecy here and not only uniqueness: nothing else in this protocol stops the penetrator from knowing [$Na]. *)
  Lemma Na_not_at_most_once :
    ~ originates_at_most_once_in C' $Na.
  Proof. refute_at_most_once_in (s_ini,0) (s_pen,0). Qed.

  (** And [B] is absent: the conjunct that fails is agreement itself, not its injectivity. *)
  Lemma no_responder_for_B :
    ~ (exists s, SA_responder_strand A B Na s /\ is_strand_of s C').
  Proof. solve_no_strand. Qed.

End SimpleAuthDualImpersonation.
