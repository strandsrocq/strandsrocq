Require Import Lia.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator. (* We depend on Penetrator just to avoid code duplication *)

Set Implicit Arguments.

Section SimpleAuthSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  This is the [SimpleAuth.v] protocol in which we define a maximal penetrator that can do everything except originating [SK A B] and [⟨ p ⟩_(SK A B)] without knowing [SK A B].
  [[
  A -> B :  A ⋅ B ⋅ Na
  B -> A :  ⟨ Na ⋅ A ⟩_(SK A B)
  ]]
  *)

  (* ============================================================ *)
  (** * Protocol Specification  *)
  Inductive SA_initiator_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Init : forall i,
      SA_initiator_strand A B Na (i, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).

  Inductive SA_responder_strand (A B Na : T) : Σ -> Prop :=
    | SAS_Resp : forall i,
      SA_responder_strand A B Na (i, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).

  Definition Ncp A B Na t := (⟨ $Na ⋅ $A ⟩_(SK A B)) ⊏ t.

  (* This definition captures the fact the the penetrator should not forge a cipher
     without knowing the encryption key [SK A B]. The idea is to only require this and
     let the penetrator do whatever else they want *)
  Definition NoForgeCipher A B n :=
    forall p, originates (⟨ p ⟩_(SK A B)) n ->
      exists n', n' ⟹+ n /\ term n' = ⊖ #(SK A B).

  Inductive SA_maximal_penetrator_strand (A B : T) : Σ -> Prop :=
    | SAS_Pen : forall s,
        ( forall n, s = strand n ->
          ~originates #(SK A B) n /\ NoForgeCipher A B n ) ->
          SA_maximal_penetrator_strand A B s.

  Inductive SA_StrandSpace (A' B' : T) : Σ -> Prop :=
    | SASS_Pen  : forall s, SA_maximal_penetrator_strand A' B' s -> SA_StrandSpace A' B' s
    | SASS_Init1 : forall A B Na s, SA_initiator_strand A B Na s -> SA_StrandSpace A' B' s
    | SASS_Resp1 : forall A B Na s, SA_responder_strand A B Na s -> SA_StrandSpace A' B' s.

  (* We show that the usual DY penetrator is subsumed by the maximal one *)
  Definition K__P_AB (A B : T) (k : K) := k <> SK A B.

  Lemma DY_is_SA_maximal_penetrator:
    forall A B s, penetrator_strand (K__P_AB A B) s -> SA_maximal_penetrator_strand A B s.
  Proof.
    intros A B s Hpen. split. intros n Hstrand. split.
    - unfold not. intros Horig.
      inversion Hpen as
        [t j Htrace|g j Htrace|g j Htrace|g h j Htrace|g h j Htrace|k Hpenkey j Htrace| k h j Htrace|k h j Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace; rewrite Hstrand in Htrace;
      apply (originates_then_mpt Htrace) in Horig;
      simplify_prop in Horig.
    - unfold NoForgeCipher. intros p Horig.
       inversion Hpen as
        [t j Htrace|g j Htrace|g j Htrace|g h j Htrace|g h j Htrace|k Hpenkey j Htrace| k h j Htrace|k h j Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace; rewrite Hstrand in Htrace;
      apply (originates_then_mpt Htrace) in Horig;
      simplify_prop in Horig using decidability.
      exists ((strand n),0). split; try simplify_term.
      rewrite node_as_pair. rewrite Hand2. apply lt_intrastrand_index; simpl. lia. now easy.
  Qed.

  (* Also, the DY penetrator is strictly subsumed by the maximal penetrator.
  *)
  Lemma SA_maximal_penetrator_not_eq_DY:
  forall A B,
      exists s,
        SA_maximal_penetrator_strand A B s /\ ~ penetrator_strand (K__P_AB A B) s.
  Proof.
    intros A B.
    assert (m : 𝔸) by constructor.

    exists (0, [⊖ ⟨ m ⟩_(SK A B); ⊕ m ]).
    split.
    - apply SAS_Pen. intros n Hstrand; apply (f_equal tr) in Hstrand; simpl in Hstrand. split.
      + intros Horig. apply (originates_then_mpt Hstrand) in Horig.
        simplify_prop in Horig.
      + intros p Horig. apply (originates_then_mpt Hstrand) in Horig.
        simplify_prop in Horig. destruct Hand. right. easy.
    - intros Hpen. inversion Hpen.
  Qed.

  (* The next results are useful to enable protocol composition under maximal penetrators *)

  (* penetrator is powerful enough to simulate any initiator! *)
  Lemma ini_penetrator :
    forall s A B Na A' B',
      SA_initiator_strand A' B' Na s ->
      SA_maximal_penetrator_strand A B s.
  Proof.
    intros s A B Na A' B' Hini.
    inversion Hini. split.
    intros n Hstrand; apply (f_equal tr) in Hstrand; simpl in Hstrand. split.
    - unfold not. intros Horig. apply (originates_then_mpt Hstrand) in Horig.
      simplify_prop in Horig.
    - intros p Horig. apply (originates_then_mpt Hstrand) in Horig.
      simplify_prop in Horig.
  Qed.
  (* penetrator can simulate responders only if pair [A B] differs from [A' B'] and [B' A'] *)
  Lemma res_penetrator :
    forall s A B Na A' B',
      ~((A = A' /\ B = B') \/ (A = B' /\ B = A')) ->
      SA_responder_strand A' B' Na s ->
      SA_maximal_penetrator_strand A B s.
  Proof.
    intros s A B Na A' B' Hneq Hres.
    inversion Hres. split.
    intros n Hstrand; apply (f_equal tr) in Hstrand; simpl in Hstrand. split.
    - unfold not. intros Horig. apply (originates_then_mpt Hstrand) in Horig.
      simplify_prop in Horig.
    - intros p Horig. apply (originates_then_mpt Hstrand) in Horig.
      simplify_prop in Horig.
      all: simplify_prop in Hneq using decidability.
  Qed.

  (* ============================================================ *)
  Lemma SK_AB_never_originates :
    forall C A B n, C_is_SS C (SA_StrandSpace A B) ->
      is_node_of n C ->
      ~originates #(SK A B) n.
  Proof.
    intros C A B n H_is_SS H_is_node_of  Horig. specialize (H_is_SS n H_is_node_of).
    inversion H_is_SS.
    1: inversion H as [n0 Horig' Hstrand]; specialize (Horig' n); st_implication Horig'.
    1,2: inversion H as [i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace;
    apply (originates_then_mpt Htrace) in Horig;
    simplify_prop in Horig.
  Qed.
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
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_SA_bundle : C_is_SS C (SA_StrandSpace A B).

  (*
      NoForgeCipher is sufficient to prove that the attacker dees not originate the
     ciphertext [⟨ $Na ⋅ $A ⟩_(SK A B)]. This lemma is enough to reject the penetrator
     case in the authentication lemma
  *)
  Lemma NoForgeCipher_not_is_mpti:
    forall n, is_node_of n C ->
      NoForgeCipher A B n ->
      ~is_mpti n 0 (index n) (tr (strand n)) (Ncp A B Na).
  Proof.
    unfold not.
    intros n Hnodeof HnoForge Hismpti.
    apply is_mpti_then_originates in Hismpti.
    specialize (HnoForge ($Na ⋅ $A ) Hismpti).
    inversion HnoForge as [x [Hintra Hterm]].
    specialize (bundle_intrastrand_prefix_closed C_is_bundle Hnodeof Hintra) as Hnodeof'.
    assert (In x (Nsubt C #(SK A B))) as Hin. { apply (Nsubtiff_inC_p C #(SK A B)). unfold p. split. easy. unfold uns_term. now rewrite Hterm. }
    assert ((Nsubt C #(SK A B)) <> nil) as Hnil. { unfold not. intros. rewrite H in Hin. now apply in_nil in Hin. }
    specialize (exists_minimal_bundle C_is_bundle Hnil) as [m [Hin' Hmin]].
    apply (minimal_then_originates C_is_bundle #(SK A B) Hin') in Hmin.
    apply (Nsubtiff_inC_p C #(SK A B)) in Hin' as [Hin'' _].
    now specialize (SK_AB_never_originates C_is_SA_bundle Hin'') as Hcontra.
  Qed.

  (** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

  (* ============================================================ *)
  (** ** Non-injective agreement *)
  #[local] Hint Unfold Ncp uns term uns_term : core.

  Lemma Ncp_dec : forall t, { Ncp A B Na t } + { ~ Ncp A B Na t }.
  Proof.
    intros t;
    destruct (A_subterm_dec (⟨ $Na ⋅ $A ⟩_(SK A B)) t);
    (try now right); (try now left).
  Qed.

  Definition Nc := N (Ncp A B Na) C Ncp_dec.
  Definition Nc_iff_inC_Ncp := N_iff_inC_p (Ncp A B Na) C Ncp_dec.
  Definition minimal_Nc_then_mpt := minimal_N_then_mpt (Ncp A B Na) C_is_bundle Ncp_dec.
  Definition minimal_Nc_then_is_mpti := minimal_N_then_is_mpti (Ncp A B Na) C_is_bundle Ncp_dec.

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
    specialize (C_is_SA_bundle m HinC) as His_SA.
    inversion His_SA as [s' Hpen|s' A' B' Na' Hini|s' A' B' Na' Hres].

    (** _Penetrator case_ *)
    - inversion Hpen as [s'' Hmaximal].
      set (α := tr (strand m));
      assert (α = tr (strand m)) as H1 by easy.
      specialize (Hmaximal m). st_implication Hmaximal.
      specialize (minimal_Nc_then_is_mpti H1 Hin Hmin) as Hmpti.
      apply (NoForgeCipher_not_is_mpti HinC) in Hand0.
      now subst.

    (** _Initiator case_ *)
    - inversion Hini as [j Htrace].
      apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti.

    (** _Responder case_: *)
    - inversion Hres as [j Htrace].
      apply (f_equal tr) in Htrace.
      specialize (minimal_Nc_then_mpt Htrace Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      simplify_prop in Hmpti; try rewrite Hand2.
      all: exists (strand m); split; auto;
      specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof;
      st_implication Hsof.
  Qed.

  (* ============================================================ *)
  (** ** Injective agreement   *)

  Proposition injectivity :
  forall U U',
      uniquely_originates $Na ->
      forall s' : Σ,
        SA_initiator_strand U U' Na s' ->
        s' = s.
  Proof.
    intros U U' Huorig s' Hini'.
    inversion Hini' as [Htrace'].
    specialize s_is_SA_init as Hini.
    inversion Hini as [Htrace].
    inversion Huorig as [? [_ Horigx]].
    assert (Horigx' := Horigx).
    specialize (mpti_then_originates $Na (s,0)) as Horig.
    specialize (mpti_then_originates $Na (s',0)) as Horig'.
    pose (s0:=s); pose (s'0:=s').
    simplify_term_in Horig; st_implication Horig.
    simplify_term_in Horig'; st_implication Horig'.
    specialize (Horigx' (s'0, 0) Horig'); specialize (Horigx (s0,0) Horig); subst.
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
    split.
    - now apply noninjective_agreement.
    - now apply injectivity.
  Qed.

End SimpleAuthSecurity.
