From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Require Import SimpleAuthMaximalEnc.
Require Import SimpleAuthMaximalEncWithB.

Set Implicit Arguments.

Section CompositionSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  We consider the composition of the SimpleAuth protocol and its variant with [B] in place of [A], under maximal attacker.

  ** NOTE: This is the variant of [SimpleAuthMaximalEnc.v] that includes [B] instead of [A] in the ciphertext. The proofs are identical. We only needed to adapt the definition of [Ncp] and replace
  [specialize (HnoForge ($Na ⋅ $A ) Hismpti).] with [specialize (HnoForge ($Na ⋅ $B ) Hismpti).] at line 156.
  [destruct (A_subterm_dec (⟨ $Na ⋅ $A ⟩_(SK A B)) t);] with [destruct (A_subterm_dec (⟨ $Na ⋅ $B ⟩_(SK A B)) t);] at line 177.
  [try rewrite Hand2.] with [try rewrite Hand1.] at line 234.

  [[
  A -> B :  A ⋅ B ⋅ Na
  B -> A :  ⟨ Na ⋅ A ⟩_(SK A B)
  ]]

  with

  [[
  A -> B :  A ⋅ B ⋅ Na
  B -> A :  ⟨ Na ⋅ B ⟩_(SK A B)
  ]]
  *)

  (* ============================================================ *)
  (** * Protocol Specification  *)

  (*
    We just compose the strands of the two protocols together
    p1 and p2 are predicates that we use to enforce key separation and achieve compositionality
    thanks to the maximal penetrator.
  *)

  Inductive SA_StrandSpace (p1 : T -> T-> Prop) (p2 : T -> T-> Prop) (A' B' : T) : Σ -> Prop :=
    | SASS_Pen  : forall s, SA_maximal_penetrator_strand A' B' s -> SA_StrandSpace p1 p2 A' B' s
    | SASS_Initc1 : forall A B Na s,
        p1 A B ->
        SimpleAuthMaximalEnc.SA_initiator_strand A B Na s ->
          SA_StrandSpace p1 p2 A' B' s
    | SASS_Respc1 : forall A B Na s,
        p1 A B ->
        SimpleAuthMaximalEnc.SA_responder_strand A B Na s ->
          SA_StrandSpace p1 p2 A' B' s
    | SASS_Initc2 : forall A B Na s,
        p2 A B ->
        SimpleAuthMaximalEncWithB.SA_initiator_strand A B Na s ->
          SA_StrandSpace p1 p2 A' B' s
    | SASS_Respc2 : forall A B Na s,
        p2 A B ->
        SimpleAuthMaximalEncWithB.SA_responder_strand A B Na s ->
          SA_StrandSpace p1 p2 A' B' s.

End CompositionSpec.
  (* ============================================================ *)

Section CompositionalSecurityProtocol1.
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : edge_set__t.

  Variable A B : T.
  Variable Na : T.

  (* We consider all possible participants for protocol 1 *)
  Definition p1_1 (A' B' : T) := True.
  (* We consider all possible participants except pairs [A' B'] matching with [A B] or [B A] for
     protocol 2. This ensures key-separation *)
  Definition p1_2 (A' B' : T) := ~((A = A' /\ B = B') \/ (A = B' /\ B = A')).

  Hypothesis s_is_SA_init : SimpleAuthMaximalEnc.SA_initiator_strand A B Na s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_SA_bundle : C_is_SS C (SA_StrandSpace p1_1 p1_2 A B).

  (** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

  (* ============================================================ *)
  (** ** Non-injective agreement *)

  (* The composition is the same as protocol 1. This results is due to the fact that the maximal
     penetrator is able to simulate protocol 2 *)
  Lemma comp_is_protocol1:
    C_is_SS C (SA_StrandSpace p1_1 p1_2 A B) ->
    C_is_SS C (SimpleAuthMaximalEnc.SA_StrandSpace A B).
  Proof.
    intros His_SS. unfold C_is_SS. intros n HinC.
    specialize (His_SS n HinC).
    inversion His_SS as [s' Hpen|A' B' Na' s' Hp1 Hini|A' B' Na' s' Hp1 Hres|A' B' Na' s' Hp1 Hini|A' B' Na' s' Hp1 Hres]; try now constructor.
    - now apply ((SASS_Init1 A B) A' B' Na').
    - now apply ((SASS_Resp1 A B) A' B' Na').
    - apply (SimpleAuthMaximalEncWithB.ini_penetrator A B) in Hini. try now constructor.
    - unfold p1_2 in Hp1. apply (SimpleAuthMaximalEncWithB.res_penetrator Hp1) in Hres. try now constructor.
  Qed.

  Proposition noninjective_agreement1 :
    exists s' : Σ,
      SimpleAuthMaximalEnc.SA_responder_strand A B Na s' /\
        is_strand_of s' C.
  Proof.
    apply comp_is_protocol1 in C_is_SA_bundle.
    now apply (SimpleAuthMaximalEnc.noninjective_agreement s_is_SA_init s_strand_of_C C_is_bundle).
  Qed.

  Corollary injective_agreement1 :
    uniquely_originates $Na ->
      (
        exists s' : Σ,
          SimpleAuthMaximalEnc.SA_responder_strand A B Na s' /\
          is_strand_of s' C
      )
      /\
      (
        forall s'' : Σ,
          SimpleAuthMaximalEnc.SA_initiator_strand A B Na s'' ->
          s'' = s
      ).
  Proof.
    split.
    - now apply noninjective_agreement1.
    - now apply (SimpleAuthMaximalEnc.injectivity (C:=C) (A:=A) (B:=B)).
  Qed.

End CompositionalSecurityProtocol1.

Section CompositionalSecurityProtocol2.
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : edge_set__t.

  Variable A B : T.
  Variable Na : T.

  (* just swap these *)
  (* We consider all possible participants for protocol 1 *)
  Definition p2_2 (A' B' : T) := True.
  (* We consider all possible participants except pairs [A' B'] matching with [A B] or [B A] for
     protocol 2. This ensures key-separation *)
  Definition p2_1 (A' B' : T) := ~((A = A' /\ B = B') \/ (A = B' /\ B = A')).

  Hypothesis s_is_SA_init : SimpleAuthMaximalEncWithB.SA_initiator_strand A B Na s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_SA_bundle : C_is_SS C (SA_StrandSpace p2_1 p2_2 A B).

  (** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

  (* ============================================================ *)
  (** ** Non-injective agreement *)

   (* The composition is the same as protocol 2. This results is due to the fact that the maximal
     penetrator is able to simulate protocol 1 *)
  Lemma comp_is_protocol2:
    C_is_SS C (SA_StrandSpace p2_1 p2_2 A B) ->
    C_is_SS C (SimpleAuthMaximalEncWithB.SA_StrandSpace A B).
  Proof.
    intros His_SS. unfold C_is_SS. intros n HinC.
    specialize (His_SS n HinC).
    inversion His_SS as [s' Hpen|A' B' Na' s' Hp1 Hini|A' B' Na' s' Hp1 Hres|A' B' Na' s' Hp1 Hini|A' B' Na' s' Hp1 Hres]; try now constructor.
    - apply (SimpleAuthMaximalEnc.ini_penetrator A B) in Hini. try now constructor.
    - unfold p2_2 in Hp1. apply (SimpleAuthMaximalEnc.res_penetrator Hp1) in Hres. try now constructor.
    - now apply ((SASS_Init2 A B) A' B' Na').
    - now apply ((SASS_Resp2 A B) A' B' Na').
  Qed.

  Proposition noninjective_agreement2 :
    exists s' : Σ,
      SimpleAuthMaximalEncWithB.SA_responder_strand A B Na s' /\
        is_strand_of s' C.
  Proof.
    apply comp_is_protocol2 in C_is_SA_bundle.
    now apply (SimpleAuthMaximalEncWithB.noninjective_agreement s_is_SA_init s_strand_of_C C_is_bundle).
  Qed.

Corollary injective_agreement :
    uniquely_originates $Na ->
      (
        exists s' : Σ,
          SimpleAuthMaximalEncWithB.SA_responder_strand A B Na s' /\
          is_strand_of s' C
      )
      /\
      (
        forall s'' : Σ,
          SimpleAuthMaximalEncWithB.SA_initiator_strand A B Na s'' ->
          s'' = s
      ).
  Proof.
    split.
    - now apply noninjective_agreement2.
    - now apply (SimpleAuthMaximalEncWithB.injectivity (C:=C) (A:=A) (B:=B)).
  Qed.

End CompositionalSecurityProtocol2.
