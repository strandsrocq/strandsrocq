From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

Require Import SimpleAuthMaximalEnc.
Require Import SimpleAuthMaximalEncWithB.

Set Implicit Arguments.

Section CompositionSpec.
  (** * Example: A Simple Unilateral Authentication Protocol

  We consider the composition of the SimpleAuth protocol of [SimpleAuthMaximalEnc.v] and its variant with [B] in place of [A] of [SimpleAuthMaximalEncWithB.v], under maximal attacker.

  NOTE: The guarantees of each protocol carry over to the composition when the other protocol never runs between the target pair [A B], in either direction. The proofs reduce the composition to the single protocol, since the maximal penetrator simulates the strands of the other one ([ini_penetrator], [res_penetrator]).

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

(** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

Section CompositionalSecurityProtocol1.
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : bundle_type.

  Variable A B : T.
  Variable Na : T.

  (* We consider all possible participants for protocol 1 *)
  Definition p1_1 (A' B' : T) := True.
  (* We consider all possible participants except pairs [A' B'] matching with [A B] or [B A] for
     protocol 2. This ensures key-separation *)
  Definition p1_2 (A' B' : T) := ~((A = A' /\ B = B') \/ (A = B' /\ B = A')).

  Hypothesis s_is_SA_init : SimpleAuthMaximalEnc.SA_initiator_strand A B Na s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_SA_bundle : strandspace_bundle C (SA_StrandSpace p1_1 p1_2 A B).

  (* Some facts, for easier use of C_is_SA_bundle *)
  Proposition C_is_bundle : is_bundle C.
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  Proposition C_is_SA :
    bundle_in_SS C (SA_StrandSpace p1_1 p1_2 A B).
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  (* ============================================================ *)
  (** ** Non-injective agreement *)

  (* The composition is the same as protocol 1. This results is due to the fact that the maximal
     penetrator is able to simulate protocol 2 *)
  Lemma comp_is_protocol1:
    strandspace_bundle C (SimpleAuthMaximalEnc.SA_StrandSpace A B).
  Proof.
    unfold strandspace_bundle. split. apply C_is_bundle.
    unfold bundle_in_SS. intros n HinC.
    specialize (C_is_SA) as His_SS.
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
    specialize comp_is_protocol1 as Hprot1.
    now apply (SimpleAuthMaximalEnc.noninjective_agreement s_is_SA_init s_strand_of_C Hprot1).
  Qed.

  Corollary injective_agreement1 :
    originates_at_most_once_in C $Na ->
      (
        exists s' : Σ,
          SimpleAuthMaximalEnc.SA_responder_strand A B Na s' /\
          is_strand_of s' C
      )
      /\
      (
        forall s'' : Σ,
          is_strand_of s'' C ->
          SimpleAuthMaximalEnc.SA_initiator_strand A B Na s'' ->
          s'' = s
      ).
  Proof.
    split.
    - now apply noninjective_agreement1.
    - apply (SimpleAuthMaximalEnc.injectivity (C:=C) (A:=A) (B:=B)); try easy.
      now apply comp_is_protocol1.
  Qed.

End CompositionalSecurityProtocol1.

(** * Proof of Security
  We now prove unilateral authentication properties of the protocol from the initiator perspective.  *)

Section CompositionalSecurityProtocol2.
  (**
    Local assumptions to make the rest more easily readable.
  *)
  Variable s : Σ.
  Variable C : bundle_type.

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
  Hypothesis C_is_SA_bundle : strandspace_bundle C (SA_StrandSpace p2_1 p2_2 A B).

  (* Some facts, for easier use of C_is_SA_bundle *)
  Proposition C_is_bundle2 : is_bundle C.
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.

  Proposition C_is_SA2 :
    bundle_in_SS C (SA_StrandSpace p2_1 p2_2 A B).
  Proof. now unfold strandspace_bundle in C_is_SA_bundle. Qed.
    
  (* ============================================================ *)
  (** ** Non-injective agreement *)

   (* The composition is the same as protocol 2. This results is due to the fact that the maximal
     penetrator is able to simulate protocol 1 *)
  Lemma comp_is_protocol2:
    strandspace_bundle C (SimpleAuthMaximalEncWithB.SA_StrandSpace A B).
  Proof.
    unfold strandspace_bundle. split. apply C_is_bundle2.
    unfold bundle_in_SS. intros n HinC.
    specialize (C_is_SA2) as His_SS.
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
    specialize comp_is_protocol2 as Hprot2.
    now apply (SimpleAuthMaximalEncWithB.noninjective_agreement s_is_SA_init s_strand_of_C Hprot2).
  Qed.

Corollary injective_agreement :
    originates_at_most_once_in C $Na ->
      (
        exists s' : Σ,
          SimpleAuthMaximalEncWithB.SA_responder_strand A B Na s' /\
          is_strand_of s' C
      )
      /\
      (
        forall s'' : Σ,
          is_strand_of s'' C ->
          SimpleAuthMaximalEncWithB.SA_initiator_strand A B Na s'' ->
          s'' = s
      ).
  Proof.
    split.
    - now apply noninjective_agreement2.
    - apply (SimpleAuthMaximalEncWithB.injectivity (C:=C) (A:=A) (B:=B)) ; try easy.
      now apply comp_is_protocol2.
  Qed.

End CompositionalSecurityProtocol2.

Section CompositionalSanity.
  (** * Sanity check: one honest run of each protocol *)

  Notation A := (Text 0).
  Notation B := (Text 1).
  Notation Na := (Text 2).
  (* protocol 2 runs between [A] and another responder: [p1_2 A B] excludes only [A B] and [B A] *)
  Notation B2 := (Text 3).
  Notation Nb := (Text 4).

  Notation s_ini1 := (0, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  Notation s_res1 := (1, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  Notation s_ini2 := (2, [ ⊕ $A ⋅ $B2 ⋅ $Nb; ⊖ ⟨ $Nb ⋅ $B2 ⟩_(SK A B2) ]).
  Notation s_res2 := (3, [ ⊖ $A ⋅ $B2 ⋅ $Nb; ⊕ ⟨ $Nb ⋅ $B2 ⟩_(SK A B2) ]).

  (** One honest session of protocol 1 between [A] and [B], then one of protocol 2 between [A] and [B2], in reverse construction order. *)
  Definition C : bundle_type :=
    {|
      nodes := rev [
        (s_ini1,0); (s_res1,0); (s_res1,1); (s_ini1,1);
        (s_ini2,0); (s_res2,0); (s_res2,1); (s_ini2,1)
      ];
      intra := rev [
        ((s_res1,0),(s_res1,1)); ((s_ini1,0),(s_ini1,1));
        ((s_res2,0),(s_res2,1)); ((s_ini2,0),(s_ini2,1))
      ];
      inter := rev [
        ((s_ini1,0),(s_res1,0));   (* A -> B   : $A ⋅ $B ⋅ $Na           *)
        ((s_res1,1),(s_ini1,1));   (* B -> A   : ⟨ $Na ⋅ $A ⟩_(SK A B)   *)
        ((s_ini2,0),(s_res2,0));   (* A -> B2  : $A ⋅ $B2 ⋅ $Nb          *)
        ((s_res2,1),(s_ini2,1))    (* B2 -> A  : ⟨ $Nb ⋅ $B2 ⟩_(SK A B2)  *)
      ]
    |}.

  (** The four strands are legitimate roles of the two protocols. *)
  Lemma s_ini1_SA : SimpleAuthMaximalEnc.SA_initiator_strand A B Na s_ini1.
  Proof. solve_role. Qed.

  Lemma s_res1_SA : SimpleAuthMaximalEnc.SA_responder_strand A B Na s_res1.
  Proof. solve_role. Qed.

  Lemma s_ini2_SA : SimpleAuthMaximalEncWithB.SA_initiator_strand A B2 Nb s_ini2.
  Proof. solve_role. Qed.

  Lemma s_res2_SA : SimpleAuthMaximalEncWithB.SA_responder_strand A B2 Nb s_res2.
  Proof. solve_role. Qed.

  (** The participant predicates admit both sessions. *)
  Lemma p1_1_AB : p1_1 A B.
  Proof. exact I. Qed.

  Lemma p1_2_AB2 : p1_2 A B A B2.
  Proof. intros [[_ H]|[H _]]; discriminate. Qed.

  Lemma p2_2_AB2 : p2_2 A B2.
  Proof. exact I. Qed.

  Lemma p2_1_AB : p2_1 A B2 A B.
  Proof. intros [[_ H]|[H _]]; discriminate. Qed.

  #[local] Hint Constructors SA_StrandSpace : sanity.
  #[local] Hint Resolve s_ini1_SA s_res1_SA s_ini2_SA s_res2_SA : sanity.
  #[local] Hint Resolve p1_1_AB p1_2_AB2 p2_2_AB2 p2_1_AB : sanity.

  (** [C] is a bundle and every strand of [C] belongs to the composed strand space. *)
  Lemma C_is_strandspace_bundle:
    strandspace_bundle C (SA_StrandSpace p1_1 (p1_2 A B) A B).
  Proof. solve_strandspace_bundle. Qed.

  (** [s_ini1] is a strand of [C]. *)
  Lemma s_ini1_strand_C : is_strand_of s_ini1 C.
  Proof. solve_is_strand_of. Qed.

  (** [Na] is originated at most once (in fact exactly once in [s_ini1]). *)
  Lemma C_Na_at_most_once : originates_at_most_once_in C $Na.
  Proof. solve_at_most_once_in. Qed.

  (** The hypotheses of [injective_agreement1] hold at once, so the guarantee is not vacuous. *)
  Lemma injective_agreement1_sanity :
    (
      exists s' : Σ,
        SimpleAuthMaximalEnc.SA_responder_strand A B Na s' /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        is_strand_of s'' C ->
        SimpleAuthMaximalEnc.SA_initiator_strand A B Na s'' ->
        s'' = s_ini1
    ).
  Proof.
    exact (
      injective_agreement1
        s_ini1_SA
        s_ini1_strand_C
        C_is_strandspace_bundle
        C_Na_at_most_once
      ).
  Qed.

  (** The same [C] seen from protocol 2: the target pair is [A B2], and the protocol 1 session is admitted by [p2_1 A B2]. *)
  Lemma C_is_strandspace_bundle2:
    strandspace_bundle C (SA_StrandSpace (p2_1 A B2) p2_2 A B2).
  Proof. solve_strandspace_bundle. Qed.

  (** [s_ini2] is a strand of [C]. *)
  Lemma s_ini2_strand_C : is_strand_of s_ini2 C.
  Proof. solve_is_strand_of. Qed.

  (** [Nb] is originated at most once (in fact exactly once in [s_ini2]). *)
  Lemma C_Nb_at_most_once : originates_at_most_once_in C $Nb.
  Proof. solve_at_most_once_in. Qed.

  (** The hypotheses of [injective_agreement] hold at once, so the guarantee is not vacuous. *)
  Lemma injective_agreement2_sanity :
    (
      exists s' : Σ,
        SimpleAuthMaximalEncWithB.SA_responder_strand A B2 Nb s' /\
        is_strand_of s' C
    )
    /\
    (
      forall s'' : Σ,
        is_strand_of s'' C ->
        SimpleAuthMaximalEncWithB.SA_initiator_strand A B2 Nb s'' ->
        s'' = s_ini2
    ).
  Proof.
    exact (
      injective_agreement
        s_ini2_SA
        s_ini2_strand_C
        C_is_strandspace_bundle2
        C_Nb_at_most_once
      ).
  Qed.

End CompositionalSanity.

Section CompositionalReflection.
  (** * Sanity check: a reflection attack without key separation
    We exhibit the reflection attack that key separation rules out: without it, protocol 2 can run between [A] and [B], and the penetrator uses [A] as a protocol 2 responder to answer its own protocol 1 challenge.  No strand of [B] occurs in the bundle at all.
  *)

  Notation A  := (Text 0).
  Notation B  := (Text 1).
  Notation Na := (Text 2).

  Notation s_ini  := (0, [ ⊕ $A ⋅ $B ⋅ $Na; ⊖ ⟨ $Na ⋅ $A ⟩_(SK A B) ]).
  (* [A] again, as protocol 2 responder to a request it believes comes from [B] *)
  Notation s_res  := (1, [ ⊖ $B ⋅ $A ⋅ $Na; ⊕ ⟨ $Na ⋅ $A ⟩_(SK B A) ]).
  (* the penetrator only reorders the names, which needs no key *)
  Notation s_sep1 := (2, [ ⊖ $A ⋅ $B ⋅ $Na; ⊕ $A ⋅ $B; ⊕ $Na ]).
  Notation s_sep2 := (3, [ ⊖ $A ⋅ $B; ⊕ $A; ⊕ $B ]).
  Notation s_cat1 := (4, [ ⊖ $B; ⊖ $A; ⊕ $B ⋅ $A ]).
  Notation s_cat2 := (5, [ ⊖ $B ⋅ $A; ⊖ $Na; ⊕ $B ⋅ $A ⋅ $Na ]).

  Definition C' : bundle_type :=
    {|
      nodes := rev [
        (s_ini,0);
        (s_sep1,0); (s_sep1,1); (s_sep1,2);
        (s_sep2,0); (s_sep2,1); (s_sep2,2);
        (s_cat1,0); (s_cat1,1); (s_cat1,2);
        (s_cat2,0); (s_cat2,1); (s_cat2,2);
        (s_res,0);  (s_res,1);
        (s_ini,1)
      ];
      intra := rev [
        ((s_sep1,0),(s_sep1,1)); ((s_sep1,1),(s_sep1,2));
        ((s_sep2,0),(s_sep2,1)); ((s_sep2,1),(s_sep2,2));
        ((s_cat1,0),(s_cat1,1)); ((s_cat1,1),(s_cat1,2));
        ((s_cat2,0),(s_cat2,1)); ((s_cat2,1),(s_cat2,2));
        ((s_res,0),(s_res,1));
        ((s_ini,0),(s_ini,1))
        ];
      inter := rev [
        ((s_ini,0),(s_sep1,0));   (* A -> P : $A ⋅ $B ⋅ $Na           *)
        ((s_sep1,1),(s_sep2,0));  (* P -> P : $A ⋅ $B                 *)
        ((s_sep2,2),(s_cat1,0));  (* P -> P : $B                      *)
        ((s_sep2,1),(s_cat1,1));  (* P -> P : $A                      *)
        ((s_cat1,2),(s_cat2,0));  (* P -> P : $B ⋅ $A                 *)
        ((s_sep1,2),(s_cat2,1));  (* P -> P : $Na                     *)
        ((s_cat2,2),(s_res,0));   (* P -> A : $B ⋅ $A ⋅ $Na           *)
        ((s_res,1),(s_ini,1))     (* A -> A : ⟨ $Na ⋅ $A ⟩_(SK A B)   *)
        ]
    |}.

  (** [A] plays the protocol 1 initiator towards [B] and the protocol 2 responder for [B]. *)
  Lemma s_ini_SA : SimpleAuthMaximalEnc.SA_initiator_strand A B Na s_ini.
  Proof. solve_role. Qed.

  Lemma s_res_SA : SimpleAuthMaximalEncWithB.SA_responder_strand B A Na s_res.
  Proof. solve_role. Qed.

  (** No key separation: both protocols admit every pair of participants. *)
  Definition any_pair (A' B' : T) := True.

  Lemma any_pair_holds : forall A' B', any_pair A' B'.
  Proof. exact (fun _ _ => I). Qed.

  (** The Dolev-Yao strands of the penetrator are strands of the maximal one. *)
  Lemma DY_pen_is_maximal : forall s,
    penetrator_strand (SimpleAuthMaximalEnc.K__P_AB A B) s -> SA_maximal_penetrator_strand A B s.
  Proof. intros s Hs. exact (SimpleAuthMaximalEnc.DY_is_SA_maximal_penetrator Hs). Qed.

  #[local] Hint Constructors SA_StrandSpace penetrator_strand : sanity.
  #[local] Hint Resolve s_ini_SA s_res_SA DY_pen_is_maximal : sanity.
  #[local] Hint Resolve any_pair_holds : sanity.

  (** [C'] is a bundle of the composition without key separation. *)
  Lemma C'_is_strandspace_bundle :
    strandspace_bundle C' (SA_StrandSpace any_pair any_pair A B).
  Proof. solve_strandspace_bundle. Qed.

  Lemma s_ini_strand_C' : is_strand_of s_ini C'.
  Proof. solve_is_strand_of. Qed.

  (** The oracle step: what [A] answers in protocol 2 is what [A] waits for in protocol 1, since [SK B A = SK A B]. *)
  Lemma the_answer_is_the_challenge :
    uns_term (s_res, 1) = uns_term (s_ini, 1).
  Proof. reflexivity. Qed.

  (** And [B] is absent: no protocol 1 responder strand of [C'] has [B] answering [A]. *)
  Lemma no_responder_for_B :
    ~ (exists s, SimpleAuthMaximalEnc.SA_responder_strand A B Na s /\ is_strand_of s C').
  Proof. solve_no_strand. Qed.

  (** So key separation is what excludes [C']: with [p1_2 A B], [noninjective_agreement1] would give the missing responder. *)
  Lemma separation_excludes_C' :
    ~ strandspace_bundle C' (SA_StrandSpace p1_1 (p1_2 A B) A B).
  Proof.
    intro H. apply no_responder_for_B.
    exact (noninjective_agreement1 s_ini_SA s_ini_strand_C' H).
  Qed.

End CompositionalReflection.
