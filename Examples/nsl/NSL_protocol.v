From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import DefaultInstances.
Require Import Penetrator.

Set Implicit Arguments.

Section NSL.

  (** As in the original Strand Spaces paper, we assume that some elements of T are principals' names *)
  Variable Tname : T -> Prop.

  (* The strand space is now defined as follows *)
  Inductive NSL_initiator_strand (A B Na Nb : T) : Σ -> Prop :=
  | NSL_Init : forall i, Tname A /\ Tname B /\ ~ Tname Na ->
      NSL_initiator_strand A B Na Nb (i, [
          ⊕ ⟨ $Na ⋅ $A ⟩_(PK B);
          ⊖ ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A);
          ⊕ ⟨ $Nb ⟩_(PK B)
      ]).

  Inductive NSL_responder_strand (A B Na Nb : T) : Σ -> Prop :=
  | NSL_Resp : forall i, Tname A /\ Tname B /\ ~ Tname Nb ->
      NSL_responder_strand A B Na Nb (i, [
          ⊖ ⟨ $Na ⋅ $A ⟩_(PK B);
          ⊕ ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A);
          ⊖ ⟨ $Nb ⟩_(PK B)
          ]).

  (* NSL strandspace is parametrized over the penetrator keys [K__P]. It combines penetrator strands
     and initiator and responder strand, quantified over all possible participants and nonces *)
  Inductive NSL_StrandSpace (K__P : K -> Prop) : Σ -> Prop :=
    | NSLSS_Pen  : forall s, penetrator_strand K__P s -> NSL_StrandSpace K__P s
    | NSLSS_Init : forall (A B Na Nb: T) s, NSL_initiator_strand A B Na Nb s -> NSL_StrandSpace K__P s
    | NSLSS_Resp : forall (A B Na Nb: T) s, NSL_responder_strand A B Na Nb s -> NSL_StrandSpace K__P s.

  (* From the paper:
    "Note that given any strand s in Σ, we can uniquely classify it as a
    penetrator strand, an initiator's strand, or a respondent's strand
    just by the form of its trace."
  *)
  Variable A B Na Nb : T.
  Variable s : Σ.
  Variable K__P : K -> Prop.
  Variable C : edge_set__t.

  Lemma disjoint_regular_strands :
    ~ (NSL_initiator_strand A B Na Nb s /\ NSL_responder_strand A B Na Nb s).
  Proof.
    intros [Hi Hr].
    inversion Hi. inversion Hr. now subst.
  Qed.

  Lemma disjoint_regular_penetrator_strands :
    ~ ( (NSL_initiator_strand A B Na Nb s \/ NSL_responder_strand A B Na Nb s) /\ penetrator_strand K__P s).
  Proof.
    intros [[Hi|Hr] Hp].
    - inversion Hi. inversion Hp. all: try now subst.
    - inversion Hr. inversion Hp. all: try now subst.
  Qed.

  (* We also prove here general facts about private keys *)
  Lemma inv_PK_U_never_originates_regular :
    C_is_SS C (NSL_StrandSpace K__P) ->
      forall U, never_originates_regular K__P (inv (PK U)) C.
  Proof.
    intros His_NSL U n Hnodeof Horig.
    unfold not.
    unfold penetrator_node.
    specialize (His_NSL n Hnodeof).
    inversion His_NSL as [s0 Hpen|A0 B0 Na0 Nb0 s0 Hinires|A0 B0 Na0 Nb0 s0 Hinires]; try easy;
    inversion Hinires; apply (f_equal tr) in H0; simpl in H0;
    apply (originates_then_mpt H0) in Horig;
    unfold mpt in Horig; simpl in Horig;
    simplify_prop in Horig.
  Qed.

End NSL.

