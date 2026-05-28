From Stdlib Require Import Lists.List.

Require Import Strands.

Module MakeEmbeddedTraceStrands (Import T : TermSig) <: StrandSig T.
  Module ST := SignedTerms T.
  Export ST.

  Definition Σ : Set := nat * list sT.
  Definition tr (s : Σ) := snd s.

  Lemma Σ_eq_dec : forall s s' : Σ, { s = s' } + { s <> s'}.
  Proof.
    repeat decide equality.
  Qed.
End MakeEmbeddedTraceStrands.

Module MakeEmbeddedTraceStrandSpace (Import T : TermSig).
  Module EmbeddedTraceStrands := MakeEmbeddedTraceStrands T.
  Module EmbeddedTraceStrandSpace := StrandSpace T EmbeddedTraceStrands.
  Export EmbeddedTraceStrandSpace.
End MakeEmbeddedTraceStrandSpace.
