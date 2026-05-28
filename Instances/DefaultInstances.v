Require Import EmbeddedTraceStrands.

Require Import UTermsTactics.

Require Import DefaultInstanceFunctor.

Module Export TermNatTactics := UTermsTactics UniverseNat TermNat.
Module Export DefaultInstance :=
  MakeDefaultInstance UniverseNat TermNat EmbeddedTraceStrands EmbeddedTraceStrandSpace TermNatTactics.
