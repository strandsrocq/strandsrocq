From strandsrocq.CPSA.Instances Require Import EmbeddedTraceStrands.

From strandsrocq.CPSA.Instances Require Import UTermsTactics.

From strandsrocq.Common Require Import DefaultInstanceFunctor.

Module Export TermNatTactics := UTermsTactics UniverseNat TermNat.
Module Export DefaultInstance :=
  MakeDefaultInstance UniverseNat TermNat EmbeddedTraceStrands EmbeddedTraceStrandSpace TermNatTactics.
