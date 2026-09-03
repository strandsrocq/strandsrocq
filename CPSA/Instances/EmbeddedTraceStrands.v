From strandsrocq.Common Require Import EmbeddedTraceStrandsFunctor.
From strandsrocq.Common Require Import UniverseNat.

From strandsrocq.CPSA.Instances Require Import UTerms.

Set Implicit Arguments.

Module TermNat := UTerm UniverseNat.
Module Export EmbeddedTraceInstance := MakeEmbeddedTraceStrandSpace TermNat.
