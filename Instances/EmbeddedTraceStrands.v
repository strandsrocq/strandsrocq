Require Import EmbeddedTraceStrandsFunctor.
Require Import UniverseNat.

Require Import UTerms.

Set Implicit Arguments.

Module TermNat := UTerm UniverseNat.
Module Export EmbeddedTraceInstance := MakeEmbeddedTraceStrandSpace TermNat.
