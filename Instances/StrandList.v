Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import String.
Import Coq.Lists.List.ListNotations.

(* From Common: *)
Require Import Strands.
Require Import Bundles.

(* These are Universe-based Terms *)
Require Import UTerms.

Set Implicit Arguments.

(* First, we define the Universe upon which we build Terms *)
Module UniverseNat <: UniverseSig.
  Definition U := nat.
  Definition U_leb := Nat.leb.
  Definition U_eq_dec := Nat.eq_dec.

  Lemma U_leb_total: forall a b, a <=? b = true \/ b <=? a = true.
  Proof.
    intros.
    specialize (Nat.le_ge_cases a b) as Htot.
    destruct Htot.
    - left; now apply (Nat.leb_le a b).
    - right; now apply (Nat.leb_le b a).
  Qed.

  Lemma U_leb_antisymmetric : forall a b, a <=? b = true -> b <=? a = true -> a = b.
  Proof.
    intros. apply (Nat.le_antisymm); now  apply (Compare_dec.leb_complete).
  Qed.
End UniverseNat.

Module TermNat := UTerm UniverseNat.

Module StrandList <: StrandSig TermNat.
  Import TermNat.

  Module ST := SignedTerms TermNat.
  Export ST.

  Definition Σ : Set := nat * list sT.
  Definition tr (s : Σ) := snd s.

  Lemma Σ_eq_dec : forall s s' : Σ, { s = s' } + { s <> s'}.
  Proof.
    repeat decide equality.
  Qed.
End StrandList.

Module StrandSpaceList := StrandSpace TermNat StrandList.
Export StrandSpaceList.
