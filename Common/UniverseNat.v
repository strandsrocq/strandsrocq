From Stdlib Require Import Arith.PeanoNat.

Require Import Universe.

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
  intros a b Hab Hba.
  apply Nat.le_antisymm; now apply Nat.leb_le.
Qed.
