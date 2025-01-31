Require Import StrandList.
Require Import StrandsTactics.
Require Import UTerms.

(* Create a concrete instance of Terms *)
Import TermNat.
Import StrandList.
Import StrandSpaceList.

Module Import StT := StrandsTactics UniverseNat TermNat StrandList StrandSpaceList.

Lemma test :
  forall (t t':T) (k k':K ) (a a' b b':𝔸),
  (t = t) ->
  (k = k) ->
  (a = a) ->
  ($t = $t /\ t = t) ->
  (t = t \/ t = t) ->
  (False -> t = t) ->
  (t = t') ->
  ($t = $t) ->
  ($t = $t' /\ t = t) ->
  (#k = #k) ->
  (#k = #k') ->
  (#k = $t) ->
  (#k <> $t) ->
  (PK t = PK t) ->
  (PK t = PK t') ->
  (a ⋅ a' = $t) ->
  (a ⋅ a' = b ⋅ b') ->
  (~~#k = $t) ->
  (#k <> $t) /\ (#k = #k') /\ (#k = $t) /\ (#k = #k).
Proof.
  intros.
  simplify_prop in |- *.
  simplify_prop in H16.
  (* simplify_prop in * |-. *)
Qed.
