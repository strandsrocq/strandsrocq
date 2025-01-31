Require Import Coq.Logic.Decidable.
Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.SetoidList.

(** Logical facts

This is a subset of [FSetLogicalFacs] module from [FSetDecide.v]
that we slightly adapted to our setting. 
*)

Tactic Notation "fold" "any" "not" "in" ident(H) :=
  repeat (
    match type of H with
    | context [?P -> False] =>
      fold (~ P) in H
    end).

Tactic Notation "fold" "any" "not" "in" "|-" "*" :=
repeat (
  match goal with
  | |- context [?P -> False] =>
    fold (~ P)
  end).

Ltac or_not_l_iff P Q tac :=
  (rewrite (or_not_l_iff_1 P Q) by tac) ||
  (rewrite (or_not_l_iff_2 P Q) by tac).

Ltac or_not_r_iff P Q tac :=
  (rewrite (or_not_r_iff_1 P Q) by tac) ||
  (rewrite (or_not_r_iff_2 P Q) by tac).

Ltac or_not_l_iff_in P Q H tac :=
  (rewrite (or_not_l_iff_1 P Q) in H by tac) ||
  (rewrite (or_not_l_iff_2 P Q) in H by tac).

Ltac or_not_r_iff_in P Q H tac :=
  (rewrite (or_not_r_iff_1 P Q) in H by tac) ||
  (rewrite (or_not_r_iff_2 P Q) in H by tac).

(* This was missing *)
Lemma explosion:
  forall P: Prop, (False -> P) <-> True.
Proof.
  easy.
Qed.

Tactic Notation "push" "not" "using" ident(db) :=
  let dec := solve_decidable using db in
  unfold not, iff;
  repeat (
    match goal with
    | |- context [True -> False] => rewrite not_true_iff
    | |- context [False -> ?P] => rewrite explosion
    (* | |- context [False -> False] => rewrite not_false_iff *)
    | |- context [(?P -> False) -> False] => rewrite (not_not_iff P) by dec
    | |- context [(?P -> False) -> (?Q -> False)] =>
        rewrite (contrapositive P Q) by dec
    | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
    | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
    | |- context [(?P -> False) -> ?Q] => rewrite (imp_not_l P Q) by dec
    | |- context [?P \/ ?Q -> False] => rewrite (not_or_iff P Q)
    | |- context [?P /\ ?Q -> False] => rewrite (not_and_iff P Q)
    | |- context [(?P -> ?Q) -> False] => rewrite (not_imp_iff P Q) by dec
    end);
  fold any not in |- *.

Tactic Notation "push" "not" :=
  push not using core.

Ltac reverse_or_not_l_iff_in P Q H tac :=
  (rewrite <-(or_not_l_iff_1 P Q) in H by tac) ||
  (rewrite <-(or_not_l_iff_2 P Q) in H by tac).

Tactic Notation
  "remove" "implications" "in" ident(H) "using" ident(db) :=
  let dec := solve_decidable using db in
  repeat (
    fold any not in H;
    match type of H with
    | context [?P -> ?Q] => reverse_or_not_l_iff_in P Q H dec
    end
  ).
  
Tactic Notation
  "push" "not" "in" ident(H) "using" ident(db) :=
  let dec := solve_decidable using db in
  unfold not, iff in H;
  repeat (
    match type of H with
    | context [True -> False] => rewrite not_true_iff in H
    (* | context [False -> False] => rewrite not_false_iff in H *)
    | context [False -> ?P] => rewrite explosion in H
    | context [(?P -> False) -> False] =>
      rewrite (not_not_iff P) in H by dec
    | context [(?P -> False) -> (?Q -> False)] =>
      rewrite (contrapositive P Q) in H by dec
    | context [(?P -> False) \/ ?Q] => or_not_l_iff_in P Q H dec
    | context [?P \/ (?Q -> False)] => or_not_r_iff_in P Q H dec
    | context [(?P -> False) -> ?Q] =>
      rewrite (imp_not_l P Q) in H by dec
    | context [?P \/ ?Q -> False] => rewrite (not_or_iff P Q) in H
    | context [?P /\ ?Q -> False] => rewrite (not_and_iff P Q) in H
    | context [(?P -> ?Q) -> False] =>
      rewrite (not_imp_iff P Q) in H by dec
    | context [?X = ?X] => assert (X = X <-> True) as Ha by (clear;easy);
      rewrite Ha in H;
      clear Ha
    | context [?X = ?Y] => assert (X = Y <-> False) as Ha by (clear;easy);
      rewrite Ha in H;
      clear Ha
      (* rewrite T_reflexive; *)
    end
  );
fold any not in H.

Tactic Notation
  "push" "not" "in" "*" "|-" "using" ident(db) :=
  repeat (
    match goal with
    | H : _ |- _  =>
      progress push not in H using db
    end
  ).

Tactic Notation "push" "not" "in" "*" "|-"  :=
  push not in * |- using core.

Tactic Notation "push" "not" "in" "*" "using" ident(db) :=
  push not using db; push not in * |- using db.
Tactic Notation "push" "not" "in" "*" :=
  push not in * using core.

(** A simple test case to see how this works.  *)
Lemma test_push : forall P Q R : Prop,
  decidable P ->
  decidable Q ->
  (~ True) ->
  (~ False) ->
  (~ ~ P) ->
  (~ (P /\ Q) -> ~ R) ->
  ((P /\ Q) \/ ~ R) ->
  (~ (P /\ Q) \/ R) ->
  (R \/ ~ (P /\ Q)) ->
  (~ R \/ (P /\ Q)) ->
  (~ P -> R) ->
  (~ ((R -> P) \/ (Q -> R))) ->
  (~ (P /\ R)) ->
  (~ (P -> R)) ->
  True.
Proof.
  intros. push not in *.
    (* note that ~(R->P) remains (since R isn't decidable) *)
  tauto.
Qed.

(** [pull not using db] will pull as many negations as
    possible toward the top of the propositions in the goal,
    using the lemmas in [db] to assist in checking the
    decidability of the propositions involved.  If [using
    db] is omitted, then [core] will be used.  Additional
    versions are provided to manipulate the hypotheses or
    the hypotheses and goal together. *)

Tactic Notation "pull" "not" "using" ident(db) :=
  let dec := solve_decidable using db in
  unfold not, iff;
  repeat (
    match goal with
    | |- context [True -> False] => rewrite not_true_iff
    | |- context [False -> False] => rewrite not_false_iff
    | |- context [(?P -> False) -> False] => rewrite (not_not_iff P) by dec
    | |- context [(?P -> False) -> (?Q -> False)] =>
      rewrite (contrapositive P Q) by dec
    | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
    | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
    | |- context [(?P -> False) -> ?Q] => rewrite (imp_not_l P Q) by dec
    | |- context [(?P -> False) /\ (?Q -> False)] =>
      rewrite <- (not_or_iff P Q)
    | |- context [?P -> ?Q -> False] => rewrite <- (not_and_iff P Q)
    | |- context [?P /\ (?Q -> False)] => rewrite <- (not_imp_iff P Q) by dec
    | |- context [(?Q -> False) /\ ?P] =>
      rewrite <- (not_imp_rev_iff P Q) by dec
    end);
  fold any not in |- *.

Tactic Notation "pull" "not" :=
  pull not using core.

Tactic Notation
  "pull" "not" "in" "*" "|-" "using" ident(db) :=
  let dec := solve_decidable using db in
  unfold not, iff in * |-;
  repeat (
    match goal with
    | H: context [True -> False] |- _ => rewrite not_true_iff in H
    | H: context [False -> False] |- _ => rewrite not_false_iff in H
    | H: context [(?P -> False) -> False] |- _ =>
      rewrite (not_not_iff P) in H by dec
    | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
      rewrite (contrapositive P Q) in H by dec
    | H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
    | H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
    | H: context [(?P -> False) -> ?Q] |- _ =>
      rewrite (imp_not_l P Q) in H by dec
    | H: context [(?P -> False) /\ (?Q -> False)] |- _ =>
      rewrite <- (not_or_iff P Q) in H
    | H: context [?P -> ?Q -> False] |- _ =>
      rewrite <- (not_and_iff P Q) in H
    | H: context [?P /\ (?Q -> False)] |- _ =>
      rewrite <- (not_imp_iff P Q) in H by dec
    | H: context [(?Q -> False) /\ ?P] |- _ =>
      rewrite <- (not_imp_rev_iff P Q) in H by dec
    end);
  fold any not in H.

Tactic Notation "pull" "not" "in" "*" "|-"  :=
  pull not in * |- using core.

Tactic Notation "pull" "not" "in" "*" "using" ident(db) :=
  pull not using db; pull not in * |- using db.
Tactic Notation "pull" "not" "in" "*" :=
  pull not in * using core.

(** A simple test case to see how this works.  *)
Lemma test_pull : forall P Q R : Prop,
  decidable P ->
  decidable Q ->
  (~ True) ->
  (~ False) ->
  (~ ~ P) ->
  (~ (P /\ Q) -> ~ R) ->
  ((P /\ Q) \/ ~ R) ->
  (~ (P /\ Q) \/ R) ->
  (R \/ ~ (P /\ Q)) ->
  (~ R \/ (P /\ Q)) ->
  (~ P -> R) ->
  (~ (R -> P) /\ ~ (Q -> R)) ->
  (~ P \/ ~ R) ->
  (P /\ ~ R) ->
  (~ R /\ P) ->
  True.
Proof.
  intros.
    (* push not in *.  *)
    pull not in *.
    push not in *. tauto.
Qed.

