Require Import Lia.

Require Import Strands.
Require Import LogicalFacts.

(* StrandsTactics depends on actual Terms *)
Require Import UTerms.
Require Import UTermsTactics.

Module StrandsTactics
  (Import U : UniverseSig)
  (Import T : UTermSig U)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St).

  Module Import TT := UTermsTactics U T.

  (* A simple tactic to reduce hypotheses/goals including term/uns_term and the like *)
  Ltac simplify_term :=
    unfold uns_term, uns, term; simpl; try easy;
    match goal with
    | [ H : ?X = tr ?Y |- context [tr ?Y] ] =>
      repeat rewrite <-H;
      simplify_term
    | [ H : index ?X = ?Y |- context [index ?X] ] =>
      repeat rewrite H;
      simplify_term
    | _ => auto; idtac
    end.

Ltac simplify_term_in H :=
  unfold uns_term, uns, term in H; simpl in H; try easy;
  match type of H with
  | context [tr ?Y] =>
    (match goal with
    | [ H1 : ?X = tr Y |- _ ] =>
      repeat rewrite <-H1 in H
    | _ => fail "no trace"
    end);
    simplify_term_in H
  | context [index ?Y] =>
    (match goal with
    | [ H1 : index Y = ?Z |- _ ] =>
      repeat rewrite H1 in H
    | _ => fail "no index"
    end);
    simplify_term_in H
  | _ => auto; idtac
end.

Lemma or_False_l:
  forall P, False \/ P <-> P.
Proof. split. intro. destruct H; easy. intro. now right. Qed.

Lemma or_False_r:
  forall P, P \/ False <-> P.
Proof. split. intro. destruct H; easy. intro. now left. Qed.

Lemma or_True_l:
  forall P, True \/ P <-> True.
Proof. split. intro. destruct H; easy. intro. now left. Qed.

Lemma or_True_r:
  forall P, P \/ True <-> True.
Proof. split. intro. destruct H; easy. intro. now right. Qed.

Lemma and_True_l:
  forall P, True /\ P <-> P.
Proof. split. intro. destruct H; easy. intro. split; easy. Qed.

Lemma and_True_r:
  forall P, P /\ True <-> P.
Proof. split. intro. destruct H; easy. intro. split; easy. Qed.

Lemma and_False_l:
  forall P, False /\ P <-> False.
Proof. split. intro. destruct H; easy. intro. split; easy. Qed.

Lemma and_False_r:
  forall P, P /\ False <-> False.
Proof. split. intro. destruct H; easy. intro. split; easy. Qed.

Lemma explosion:
  forall P : Prop, (False -> P) <-> True.
Proof. easy. Qed.

Lemma false_implication:
  (True -> False) <-> False.
Proof. easy. Qed.

Lemma notTrue:
  ~True <-> False.
Proof. easy. Qed.

Lemma notFalse:
  ~False <-> True.
Proof. easy. Qed.


(** Note this tactic depends on [TermTactic X Y in H] which is term dependent and is defined in [Terms.v]. In case terms are modified it is only required to adapt that part of the tactics.*)
Ltac simplify_prop_inner H dec :=
  simpl in H;
  unfold not in H;
  (* autorewrite is much slower we go by explicit cases *)
  repeat (
    (* idtac "Repetition" H;   *)
    match dec with
    | True =>
        push not in H using Terms_decidability;
        remove implications in H using Terms_decidability
        (* idtac "here" H *)
    | _ => idtac
    end;
    (* dec H; *)
    match type of H with
    | context [?X = ?X]  =>
      let H1 := fresh "Hassert" in
        (* idtac "equality" X H; *)
        assert (X = X <-> True) as H1 by ( clear; easy );
        rewrite H1 in H;
        clear H1
    | context [?X = ?Y]  =>
      (* idtac "123: inequality" X Y H; *)
      TermTactic X Y in H
      (* idtac "125: returned term" X Y H *)
    | True => clear H
    | False => contradiction
    | context [False \/ ?X]  =>
      rewrite or_False_l in H
    | context [?X \/ False]  =>
      rewrite or_False_r in H
    | context [True \/ ?X]  =>
      rewrite or_True_l in H
    | context [?X \/ True]  =>
      rewrite or_True_r in H
    | context [True /\ ?X]  =>
      rewrite and_True_l in H
    | context [?X /\ True]  =>
      rewrite and_True_r in H
    | context [False /\ ?X]  =>
      rewrite and_False_l in H
    | context [?X /\ False]  =>
      rewrite and_False_r in H
    | context [False -> ?X]  =>
      rewrite explosion in H
    | context [True -> False]  =>
      rewrite false_implication in H
    | context [~True]  =>
      rewrite notTrue in H
    | context [~False]  =>
      rewrite notFalse in H
    | ?X /\ ?Y =>
      let H1 := fresh "Hand" in
      let H2 := fresh "Hand" in
        destruct H as [H1 H2];
        simplify_prop_inner H1 dec;
        simplify_prop_inner H2 dec
    | ?X \/ ?Y =>
      let H1 := fresh "Hor" in
        destruct H as [H1|H1];
        simplify_prop_inner H1 dec
    | (?X -> False) -> False =>
      (* idtac "double not 1" X;  *)
      try (apply H; clear H; intros H)+(destruct H; intros H; tauto)
      (* let H1 := fresh "Hnot" in
        apply H; intros H1; simplify_prop_inner H1 *)
    | _ => idtac
    end
  ).

Tactic Notation "simplify_prop" "in" ident(H) "using" "decidability" :=
    simplify_prop_inner H True;
    subst;
    try easy; (* solve with easy *)
    try auto. (* solve with auto *)

Tactic Notation "simplify_prop" "in" ident(H) :=
  (* idtac "simplify_prop in " H; *)
  simplify_prop_inner H False;
  subst;
  try easy; (* solve with easy *)
  try auto. (* solve with auto *)

Tactic Notation "simplify_prop" "in" "*" "|-" :=
  repeat (
    (* idtac "Repetition"; *)
    match goal with
    | H : _ |- _  =>
      progress simplify_prop in H
    end
  ).

  Tactic Notation "simplify_prop" "in" "|-" "*" :=
    simpl;
    unfold not;
    repeat (
      (* idtac "Repetition"; *)
      match goal with
      | |- context [?X = ?X] =>
        let H1 := fresh "Hassert" in
          (* idtac "equality" X H; *)
          assert (X = X <-> True) as H1 by ( clear; easy );
          rewrite H1;
          clear H1
      | |- context [?X = ?Y] =>
        (* idtac "inequality" X Y H; *)
        TermTactic X Y
      | |- context [False \/ ?X] =>
        rewrite or_False_l
      | |- context [?X \/ False] =>
        rewrite or_False_r
      | |- context [True \/ ?X] =>
        rewrite or_True_l
      | |- context [?X \/ True] =>
        rewrite or_True_r
      | |- context [True /\ ?X] =>
        rewrite and_True_l
      | |- context [?X /\ True] =>
        rewrite and_True_r
      | |- context [False /\ ?X] =>
        rewrite and_False_l
      | |- context [?X /\ False] =>
        rewrite and_False_r
      | |- context [False -> ?X]  =>
        rewrite explosion
      | |- context [True -> False]  =>
        rewrite false_implication
      | |- context [~True]  =>
        rewrite notTrue
      | |- context [~False] =>
        rewrite notFalse
      | |- (?X -> False) =>
        let H1 := fresh "Hcontra" in
          intros H1;
          simplify_prop in H1
      end
    ).

Tactic Notation "simplify_prop" "in" "*" "|-" "*" :=
  simplify_prop in * |-;
  simplify_prop in |- *.

Ltac st_implication H :=
  simplify_prop in H;
  (* since simplify_prop can destruct H we need to use 'try' *)
  try (match type of H with
  | ?X -> ?Y =>
    let H1 := fresh "Hassert" in
    (* idtac "implication" H1 X Y; *)
    try (assert (X) as H1 by (
      solve [easy | lia | (simplify_term; try easy; try lia) | intuition]
    );
    specialize (H H1);
    clear H1;
    st_implication H)
  | _ => idtac
  end).
End StrandsTactics.
