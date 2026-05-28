From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lists.ListSet.
(* From Stdlib Require Import Lists.SetoidList. *)
From Stdlib Require Import Relations.
From Stdlib Require Import Bool.
From Stdlib Require Import Logic.Decidable.
Import Stdlib.Lists.List.ListNotations.
Import Nat.

Require Import Universe.
Require Import UTerms.

Module UTermsTactics (U : UniverseSig) (Import UT : UTermSig U).

  Lemma A_T_iff :
    forall a b, $a = $b <-> a = b.
  Proof. split; intros; now inversion H. Qed.

  Lemma A_K_iff :
    forall a b, #a = #b <-> a = b.
  Proof. split; intros; now inversion H. Qed.

  Lemma PKerase :
    forall A B, PK A = PK B <-> A = B.
  Proof.
    intros A B. split; intros; subst; try easy. now apply (PK_injective) in H.
  Qed.

  Lemma SKerase :
    forall A B A' B',
      SK A B = SK A' B' <-> (A = A' /\ B = B') \/ (A = B' /\ B = A').
  Proof.
    intros A B A' B'. split; intros; subst; try easy.
    - now apply (SK_injective).
    - repeat destruct H; subst; try easy. now apply (SK_bidirectional).
  Qed.

  Lemma concat_iff:
    forall a b c d, a⋅b = c⋅d <-> a=c /\ b=d.
  Proof.
    intros. split; intros; subst; try easy. inversion H; easy. destruct H; subst; easy.
  Qed.

  Lemma cipher_iff:
    forall a a' k k', ⟨ a ⟩_ k = ⟨ a' ⟩_ k' <-> a = a' /\ k = k'.
  Proof.
    intros. split; intros; subst; try easy. inversion H; easy. destruct H; subst; easy.
  Qed.

  (* This tactic is term-dependent. It is invoked when X <> Y to deconstruct
  X and Y if possible or prove their inequality *)
  Ltac term_tactic_in X Y H :=
    (* idtac "UTermTactic" X Y H; *)
    match X with
    | #?Z => match Y with #?W => rewrite A_K_iff in H end (* keys K *)
    | $?Z => match Y with $?W => rewrite A_T_iff in H end (* texts T *)
    | PK ?Z => match Y with PK ?W => rewrite PKerase in H end (* public key identities *)
    | SK ?Z ?Z' => match Y with SK ?W ?W' => rewrite SKerase in H end (* symmetric key identities *)
    | ?Z ⋅ ?W => match Y with ?Z' ⋅ ?W' => rewrite concat_iff in H end
    | ⟨ ?Z ⟩_ ?W => match Y with ⟨ ?Z' ⟩_ ?W' => rewrite cipher_iff in H end
    | _ =>
      match type of X with
      | 𝔸 => (* Tries to prove inequality *)
          let H1 := fresh "Hassert" in
            (* idtac "proving inequality" X Y H; *)
            assert (X = Y <-> False) as H1 by ( clear; easy );
            rewrite H1 in H;
            clear H1
      (* | _ => idtac "term" X Y H *)
      end
    end.

  Tactic Notation "TermTactic" constr(X) constr(Y) "in" ident(H) :=
    term_tactic_in X Y H.

  Ltac term_tactic X Y :=
    (* idtac "termTactic" X Y; *)
    (* deconstructs *)
    match X with
    | #?Z => match Y with #?W => rewrite A_K_iff end (* keys K *)
    | $?Z => match Y with $?W => rewrite A_T_iff end (* texts T *)
    | PK ?Z => match Y with PK ?W => rewrite PKerase end (* public key identities T *)
    | SK ?Z ?Z' => match Y with SK ?W ?W' => rewrite SKerase end (* symmetric key identities *)
    | ?Z ⋅ ?W => match Y with ?Z' ⋅ ?W' => rewrite concat_iff end
    | ⟨ ?Z ⟩_ ?W => match Y with ⟨ ?Z' ⟩_ ?W' => rewrite cipher_iff end
    | _ =>
      match type of X with
      | 𝔸 => (* Tries to prove inequality *)
          let H1 := fresh "Hassert" in
            (* idtac "proving inequality" X Y; *)
            assert (X = Y <-> False) as H1 by ( clear; easy );
            rewrite H1;
            clear H1
      (* | _ => fail 1 *)
      end
    end.

  Tactic Notation "TermTactic" constr(X) constr(Y) :=
    term_tactic X Y.
End UTermsTactics.
