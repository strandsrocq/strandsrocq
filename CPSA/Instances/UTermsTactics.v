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

From strandsrocq.Common Require Import Universe.
From strandsrocq.CPSA.Instances Require Import UTerms.

Module UTermsTactics (U : UniverseSig) (Import UT : UTermSig U).

  Lemma M_Name_iff :
    forall a b : Name, M_Name a =  M_Name b <-> a = b.
  Proof. split; intros; now inversion H. Qed.
  Lemma M_Text_iff :
    forall a b : Text, M_Text a =  M_Text b <-> a = b.
  Proof. split; intros; now inversion H. Qed.
  Lemma M_Data_iff :
    forall a b : Data, M_Data a =  M_Data b <-> a = b.
  Proof. split; intros; now inversion H. Qed.
  Lemma M_Tag_iff :
    forall a b : Tag, M_Tag a =  M_Tag b <-> a = b.
  Proof. split; intros; now inversion H. Qed.
  Lemma M_Skey_iff :
    forall a b : Skey, M_Skey a =  M_Skey b <-> a = b.
  Proof. split; intros; now inversion H. Qed.
  Lemma M_Akey_iff :
    forall a b : Akey, M_Akey a =  M_Akey b <-> a = b.
  Proof. split; intros; now inversion H. Qed.

  Lemma PKerase :
    forall A B, K A = K B <-> A = B.
  Proof.
    intros A B. split; intros; subst; try easy. now apply (PK_injective) in H.
  Qed.
  Lemma PKerase_s :
    forall A B t, Ks t A = Ks t B <-> A = B.
  Proof.
    intros A B. split; intros; subst; try easy. now apply (PK_injective_s) in H.
  Qed.  

  Lemma SKerase :
    forall A B A' B',
      Bltk A B = Bltk A' B' <-> (A = A' /\ B = B') \/ (A = B' /\ B = A').
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

  Lemma hash_iff:
    forall a a', # a = # a' <-> a = a'.
  Proof.
    intros. split; intros; subst; try easy. inversion H; easy.
  Qed.

  (* This tactic is term-dependent. It is invoked when X <> Y to deconstruct
  X and Y if possible or prove their inequality *)
  Ltac term_tactic_in X Y H :=
    (* idtac "UTermTactic" X Y H; *)
    match X with
    (* | Inv ?Z => match Y with Inv ?K => rewrite Inv_bijective in H end *)
    | M_Name ?Z => match Y with M_Name ?W => rewrite M_Name_iff in H end
    | M_Text ?Z => match Y with M_Text ?W => rewrite M_Text_iff in H end
    | M_Data ?Z => match Y with M_Data ?W => rewrite M_Data_iff in H end
    | M_Tag ?Z => match Y with M_Tag ?W => rewrite M_Tag_iff in H end
    | M_Skey ?Z => match Y with M_Skey ?W => rewrite M_Skey_iff in H end
    | M_Akey ?Z => match Y with M_Akey ?W => rewrite M_Akey_iff in H end
    | K ?Z => match Y with K ?W => rewrite PKerase in H end (* public key identities *)
    | Ks ?T ?Z => match Y with Ks ?T ?W => rewrite PKerase_s in H end (* public key identities *)
    | Bltk ?Z ?Z' => match Y with Bltk ?W ?W' => rewrite SKerase in H end (* symmetric key identities *)
    | ?Z ⋅ ?W => match Y with ?Z' ⋅ ?W' => rewrite concat_iff in H end
    | ⟨ ?Z ⟩_ ?W => match Y with ⟨ ?Z' ⟩_ ?W' => rewrite cipher_iff in H end
    | # ?Z => match Y with # ?Z' => rewrite hash_iff in H end
    | _ =>
      match type of X with
      | Mesg => (* Tries to prove inequality *)
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
    (* | Inv ?Z => match Y with Inv ?K => rewrite Inv_bijective end *)
    | M_Name ?Z => match Y with M_Name ?W => rewrite M_Name_iff end
    | M_Text ?Z => match Y with M_Text ?W => rewrite M_Text_iff end
    | M_Data ?Z => match Y with M_Data ?W => rewrite M_Data_iff end
    | M_Tag ?Z => match Y with M_Tag ?W => rewrite M_Tag_iff end
    | M_Skey ?Z => match Y with M_Skey ?W => rewrite M_Skey_iff end
    | M_Akey ?Z => match Y with M_Akey ?W => rewrite M_Akey_iff end
    | K ?Z => match Y with K ?W => rewrite PKerase end (* public key identities *)
    | Ks ?T ?Z => match Y with Ks ?T ?W => rewrite PKerase_s end (* public key identities *)
    | Bltk ?Z ?Z' => match Y with Bltk ?W ?W' => rewrite SKerase end (* symmetric key identities *)
    | ?Z ⋅ ?W => match Y with ?Z' ⋅ ?W' => rewrite concat_iff end
    | ⟨ ?Z ⟩_ ?W => match Y with ⟨ ?Z' ⟩_ ?W' => rewrite cipher_iff end
    | # ?Z => match Y with # ?Z' => rewrite hash_iff end
    | _ =>
      match type of X with
      | Mesg => (* Tries to prove inequality *)
          let H1 := fresh "Hassert" in
            (* idtac "proving inequality" X Y H; *)
            assert (X = Y <-> False) as H1 by ( clear; easy );
            rewrite H1;
            clear H1
      (* | _ => idtac "term" X Y H *)
      end
    end.

  Tactic Notation "TermTactic" constr(X) constr(Y) :=
    term_tactic X Y.
End UTermsTactics.
