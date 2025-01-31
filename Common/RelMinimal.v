
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.
Require Import Relations.

Set Implicit Arguments.

Section RelMinimal.
  (* First a few variables and hypotheses *)
  Variable A : Set.
  Variable R : A -> A -> Prop.

  Hypothesis eq_dec : forall x y : A, { x=y } + { ~x=y }.
  Hypothesis R_dec : forall x y : A, { R x y } + { ~R x y }.

  Hypothesis R_antisymmetric: antisymmetric A R.
  Hypothesis R_transitive: transitive A R.

  Notation "n1 '⊑' n2" := (R n1 n2) (at level 60).

  Fixpoint minimal (N : set A) : option A :=
    match N with
    | [] => None
    | n' :: N' => match minimal N' with
                | None => Some n'
                | Some m' => if R_dec n' m' then Some n' else Some m'
                end
    end.

  (* mininal N is an element of N *)
  Lemma minimal_in_N: forall N' m, minimal N' = Some m -> set_In m N'.
  Proof.
    induction N' as [| n N'' IHn].
    - discriminate.
    - intros m Hsome. unfold minimal in Hsome; fold minimal in Hsome.
      destruct (minimal N'') as [m'|].
      + destruct (R_dec n m').
        * injection Hsome as Hsome'. subst. apply in_eq.
        * specialize (IHn m Hsome). apply in_cons. apply IHn.
      + injection Hsome as Hsome'. subst. apply in_eq.
  Qed.

  Lemma no_minimal_nil: forall N, minimal N = None <-> N = nil.
  Proof.
    intro N. destruct N.
    all:  try split; trivial;
      unfold minimal; fold minimal;
      destruct (minimal N); try destruct (R_dec a a0);
      discriminate.
  Qed.

  Definition is_minimal m N :=
    set_In m N -> forall n, set_In n N -> n<>m -> not (n ⊑ m).

  Lemma m_is_minimal : forall N m, minimal N = Some m -> is_minimal m N.
  Proof.
    (* intros m Hsome.  *)
    induction N as [|n' N' IH].
    - (* base case is trivial *) discriminate.
    - intros m Hsome Hin n Hinbis Hneq. (* inductive case *)
      specialize (in_inv Hinbis) as Hinind.
      unfold minimal in Hsome; fold minimal in Hsome.
      destruct (minimal N') as [m'|] eqn:HminimalN'.
      + (* minimal N' is Some m' *)
        destruct (R_dec n' m') as [Hmin|Hnomin].
        all: injection Hsome as Heq. all: subst.
        * (* n' ⊑ m', n' is the new minimal *)
          destruct Hinind as [?|Hin2]; auto.
          unfold is_minimal in IH.
          assert (Some m' = Some m') as Hm by reflexivity.
          specialize (IH m' Hm).
          specialize (minimal_in_N _ HminimalN') as Hinm.
          specialize (IH Hinm n Hin2).
          (* assert (Some m' = Some m') as H by reflexivity; specialize (Hin H). *)
          destruct (eq_dec n m') as [He|Hd].
          -- (* n = m' *) subst. intro Hcontra.
             (* use antisymmetric *)
             specialize (R_antisymmetric Hmin Hcontra). auto.
          -- (* n <> m' *) specialize (IH Hd). intro Hcontra.
             (* use transitive *)
             specialize (R_transitive Hcontra Hmin). auto.
        * (* ~ n' ⊑ m, m is still the minimal element *)
          assert (Some m = Some m) as Hm by reflexivity.
          specialize (minimal_in_N _ HminimalN') as Hinm.
          specialize (IH m Hm). unfold is_minimal in IH.
          specialize (IH Hinm n).
          destruct Hinind. all: subst;auto.
      + (* minimal N' is None *)
        apply no_minimal_nil in HminimalN'; subst.
        injection Hsome as Heq.
        destruct Hinind; subst.
        all: auto.
  Qed.

  Lemma exists_minimal: forall N, N <> nil -> exists m, set_In m N /\ is_minimal m N.
  Proof.
    intros N Hneq.
    specialize (no_minimal_nil N) as [Hnil _].
    destruct (minimal N) as [m|] eqn:Hmin.
    - exists m. split.
      + apply (minimal_in_N _ Hmin).
      + apply (m_is_minimal _ Hmin).
    - specialize (Hnil (eq_refl (A:=option A) None)). contradiction.
  Qed.
End RelMinimal.
