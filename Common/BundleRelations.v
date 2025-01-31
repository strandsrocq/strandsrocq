Require Import ListSet.
Require Import Coq.Lists.List Coq.Lists.ListSet Coq.Bool.Bool Coq.Bool.Sumbool.
Require Import Relations.
Require Import Relations.Relation_Operators.

Require Import Strands.

Import Coq.Lists.List.ListNotations.

Open Scope list_scope.

Set Implicit Arguments.

Module BundleRelations
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St).

  (*
    In this section, we define the ≺ and ⪯ among nodes, for any set of edges C.
    In particular, here we are not assuming that C is a bundle.

    Also, we *do not* need the definition of bundles here!
  *)

  (* ≺ relation: transitive closure of C *)
  Inductive bundle_lt (C:edge_set__t) : node__t -> node__t -> Prop :=
  | bundle_lt_one   : forall n n', set_In (n, n') C -> bundle_lt C n n'
  | bundle_lt_multi : forall n n'' n', bundle_lt C n n' -> bundle_lt C n' n'' -> bundle_lt C n n''.

  Notation "C '⊢' n1 '≺' n2" := (bundle_lt C n1 n2) (at level 70).

  (* ⪯ relation: transitive and reflexive closure of C *)
  Inductive bundle_le (C:edge_set__t) (n:node__t): node__t -> Prop :=
  | bundle_le_zero : bundle_le C n n
  | bundle_le_one (n':node__t) : set_In (n, n') C -> bundle_le C n n'
  | bundle_le_multi (n':node__t) : forall n'', bundle_le C n n'' ->  bundle_le C n'' n' -> bundle_le C n n'.

  Notation "C '⊢' n1 '⪯' n2" := (bundle_le C n1 n2) (at level 70).

  Lemma bundle_le_inv_empty :
    forall n1 n2,
      [] ⊢ n1 ⪯ n2 -> n1 = n2.
  Proof.
    intros n1 n2 Hle.
    induction Hle as [|n1 n2 H | n1 n2 n3 ? ? ? ?]; try easy.
    destruct (eq_node__t_dec n1 n3); try subst; easy.
  Qed.

  Lemma bundle_le_cons:
    forall e m1 m2 C,
      C ⊢ m1 ⪯ m2 -> (e :: C) ⊢ m1 ⪯ m2.
  Proof.
    intros e m1 m2 C Hecrt. induction Hecrt as [|n n' Hone|n n' n'' Hmulti1 IHmulti1 Hmulti2 IHmulti2].
    - apply bundle_le_zero.
    - specialize (in_cons e (n,n') C Hone) as Hinind. apply bundle_le_one. assumption.
    - apply (bundle_le_multi IHmulti1 IHmulti2).
  Qed.

  Lemma bundle_lt_cons:
    forall e m1 m2 C,
      C ⊢ m1 ≺ m2 -> (e :: C) ⊢ m1 ≺ m2.
  Proof.
    intros e m1 m2 C Hecrt. induction Hecrt as [n n' Hone|n n' n'' Hmulti1 IHmulti1 Hmulti2 IHmulti2].
    - specialize (in_cons e (n,n') C Hone) as Hinind. apply bundle_lt_one. assumption.
    - apply (bundle_lt_multi IHmulti1 IHmulti2).
  Qed.

  Lemma bundle_le_iff: forall m1 m2 n1 n2 C,
      (n1,n2)::C ⊢ m1 ⪯ m2 <->
       C ⊢ m1 ⪯ m2 \/
          (C ⊢ m1 ⪯ n1 /\ C ⊢ n2 ⪯ m2).
  Proof with (right; split; assumption).
    split.
    - intro Hecrt. induction Hecrt as [| | m1 m2 n'' Hmulti1 IH1 Hmulti2 IH2].
      + specialize (bundle_le_zero C n) as Hyes. left. assumption.
      + simpl in H. destruct H.
        * injection H as Heq1 Heq2. subst. right. split. all: apply (bundle_le_zero C _).
        * left. apply bundle_le_one. assumption.
      + destruct (eq_node__t_dec m1 n'') as [Heq1|Hneq1].
        all: destruct (eq_node__t_dec n'' m2) as [Heq2|Hneq2].
        -- (* m1 = n'' = m2 *) subst. left. apply bundle_le_zero.
        -- (* m1 = n'', n'' <> m2 *) subst. apply IH2.
        -- (* m1 <> n'', n'' = m2 *) subst. apply IH1.
        -- (* m1 <> n'', n'' <> m2 *)
          destruct IH1 as [IH1or | [IH1and1 IH1and2]].
          all: destruct IH2 as [IH2or | [IH2and1 IH2and2]].
          ++ left. apply (bundle_le_multi IH1or IH2or).
          ++ specialize (bundle_le_multi IH1or IH2and1) as IHw...
          ++ specialize (bundle_le_multi IH1and2 IH2or) as IHw...
          ++ trivial...
    - intros [Hor | [Hand1 Hand2]].
      + apply bundle_le_cons. assumption.
      + apply (bundle_le_cons (n1, n2)) in Hand1.
        apply (bundle_le_cons (n1, n2)) in Hand2.
        assert (bundle_le ((n1,n2) :: C) n1 n2) as Hin. { apply bundle_le_one. apply in_eq. }
        specialize (bundle_le_multi Hand1 Hin) as Hin2.
        apply (bundle_le_multi Hin2 Hand2).
  Qed.

  Lemma bundle_le_dec : forall C m1 m2, { C ⊢ m1 ⪯ m2 } + { ~ C ⊢ m1 ⪯ m2 }.
  Proof.
    intros C.
    induction C as [ | (n1, n2) C IHC].
    - (* Base case: C = [] *)
      intros m1 m2.
      destruct (eq_node__t_dec m1 m2).
      + left. subst. apply bundle_le_zero.
      + right. unfold not; intros Hle. now apply bundle_le_inv_empty in Hle.
    - (* Ind. case: C is of the form (n1, n2)::C *)
      intros m1 m2.
      destruct (IHC m1 m2) as [HindL | HindR].
      + left.
        apply bundle_le_cons. assumption.
      + specialize (bundle_le_iff m1 m2 n1 n2 C) as [Hl Hr].
        destruct (IHC n2 m2) as [Handeq2 | Handneq2].
        * destruct (IHC m1 n1) as [Handeq1 | Handneq1].
          -- left. apply Hr. right. split. all: assumption.
          -- right. intro Hcontra. specialize (Hl Hcontra) as [? | [? ?]]. all: contradiction.
        * right. intro Hcontra. specialize (Hl Hcontra) as [? | [? ?]]. all: contradiction.
  Qed.

  Lemma bundle_lt_then_le : forall C n1 n2, C ⊢ n1 ≺ n2 -> C ⊢ n1 ⪯ n2.
  Proof.
    intros C n1 n2 Hlt.
    induction Hlt.
    - apply bundle_le_one. assumption.
    - apply (bundle_le_multi IHHlt1 IHHlt2).
  Qed.

  Lemma bundle_le_then_lt :
    forall C n1 n2, C ⊢ n1 ⪯ n2 ->
      n1 = n2 \/ C ⊢ n1 ≺ n2.
  Proof.
    intros C n1 n2 Hlt.
    induction Hlt.
    - left. trivial.
    - right. apply bundle_lt_one. assumption.
    - destruct IHHlt1 as [Heq1 | Hect1]. all: destruct IHHlt2 as [Heq2 | Hect2].
      + subst. left. reflexivity.
      + subst. right. assumption.
      + subst. right. assumption.
      + right. apply (bundle_lt_multi Hect1 Hect2).
  Qed.

  Lemma bundle_le_refl :
    forall C, reflexive node__t (bundle_le C).
  Proof.
    intro C. unfold reflexive. intro x. apply bundle_le_zero.
  Qed.

  Lemma bundle_le_trans :
    forall C, transitive node__t (bundle_le C).
  Proof.
    unfold transitive.
    intros C n n' n'' Hlt1 Hlt2.
    apply (bundle_le_multi Hlt1 Hlt2).
  Qed.

End BundleRelations.


