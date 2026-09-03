From Stdlib Require Import Lists.ListSet.
From Stdlib Require Import Lists.List Lists.ListSet.
(* Stdlib.Bool.Bool Stdlib.Bool.Sumbool. *)
From Stdlib Require Import Relations.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Sorting.Permutation.

Require Import Strands.

Import Stdlib.Lists.List.ListNotations.

Open Scope list_scope.

Set Implicit Arguments.

Module BundleRelations
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St).

  (*
    In this section, we define the ≺ and ⪯ among nodes, for any set of edges E.
    In particular, here we are not assuming that E are edges of a bundle_type.
    Thus, we *do not* need the definition of bundles here!
  *)

  (* ≺ relation: transitive closure of E *)
  Inductive bundle_lt (E : edge_set__t) : node__t -> node__t -> Prop :=
  | bundle_lt_one   : forall n n', set_In (n, n') E -> bundle_lt E n n'
  | bundle_lt_multi : forall n n'' n', bundle_lt E n n' -> bundle_lt E n' n'' -> bundle_lt E n n''.

  Notation "E '⊢' n1 '≺' n2" := (bundle_lt E n1 n2) (at level 70).

  (* ⪯ relation: transitive and reflexive closure of E *)
  Inductive bundle_le (E : edge_set__t) (n : node__t): node__t -> Prop :=
  | bundle_le_zero : bundle_le E n n
  | bundle_le_one (n':node__t) : set_In (n, n') E -> bundle_le E n n'
  | bundle_le_multi (n':node__t) : forall n'', bundle_le E n n'' ->  bundle_le E n'' n' -> bundle_le E n n'.

  Notation "E '⊢' n1 '⪯' n2" := (bundle_le E n1 n2) (at level 70).
    
  Lemma bundle_le_inv_empty :
    forall n1 n2,
      [] ⊢ n1 ⪯ n2 -> n1 = n2.
  Proof.
    intros n1 n2 Hle.
    induction Hle as [|n1 n2 H | n1 n2 n3 ? ? ? ?]; try easy.
    destruct (eq_node__t_dec n1 n3); try subst; easy.
  Qed.

  Lemma bundle_le_cons:
    forall e m1 m2 E,
      E ⊢ m1 ⪯ m2 -> (e :: E) ⊢ m1 ⪯ m2.
  Proof.
    intros e m1 m2 E Hecrt. induction Hecrt as [|n n' Hone|n n' n'' Hmulti1 IHmulti1 Hmulti2 IHmulti2].
    - apply bundle_le_zero.
    - specialize (in_cons e (n,n') E Hone) as Hinind. apply bundle_le_one. assumption.
    - apply (bundle_le_multi IHmulti1 IHmulti2).
  Qed.

  Lemma bundle_le_sub:
    forall m1 m2 E D,
    (forall x, set_In x E -> set_In x D) ->
    E ⊢ m1 ⪯ m2 -> D ⊢ m1 ⪯ m2.
  Proof.
    intros m1 m2 E D Hsub Hle.
    induction Hle; try now constructor.
    - apply bundle_le_one; now apply Hsub.
    - eapply bundle_le_multi. apply IHHle1. apply IHHle2.
  Qed.

  Lemma bundle_le_union:
    forall m1 m2 E D,
      D ⊢ m1 ⪯ m2 -> (set_union eq_edge__t_dec E D) ⊢ m1 ⪯ m2.
  Proof.
    intros m1 m2 E D Hle.
    eapply bundle_le_sub.
    intros ?. apply set_union_intro2. easy.
  Qed.  

  Lemma bundle_le_incident_to :
    forall E n1 n2, E ⊢ n1 ⪯ n2 -> n1 = n2 \/ (incident_to n1 E /\ incident_to n2 E).
  Proof.
    intros E n1 n2 Hle.
    induction Hle; auto.
    - apply edge_of_implies_incident_to in H; auto.
    - destruct IHHle1, IHHle2; subst; tauto.
  Qed.

  Lemma bundle_lt_cons:
    forall e m1 m2 E,
      E ⊢ m1 ≺ m2 -> (e :: E) ⊢ m1 ≺ m2.
  Proof.
    intros e m1 m2 E Hecrt. induction Hecrt as [n n' Hone|n n' n'' Hmulti1 IHmulti1 Hmulti2 IHmulti2].
    - specialize (in_cons e (n,n') E Hone) as Hinind. apply bundle_lt_one. assumption.
    - apply (bundle_lt_multi IHmulti1 IHmulti2).
  Qed.

  Lemma bundle_lt_permute :
    forall m1 m2 E E',
    Permutation E E' ->
    E ⊢ m1 ≺ m2 -> E' ⊢ m1 ≺ m2.
  Proof.
    intros m1 m2 E E' Hperm Hlt.
    induction Hlt.
    - apply (Permutation_in (n,n') Hperm) in H; now constructor.
    - apply (bundle_lt_multi IHHlt1 IHHlt2).
  Qed.

  Lemma bundle_lt_incl :
    forall E E' n1 n2,
      (forall e, In e E -> In e E') ->
      E ⊢ n1 ≺ n2 ->
      E' ⊢ n1 ≺ n2.
  Proof.
    intros E E' n1 n2 Hincl Hlt.
    induction Hlt.
    - apply bundle_lt_one. now apply Hincl.
    - eapply bundle_lt_multi; eauto.
  Qed.

  Lemma bundle_lt_then_le : forall E n1 n2, E ⊢ n1 ≺ n2 -> E ⊢ n1 ⪯ n2.
  Proof.
    intros E n1 n2 Hlt.
    induction Hlt.
    - apply bundle_le_one. assumption.
    - apply (bundle_le_multi IHHlt1 IHHlt2).
  Qed.

  Lemma bundle_le_then_lt :
    forall E n1 n2, E ⊢ n1 ⪯ n2 ->
      n1 = n2 \/ E ⊢ n1 ≺ n2.
  Proof.
    intros E n1 n2 Hlt.
    induction Hlt.
    - left. trivial.
    - right. apply bundle_lt_one. assumption.
    - destruct IHHlt1 as [Heq1 | Hect1]. all: destruct IHHlt2 as [Heq2 | Hect2].
      + subst. left. reflexivity.
      + subst. right. assumption.
      + subst. right. assumption.
      + right. apply (bundle_lt_multi Hect1 Hect2).
  Qed.

  Lemma bundle_lt_iff :
    forall m1 m2 n1 n2 E,
    ((n1,n2)::E) ⊢ m1 ≺ m2 <->
    E ⊢ m1 ≺ m2 \/
      (E ⊢ m1 ⪯ n1 /\ E ⊢ n2 ⪯ m2).
  Proof with (right; split; assumption).
    split.
    - intro Hecrt. induction Hecrt as [|m1 m2 n'' Hmulti1 IH1 Hmulti2 IH2].
      + simpl in H. destruct H.
        * injection H as Heq1 Heq2. subst. right. split. all: apply bundle_le_zero.
        * left. apply bundle_lt_one. assumption.
      + destruct (eq_node__t_dec m1 n'') as [Heq1|Hneq1].
        all: destruct (eq_node__t_dec n'' m2) as [Heq2|Hneq2].
        -- subst. apply IH2.
        -- subst. apply IH2.
        -- subst. apply IH1.
        -- destruct IH1 as [IH1or|[IH1and1 IH1and2]];
           destruct IH2 as [IH2or|[IH2and1 IH2and2]].
           ++ left. apply (bundle_lt_multi IH1or IH2or).
           ++ apply bundle_lt_then_le in IH1or. specialize (bundle_le_multi IH1or IH2and1) as IHw...
           ++ apply bundle_lt_then_le in IH2or. specialize (bundle_le_multi IH1and2 IH2or) as IHw...
           ++ trivial...
    - intros [Hor|[Hand1 Hand2]].
      + apply bundle_lt_cons. assumption.
      + apply (bundle_le_cons (n1,n2)) in Hand1.
        apply (bundle_le_cons (n1,n2)) in Hand2.
        assert (((n1,n2)::E) ⊢ n1 ≺ n2) as Hin.
        { apply bundle_lt_one. apply in_eq. }
        apply bundle_le_then_lt in Hand1.
        apply bundle_le_then_lt in Hand2.
        destruct Hand1, Hand2; subst; try easy;
        try (now specialize (bundle_lt_multi Hin H0));
        try (now specialize (bundle_lt_multi H Hin)).
        specialize (bundle_lt_multi H Hin) as Hin2.
        apply (bundle_lt_multi Hin2 H0).
  Qed.

  Lemma bundle_le_iff: forall m1 m2 n1 n2 E,
      (n1,n2)::E ⊢ m1 ⪯ m2 <->
       E ⊢ m1 ⪯ m2 \/
          (E ⊢ m1 ⪯ n1 /\ E ⊢ n2 ⪯ m2).
  Proof with (right; split; assumption).
    split.
    - intro Hecrt. induction Hecrt as [| | m1 m2 n'' Hmulti1 IH1 Hmulti2 IH2].
      + specialize (bundle_le_zero E n) as Hyes. left. assumption.
      + simpl in H. destruct H.
        * injection H as Heq1 Heq2. subst. right. split. all: apply (bundle_le_zero E _).
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
        assert (bundle_le ((n1,n2) :: E) n1 n2) as Hin. { apply bundle_le_one. apply in_eq. }
        specialize (bundle_le_multi Hand1 Hin) as Hin2.
        apply (bundle_le_multi Hin2 Hand2).
  Qed.

  Lemma bundle_le_dec : forall E m1 m2, { E ⊢ m1 ⪯ m2 } + { ~ E ⊢ m1 ⪯ m2 }.
  Proof.
    intros E.
    induction E as [ | (n1, n2) E IHC].
    - (* Base case: E = [] *)
      intros m1 m2.
      destruct (eq_node__t_dec m1 m2).
      + left. subst. apply bundle_le_zero.
      + right. unfold not; intros Hle. now apply bundle_le_inv_empty in Hle.
    - (* Ind. case: E is of the form (n1, n2)::E *)
      intros m1 m2.
      destruct (IHC m1 m2) as [HindL | HindR].
      + left.
        apply bundle_le_cons. assumption.
      + specialize (bundle_le_iff m1 m2 n1 n2 E) as [Hl Hr].
        destruct (IHC n2 m2) as [Handeq2 | Handneq2].
        * destruct (IHC m1 n1) as [Handeq1 | Handneq1].
          -- left. apply Hr. right. split. all: assumption.
          -- right. intro Hcontra. specialize (Hl Hcontra) as [? | [? ?]]. all: contradiction.
        * right. intro Hcontra. specialize (Hl Hcontra) as [? | [? ?]]. all: contradiction.
  Qed.

  Lemma bundle_le_refl :
    forall E, reflexive node__t (bundle_le E).
  Proof.
    intro E. unfold reflexive. intro x. apply bundle_le_zero.
  Qed.

  Lemma bundle_le_trans :
    forall E, transitive node__t (bundle_le E).
  Proof.
    unfold transitive.
    intros E n n' n'' Hlt1 Hlt2.
    apply (bundle_le_multi Hlt1 Hlt2).
  Qed.

  Lemma bundle_le_rev_trans :
    forall E, transitive node__t (fun n n' => E ⊢ n' ⪯ n).
  Proof.
    unfold transitive.
    intros E n n' n'' Hlt1 Hlt2.
    apply (bundle_le_multi Hlt2 Hlt1).
  Qed.

  Lemma bundle_le_antisymm_acyclic :
    forall E,
      (forall n, ~ E ⊢ n ≺ n) ->
      antisymmetric node__t (bundle_le E).
  Proof.
    unfold antisymmetric.
    intros E Hacyclic n n' Hle Hle'.
    destruct (eq_node__t_dec n n') as [Heq|Hneq]; auto.
    apply bundle_le_then_lt in Hle.
    apply bundle_le_then_lt in Hle'.
    destruct Hle as [Heq|Hlt]; try contradiction.
    destruct Hle' as [Heq|Hlt']; try (symmetry in Heq; contradiction).
    exfalso. apply (Hacyclic n). exact (bundle_lt_multi Hlt Hlt').
  Qed.

  Lemma bundle_le_rev_antisymm :
    forall E,
      (forall n, ~ E ⊢ n ≺ n) ->
      antisymmetric node__t (fun n n' => E ⊢ n' ⪯ n).
  Proof.
    unfold antisymmetric.
    intros E Hacyclic n n' Hle Hle'.
    eapply bundle_le_antisymm_acyclic; eauto.
  Qed.

End BundleRelations.


