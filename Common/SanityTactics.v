(**
  Tactics for sanity checks: building a concrete bundle and discharging, on it,
  the hypotheses of a protocol guarantee.

  [ind_bundle] is useful beyond sanity checks: it proves [IndBundle], or
  [is_bundle] via [IndBundle_sound], for any concrete bundle whose three lists
  are in derivation order.
*)

From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

Require Import Strands.
Require Import Bundles.
Require Import BundleInductive.
Require Import MinimalMPT.
Require Import StrandsTacticsFunctor.

Module MakeSanityTactics
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St)
  (Import B : BundleSig T St SSp)
  (Import BI : BundleInductiveSig T St SSp B)
  (Import TT : TermTacticsSig).

  (* [MPT] and [MakeStrandsTactics] have no module type, so they are
     re-instantiated here rather than taken as parameters.  Both are cheap:
     of the first only [originates_then_mpt] is used, the second is Ltac only. *)
  Module MPTI := MPT T St SSp B.
  Import MPTI.
  Module STI := MakeStrandsTactics T St SSp TT.
  Import STI.

  (** ** Building the bundle *)

  (* Side conditions of the [IndBundle] constructors.  Internal to [ind_bundle]. *)
  Ltac indb_in  := simpl; repeat first [ left; reflexivity | right ].
  Ltac indb_nin := simpl; let H := fresh in intro H;
                   repeat (destruct H as [H|H]);
                   solve [ discriminate H | now inversion H | contradiction ].
  Ltac indb_edge := simpl; reflexivity.
  Ltac indb_pos  := simpl; exact I.

  (** Each constructor conses onto the head of [nodes], and [G_pos]/[G_neg] also
      onto [intra]/[inter], so the heads of the three lists determine which one
      applies, so no search is needed: only case recognition. *)
  Ltac ind_bundle :=
    try apply IndBundle_sound;
    repeat first
      [ apply G_empty
      | eapply G_pos_zero; [ | indb_nin | indb_pos  | reflexivity ]
      | eapply G_pos;      [ | indb_in  | indb_nin  | indb_pos  | indb_edge ]
      | eapply G_neg_zero; [ | indb_in  | indb_nin  | indb_edge | reflexivity ]
      | eapply G_neg;      [ | indb_in  | indb_in   | indb_nin  | indb_edge | indb_edge ] ].

  (** ** Discharging the guarantee's hypotheses *)

  (** A concrete strand belongs to a role.  The role constructor fixes the strand
      identifier by unification; what is left is its premise, if it has one, which
      for a typing discipline is a conjunction of memberships and non-memberships. *)
  Ltac solve_role :=
    econstructor; repeat split;
    repeat first
      [ (let H := fresh in intro H; repeat (destruct H as [H|H]); discriminate)
      | solve [ repeat first [ left; reflexivity | right ]; reflexivity ]
      | easy ].

  (** [is_strand_of s C]: the index is bounded by the trace length, so peeling it
      exhausts the nodes of [s], and [lia] closes the overflow case. *)
  Ltac solve_is_strand_of :=
    unfold is_strand_of, is_node_of; intros n Hs Hlt;
    rewrite Hs in Hlt; simpl in Hlt;
    rewrite (node_as_pair n), Hs;
    remember (index n) as i;
    repeat (destruct i as [|i]; [ simpl; tauto | ]);
    lia.

  (** [bundle_in_SS C SSp]: one case per node, closed by [eauto] on the [sanity]
      database.  That database is the only per protocol part: the example declares
      its strand space with [Hint Constructors] and the strands it exhibits with
      [Hint Resolve], so [eauto] can use those strands and no others. *)
  Ltac solve_bundle_in_SS :=
    unfold bundle_in_SS; intros n Hn;
    repeat (destruct Hn as [Hn|Hn];
            [ rewrite <- Hn; simpl; eauto with sanity | ]);
    contradiction.

  (** [strandspace_bundle] requires to prove both [is_bundle] and [bundle_in_SS]. *)
  Ltac solve_strandspace_bundle :=
    split; [ind_bundle | solve_bundle_in_SS].

  (* Node 0 of a strand of [C] with a concrete trace is a node of [C]: split the
     membership and close every disjunct whose trace differs.  Internal to
     [solve_unique_strand] and [solve_no_strand]. *)
  Ltac strand_node0_cases :=
    match goal with
    | H : is_strand_of ?t ?C |- _ =>
        assert (is_node_of (t, 0) C) as Hn by (apply H; simpl; [reflexivity | lia]);
        simpl in Hn;
        repeat (destruct Hn as [Hn|Hn]); try discriminate; try contradiction
    end.

  (** [forall s, is_strand_of s C -> Role ... s -> s = s0]: inverting the role makes
      the trace concrete, so node 0 of [s] is a node of [C], and the membership has
      exactly one disjunct whose trace matches. *)
  Ltac solve_unique_strand :=
    intros s Hs Hr; inversion Hr; subst;
    strand_node0_cases;
    now inversion Hn.

  (** [~ (exists s, Role ... s /\ is_strand_of s C)]: as for [solve_unique_strand],
      but no disjunct of the membership has a matching trace. *)
  Ltac solve_no_strand :=
    let s := fresh "s" in let Hr := fresh "Hr" in let Hs := fresh "Hs" in
    intros [s [Hr Hs]]; inversion Hr; subst;
    strand_node0_cases.

  (** [originates t n] for a node at index 0: [index_0_positive_originates] takes
      it from the subterm and positivity side conditions, both computed. *)
  Ltac solve_originates :=
    apply index_0_positive_originates;
    [ unfold uns_term, term; simpl; intuition
    | unfold is_positive, term; now simpl
    | reflexivity ].

  (** Refute [originates_at_most_once_in C t] by naming the two nodes of [C] that
      both originate [t].  They are given rather than searched for: which two
      origination points collide is the content of the counterexample. *)
  Ltac refute_at_most_once_in n1 n2 :=
    match goal with
    | |- ~ originates_at_most_once_in ?C ?t =>
        let Hamo := fresh "Hamo" in intro Hamo;
        let Hn1 := fresh "Hn" in assert (is_node_of n1 C) as Hn1 by indb_in;
        let Hn2 := fresh "Hn" in assert (is_node_of n2 C) as Hn2 by indb_in;
        let Ho1 := fresh "Ho" in assert (originates t n1) as Ho1 by solve_originates;
        let Ho2 := fresh "Ho" in assert (originates t n2) as Ho2 by solve_originates;
        specialize (Hamo _ _ Hn1 Hn2 Ho1 Ho2); discriminate
    end.

  (** Turn an origination hypothesis into the minimal-position fact it implies,
      and reduce it.  Once the node is concrete [tr (strand n)] computes, so
      [eq_refl] is the witness that [originates_then_mpt] asks for. *)
  Ltac origin_to_mpt H :=
    let Hm := fresh "Hm" in
    specialize (originates_then_mpt eq_refl H) as Hm;
    simpl in Hm; simplify_prop in Hm.

  (** [originates_at_most_once_in C t]: the two memberships generate the cross
      product of the nodes of [C], the diagonal closes by [reflexivity], and every
      mixed case dies because one of the two nodes cannot originate [t]. *)
  Ltac solve_at_most_once_in :=
    unfold originates_at_most_once_in; intros n n' Hin Hin' Ho Ho';
    repeat (destruct Hin as [Hn|Hin]); try easy; subst;
    (* discharge the impossible nodes for [n] before splitting on [n'], so the
       cross product never forms: on a bundle of 15 nodes that is 30 cases
       instead of 225 *)
    try origin_to_mpt Ho;
    repeat (destruct Hin' as [Hn'|Hin']); try easy; subst;
    try reflexivity;
    try origin_to_mpt Ho'.

End MakeSanityTactics.
