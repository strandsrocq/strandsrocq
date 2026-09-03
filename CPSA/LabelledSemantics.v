From Stdlib Require Import List Lia Arith.PeanoNat.
Import ListNotations.

From strandsrocq.CPSA Require Import
  RoleSyntax ChoiceRoles Semantics ComputableSemantics.
From strandsrocq.CPSA.Instances Require Import DefaultInstances.

Import CPSA_Direct_Syntax.
Import ChoiceRoles.
Import CPSA_Semantics.
Import CPSA_Computable_Semantics.

Open Scope string_scope.
Open Scope list_scope.
Open Scope cpsa_direct_syntax_scope.

(** * Type-level labelled CPSA semantics

    This file defines the canonical labelled transition system for thread-pool
    executions.  The LTS lives in [Type], and receive steps use the indexed
    occurrence judgment from [ComputableSemantics.v].  Thus labels carry the
    same communication witnesses as [pool_reachable_fromT], and the two
    presentations convert into each other computationally.

    Labels mention pool thread/index coordinates.  The helper functions below
    can turn those coordinates into bundle nodes once a strand assignment [st]
    is chosen for thread indices.
*)
Module CPSA_Labelled_Semantics.

  (** A [node_ref] is a node name relative to the operational thread pool:
      [ref_thread] selects the thread, and [ref_index] selects the event within
      that thread.  This is deliberately independent of bundle strand names;
      the conversion to bundle nodes is performed later by choosing a strand
      assignment [st : nat -> Σ]. *)
  Record node_ref := {
    ref_thread : nat;
    ref_index : nat
  }.

  (** A step label records the node created by a transition.

      - [dst] is the newly executed event.
      - [ev] repeats the signed event at [dst], making labels readable without
        looking up the destination in the target pool.
      - [src] is [None] for sends and [Some r] for receives, where [r] is the
        positive node that justifies the receive.

      Thus receive labels carry the communication edge needed to reconstruct
      bundle interstrand edges. *)
  Record step_label := {
    dst : node_ref;
    ev : sT;
    src : option node_ref
  }.

  (** Interpret a pool-relative node reference as an actual bundle node. *)
  Definition node_of_ref (st : nat -> Σ) (r : node_ref) : node__t :=
    (st (ref_thread r), ref_index r).

  Definition label_dst (st : nat -> Σ) (l : step_label) : node__t :=
    node_of_ref st (dst l).

  Definition label_src (st : nat -> Σ) (l : step_label) : option node__t :=
    option_map (node_of_ref st) (src l).

  Definition empty_bundle : bundle_type :=
    {| nodes := []; intra := []; inter := [] |}.

  (** Add the node and edges described by one label to a bundle skeleton.

      The destination node is always added.  If the destination index is not
      zero, an intrastrand edge from the previous event on the same thread is
      added.  If [src] is present, the corresponding interstrand edge is added.

      This function is intentionally just a syntactic skeleton builder.  The
      soundness theorems below go through [ComputableSemantics.v], whose bundle
      construction already proves the required wellformedness properties. *)
  Definition add_label_to_bundle
    (st : nat -> Σ)
    (B : bundle_type)
    (l : step_label)
    : bundle_type :=
    let n := label_dst st l in
    let pred :=
      match ref_index (dst l) with
      | 0 => None
      | S j => Some (st (ref_thread (dst l)), j)
      end in
    {| nodes := n :: nodes B;
       intra :=
         match pred with
         | None => intra B
         | Some p => (p, n) :: intra B
         end;
       inter :=
         match label_src st l with
         | None => inter B
         | Some p => (p, n) :: inter B
         end |}.

  Definition bundle_of_labels (st : nat -> Σ) (ls : list step_label)
    : bundle_type :=
    fold_left (add_label_to_bundle st) ls empty_bundle.

  Reserved Notation "P '⊩ᵀ' T '-[' l ']→' T'"
    (at level 70, T at next level, l at next level).

  (** One labelled operational step.

      The four constructors mirror the four constructors of
      [pool_reachable_fromT]:

      - spawn a new sending thread;
      - extend an existing thread with a send;
      - spawn a new receiving thread;
      - extend an existing thread with a receive.

      The send rules have no source.  The receive rules use the Type-level
      indexed occurrence judgment [T ↓[i,j] ⊕m], so the label records exactly
      the positive node used by the computable semantics. *)
  Inductive labelled_stepT (P : protocol)
    : thread_pool -> step_label -> thread_pool -> Type :=
  | TLSpawnSend :
      forall T m,
        P ▷ [⊕m] ->
        P ⊩ᵀ T -[
          {| dst := {| ref_thread := length T; ref_index := 0 |};
             ev := ⊕m;
             src := None |}
        ]→ T ⋈ [⊕m]
  | TLExtendSend :
      forall tr T1 T2 m,
        P ▷ tr ++ [⊕m] ->
        P ⊩ᵀ T1 ⋈ tr ⋈ T2 -[
          {| dst := {| ref_thread := length T1; ref_index := length tr |};
             ev := ⊕m;
             src := None |}
        ]→ T1 ⋈ (tr ++ [⊕m]) ⋈ T2
  | TLSpawnRecv :
      forall T i j m,
        T ↓[i,j] ⊕m ->
        P ▷ [⊖m] ->
        P ⊩ᵀ T -[
          {| dst := {| ref_thread := length T; ref_index := 0 |};
             ev := ⊖m;
             src := Some {| ref_thread := i; ref_index := j |} |}
        ]→ T ⋈ [⊖m]
  | TLExtendRecv :
      forall tr T1 T2 i j m,
        T1 ⋈ tr ⋈ T2 ↓[i,j] ⊕m ->
        P ▷ tr ++ [⊖m] ->
        P ⊩ᵀ T1 ⋈ tr ⋈ T2 -[
          {| dst := {| ref_thread := length T1; ref_index := length tr |};
             ev := ⊖m;
             src := Some {| ref_thread := i; ref_index := j |} |}
        ]→ T1 ⋈ (tr ++ [⊖m]) ⋈ T2

  where "P '⊩ᵀ' T '-[' l ']→' T'" :=
    (labelled_stepT P T l T') : cpsa_direct_syntax_scope.

  Reserved Notation "P '⊩ᵀ' T '-[' ls ']→*' T'"
    (at level 70, T at next level, ls at next level).

  (** Reflexive transitive closure of labelled steps, with the labels stored in
      execution order.  The list [ls] can be read as the audit trail of the pool
      execution from the initial pool to the final one. *)
  Inductive labelled_reachable_fromT (P : protocol)
    : thread_pool -> list step_label -> thread_pool -> Type :=
  | TLReachDone :
      forall T,
        P ⊩ᵀ T -[ [] ]→* T
  | TLReachStep :
      forall T0 T1 T2 l ls,
        P ⊩ᵀ T0 -[ l ]→ T1 ->
        P ⊩ᵀ T1 -[ ls ]→* T2 ->
        P ⊩ᵀ T0 -[ l :: ls ]→* T2

  where "P '⊩ᵀ' T '-[' ls ']→*' T'" :=
    (labelled_reachable_fromT P T ls T') : cpsa_direct_syntax_scope.

  (** Append one labelled step to the end of a labelled execution.

      The Type-level pool semantics is inductive in "previous derivation plus
      final step" form, so the reverse conversion below naturally needs this
      snoc lemma to append the newly generated label. *)
  Lemma labelled_reachableT_snoc :
    forall P T0 T1 T2 ls l,
      P ⊩ᵀ T0 -[ ls ]→* T1 ->
      P ⊩ᵀ T1 -[ l ]→ T2 ->
      P ⊩ᵀ T0 -[ ls ++ [l] ]→* T2.
  Proof.
    intros P T0 T1 T2 ls l Hreach Hstep.
    induction Hreach.
    - simpl.
      apply TLReachStep with (T1 := T2).
      + exact Hstep.
      + constructor.
    - simpl.
      apply TLReachStep with (T1 := T1).
      + exact l1.
      + now apply IHHreach.
  Defined.

  Lemma labelled_step_length_monotone :
    forall P T l T',
      P ⊩ᵀ T -[ l ]→ T' ->
      length T <= length T'.
  Proof.
    intros P T l T' Hstep.
    inversion Hstep; subst; simpl; rewrite ?length_app; simpl; lia.
  Qed.

  Lemma labelled_reachable_length_monotone :
    forall P T ls T',
      P ⊩ᵀ T -[ ls ]→* T' ->
      length T <= length T'.
  Proof.
    intros P T ls T' Hreach.
    induction Hreach as
      [T | T0 T1 T2 l ls Hstep Htail IH]; try lia.
    eapply Nat.le_trans with (m := length T1).
    - exact (labelled_step_length_monotone P T0 l T1 Hstep).
    - exact IH.
  Qed.

  Lemma labelled_destination_thread_bound :
    forall P T0 ls T,
      P ⊩ᵀ T0 -[ ls ]→* T ->
      forall l,
        In l ls ->
        ref_thread (dst l) < length T.
  Proof.
    intros P T0 ls T Hreach.
    induction Hreach as
      [T | T0 T1 T2 l ls Hstep Htail IH]; intros q Hq.
    - contradiction.
    - simpl in Hq. destruct Hq as [Heq | Hq].
      + subst q.
        assert (Hmono : length T1 <= length T2).
        { exact (labelled_reachable_length_monotone P T1 ls T2 Htail). }
        inversion Hstep; subst; simpl in *;
          rewrite ?length_app in *; simpl in *; lia.
      + apply IH in Hq.
        exact Hq.
  Qed.

  Lemma map_label_dst_ext :
    forall st st' ls,
      (forall l,
          In l ls ->
          st (ref_thread (dst l)) = st' (ref_thread (dst l))) ->
      map (label_dst st) ls = map (label_dst st') ls.
  Proof.
    intros st st' ls Hagree.
    induction ls as [|l ls IH]; simpl; auto.
    f_equal.
    - unfold label_dst, node_of_ref.
      rewrite (Hagree l ltac:(left; reflexivity)). reflexivity.
    - apply IH. intros q Hq. apply Hagree. now right.
  Qed.

  Lemma map_label_dst_reachable_ext :
    forall P T0 ls T st st',
      P ⊩ᵀ T0 -[ ls ]→* T ->
      (forall i, i < length T -> st i = st' i) ->
      map (label_dst st) ls = map (label_dst st') ls.
  Proof.
    intros P T0 ls T st st' Hreach Hagree.
    apply map_label_dst_ext.
    intros l Hl.
    apply Hagree.
    exact (labelled_destination_thread_bound P T0 ls T Hreach l Hl).
  Qed.

  (** Forget one label and recover the corresponding one-step Type-level pool
      reachability derivation.  This conversion is transparent, so it can be
      unfolded by computation. *)
  Definition labelled_stepT_erases
    {P T T' l}
    (Hstep : P ⊩ᵀ T -[ l ]→ T')
    : pool_reachable_fromT P T T' :=
    match Hstep with
    | TLSpawnSend _ T m Hprefix =>
        PoolSpawnSendT P T T m (PoolBaseT P T) Hprefix
    | TLExtendSend _ tr T1 T2 m Hprefix =>
        PoolExtendSendT P (T1 ⋈ tr ⋈ T2) tr T1 T2 m
          (PoolBaseT P (T1 ⋈ tr ⋈ T2))
          Hprefix
    | TLSpawnRecv _ T i j m Hocc Hprefix =>
        PoolSpawnRecvT P T T i j m (PoolBaseT P T) Hocc Hprefix
    | TLExtendRecv _ tr T1 T2 i j m Hocc Hprefix =>
        PoolExtendRecvT P (T1 ⋈ tr ⋈ T2) tr T1 T2 i j m
          (PoolBaseT P (T1 ⋈ tr ⋈ T2))
          Hocc
          Hprefix
    end.

  (** Forget all labels from a labelled execution.  The result is a
      [pool_reachable_fromT] derivation with the same endpoints. *)
  Fixpoint labelled_reachableT_erases
    {P T0 T ls}
    (Hreach : P ⊩ᵀ T0 -[ ls ]→* T)
    : pool_reachable_fromT P T0 T :=
    match Hreach with
    | TLReachDone _ T =>
        PoolBaseT P T
    | TLReachStep _ T0 T1 T2 l ls Hstep Htail =>
        pool_reachable_fromT_trans
          P T0 T1 T2
          (labelled_stepT_erases Hstep)
          (labelled_reachableT_erases Htail)
    end.

  (** Convert a Type-level pool reachability derivation into a labelled
      execution.

      This is the computational reverse of [labelled_reachableT_erases].  Each
      pool constructor determines the next label.  In the receive cases, the
      [i,j] witness already present in [pool_reachable_fromT] becomes the
      [src] field of the label. *)
  Fixpoint reachableT_from_has_labelsT
    {P T0 T}
    (Hreach : pool_reachable_fromT P T0 T)
    : { ls : list step_label & P ⊩ᵀ T0 -[ ls ]→* T } :=
    match Hreach with
    | PoolBaseT _ _ =>
        existT _ [] (TLReachDone P T0)
    | PoolSpawnSendT _ _ T m Hprev Hprefix =>
        let '(existT _ ls Hls) := reachableT_from_has_labelsT Hprev in
        existT _
          (ls ++
            [{| dst := {| ref_thread := length T; ref_index := 0 |};
                ev := ⊕m;
                src := None |}])
          (labelled_reachableT_snoc
            P _ T _ ls _
            Hls
            (TLSpawnSend P T m Hprefix))
    | PoolExtendSendT _ _ tr T1 T2 m Hprev Hprefix =>
        let '(existT _ ls Hls) := reachableT_from_has_labelsT Hprev in
        existT _
          (ls ++
            [{| dst := {| ref_thread := length T1; ref_index := length tr |};
                ev := ⊕m;
                src := None |}])
          (labelled_reachableT_snoc
            P _ (T1 ⋈ tr ⋈ T2) _ ls _
            Hls
            (TLExtendSend P tr T1 T2 m Hprefix))
    | PoolSpawnRecvT _ _ T i j m Hprev Hocc Hprefix =>
        let '(existT _ ls Hls) := reachableT_from_has_labelsT Hprev in
        existT _
          (ls ++
            [{| dst := {| ref_thread := length T; ref_index := 0 |};
                ev := ⊖m;
                src := Some {| ref_thread := i; ref_index := j |} |}])
          (labelled_reachableT_snoc
            P _ T _ ls _
            Hls
            (TLSpawnRecv P T i j m Hocc Hprefix))
    | PoolExtendRecvT _ _ tr T1 T2 i j m Hprev Hocc Hprefix =>
        let '(existT _ ls Hls) := reachableT_from_has_labelsT Hprev in
        existT _
          (ls ++
            [{| dst := {| ref_thread := length T1; ref_index := length tr |};
                ev := ⊖m;
                src := Some {| ref_thread := i; ref_index := j |} |}])
          (labelled_reachableT_snoc
            P _ (T1 ⋈ tr ⋈ T2) _ ls _
            Hls
            (TLExtendRecv P tr T1 T2 i j m Hocc Hprefix))
    end.

  Definition reachable_poolT_has_labelsT
    {P T}
    (Hreach : reachable_poolT P T)
    : { ls : list step_label & P ⊩ᵀ [] -[ ls ]→* T } :=
    reachableT_from_has_labelsT Hreach.

  (** Bundle completeness, transported through the Type-level LTS.

      The existing completeness theorem in [ComputableSemantics.v] produces an
      inhabited [reachable_poolT] derivation from an inductive compatible
      bundle.  The conversion above then turns that derivation into an
      inhabited labelled execution.

      The outer statement remains existential/propositional because the bundle
      hypotheses themselves live in [Prop].  The actual conversion from
      [reachable_poolT] to labelled executions is computational. *)
  Theorem bundle_has_labelled_executionT :
    forall G P,
      IndBundle G ->
      ofProtocol G P ->
      tau_non_originating G ->
      exists T full_trace pool_strand,
        inhabited { ls : list step_label & P ⊩ᵀ [] -[ ls ]→* T } /\
        extends_pool_trace T full_trace /\
        represents_pool G T full_trace pool_strand.
  Proof.
    intros G P Hbundle Hproto Htau.
    destruct (reachable_poolT_inhabited_of_bundle G P Hbundle Hproto Htau)
      as [T [full_trace [pool_strand [[HreachT] [Hext Hrepr]]]]].
    destruct (reachable_poolT_has_labelsT HreachT) as [ls Hlabelled].
    exists T, full_trace, pool_strand.
    split.
    - constructor.
      exists ls.
      exact Hlabelled.
    - split.
      + exact Hext.
      + exact Hrepr.
  Qed.

End CPSA_Labelled_Semantics.
