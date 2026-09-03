From Stdlib Require Import List String.
Import ListNotations.

From strandsrocq.CPSA Require Import
  RoleSyntax ChoiceRoles Semantics ProtocolExamples ComputableSemantics
  LabelledSemantics.
From strandsrocq.CPSA.Instances Require Import DefaultInstances.

(** * Paper examples

This file collects the Rocq artifacts that are referenced by the paper.  It is
intended as a small proof index: each item below points to, or packages, the
corresponding development theorem used in the text.
*)

Module PaperExamples.

  Import CPSA_Direct_Syntax.
  Import ChoiceRoles.
  Import CPSA_Semantics.
  Import CPSA_Computable_Semantics.
  Import CPSA_Labelled_Semantics.

  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope cpsa_direct_syntax_scope.

  Local Coercion M_Name : Name >-> Mesg.
  Local Coercion M_Text : Text >-> Mesg.
  Local Coercion M_Akey : Akey >-> Mesg.
  Local Coercion M_Tag : Tag >-> Mesg.
  Local Coercion TTag : Tag >-> cpsa_term.

  (** Separate scopes keep protocol-local paper names unambiguous: for
      instance [MkText 0] is [Q] in Section 4, but [Na] in the worked
      Yahalom example. *)
  Declare Scope paper_yes_no_scope.
  Declare Scope paper_yahalom_scope.

  Parameter eta : valuation.

  (** ** Paper Section 4: yes-or-no protocol and choice *)

  Section YesOrNoProtocol.
    (** The symbolic variables used by the yes-or-no roles in
        Section 4 of the paper.  They are section-local so the roles can use
        the paper names [A], [Q], [y], and [n] without polluting the rest of
        the file. *)
    Let a : tvar S_Name := mkTVar "A".
    Let q : tvar S_Text := mkTVar "Q".
    Let y : tvar S_Text := mkTVar "y".
    Let n : tvar S_Text := mkTVar "n".

    (** The questioner branches are written out explicitly so that the
        desugaring theorem below has concrete roles to compare against.  The
        protocol itself uses the [CHOICE] form [yes_no_questioner_roles]. *)
    Definition yes_no_questioner_yes_role : role :=
      DEFROLE "questioner-yes"
      VARS [
        [a] IS S_Name;
        [q; y; n] IS S_Text ]
      TRACE
        [ send enc{q; y; n}_(pubk a);
          recv (as_msg y) ]
      NONORIG
        []
      UNIQORIG
        [].

    Definition yes_no_questioner_no_role : role :=
      DEFROLE "questioner-no"
      VARS [
        [a] IS S_Name;
        [q; y; n] IS S_Text ]
      TRACE
        [ send enc{q; y; n}_(pubk a);
          recv (as_msg n) ]
      NONORIG
        []
      UNIQORIG
        [].

    (** Paper Section 4 presents choice as a trace-tree abbreviation.  This is
        the questioner behavior using that abbreviation directly. *)
    Definition yes_no_questioner_roles : list role :=
      CHOICE "questioner"
      VARS [
        [a] IS S_Name;
        [q; y; n] IS S_Text ]
      NONORIG
        []
      UNIQORIG
        []
      TRACES [
        TRACE [ send enc{q; y; n}_(pubk a) ]
        THEN [
          TRACE "yes" [ recv (as_msg y) ];
          TRACE "no" [ recv (as_msg n) ]
        ]
      ].

    Definition yes_no_answerer_yes_role : role :=
      DEFROLE "answerer-yes"
      VARS [
        [a] IS S_Name;
        [q; y; n] IS S_Text ]
      TRACE
        [ recv enc{q; y; n}_(pubk a);
          send (as_msg y) ]
      NONORIG
        []
      UNIQORIG
        [].

    Definition yes_no_answerer_no_role : role :=
      DEFROLE "answerer-no"
      VARS [
        [a] IS S_Name;
        [q; y; n] IS S_Text ]
      TRACE
        [ recv enc{q; y; n}_(pubk a);
          send (as_msg n) ]
      NONORIG
        []
      UNIQORIG
        [].

    (** The answerer roles are kept both as explicit roles and as a [CHOICE]
        expression.  This mirrors the paper: the expanded roles are useful for
        the small reachability proofs, while the [CHOICE] expression records
        the intended source syntax. *)
    Definition yes_no_answerer_roles : list role :=
      CHOICE "answerer"
      VARS [
        [a] IS S_Name;
        [q; y; n] IS S_Text ]
      NONORIG
        []
      UNIQORIG
        []
      TRACES [
        TRACE [ recv enc{q; y; n}_(pubk a) ]
        THEN [
          TRACE "yes" [ send (as_msg y) ];
          TRACE "no" [ send (as_msg n) ]
        ]
      ].

    (** The questioner choice elaborates to the two ordinary roles above. *)
    Theorem paper_yes_no_questioner_choice_desugars :
      yes_no_questioner_roles = [
        yes_no_questioner_yes_role;
        yes_no_questioner_no_role
      ].
    Proof.
      reflexivity.
    Qed.

    (** This is the desugaring lemma cited for the answerer choice in
        Section 4. *)
    Theorem paper_yes_no_choice_desugars :
      yes_no_answerer_roles = [
        yes_no_answerer_yes_role;
        yes_no_answerer_no_role
      ].
    Proof.
      reflexivity.
    Qed.

    (** The yes-or-no protocol used for the operational examples in
        Section 4.3.  Choice has disappeared by this point: the protocol is
        just a list of ordinary roles. *)
    Definition yes_no_protocol : protocol :=
      mkProtocol (yes_no_questioner_roles ++ yes_no_answerer_roles).

    (** The paper-level examples only use regular trace generation, so this
        well-formedness check establishes that no message-level origination
        assumptions are hidden in the protocol. *)
    Theorem paper_yes_no_protocol_well_formed :
      wf_protocol_no_mesg_origination yes_no_protocol.
    Proof.
      simpl.
      intros r [<- | [<- | [<- | [<- | []]]]];
        simpl; repeat split; intros x H; destruct H.
    Qed.

    (** Concrete ground values for the yes-or-no run.  The associated
        [paper_yes_no_scope] lets the concrete atoms below be written
        and printed as [A], [Q], [Y], and [N]. *)
    Notation "'A'" := (MkName 0)
      : paper_yes_no_scope.
    Notation "'Q'" := (MkText 0)
      : paper_yes_no_scope.
    Notation "'Y'" := (MkText 1)
      : paper_yes_no_scope.
    Notation "'N'" := (MkText 2)
      : paper_yes_no_scope.

    Local Open Scope paper_yes_no_scope.
    
    Definition yes_no_valuation : valuation :=
      eta {{ a := A }}
          {{ q := Q }}
          {{ y := Y }}
          {{ n := N }}.

    Definition yes_no_question : Mesg :=
      ⟨ Q ⋅ Y ⋅ N ⟩_(K A).

    (** The pool [T2] in Section 4.3: the question has been sent by the
        questioner and received by the answerer, but the answerer has not yet
        committed to yes or no. *)
    Definition yes_no_T2 : thread_pool :=
      [[⊕ yes_no_question]] ⋈ [⊖ yes_no_question].

    Definition yes_no_yes_pool : thread_pool :=
      [[⊕ yes_no_question; ⊖ Y]] ⋈
      [⊖ yes_no_question; ⊕ Y].

    Definition yes_no_no_pool : thread_pool :=
      [[⊕ yes_no_question; ⊖ N]] ⋈
      [⊖ yes_no_question; ⊕ N].

    (** Prefix witnesses used by the operational rules.  Each one says that a
        ground trace prefix is compatible with one instantiated role in
        [yes_no_protocol]. *)
    Lemma paper_yes_no_prefix_questioner_yes_send :
      yes_no_protocol ▷ [⊕ yes_no_question].
    Proof.
      exists yes_no_questioner_yes_role, yes_no_valuation, [⊖ Y].
      split; [simpl; auto | vm_compute; reflexivity].
    Qed.

    Lemma paper_yes_no_prefix_answerer_common :
      yes_no_protocol ▷ [⊖ yes_no_question].
    Proof.
      exists yes_no_answerer_yes_role, yes_no_valuation, [⊕ Y].
      split; [simpl; auto | vm_compute; reflexivity].
    Qed.

    Lemma paper_yes_no_prefix_answerer_yes :
      yes_no_protocol ▷ [⊖ yes_no_question; ⊕ Y].
    Proof.
      exists yes_no_answerer_yes_role, yes_no_valuation, [].
      split; [simpl; auto | vm_compute; reflexivity].
    Qed.

    Lemma paper_yes_no_prefix_questioner_yes :
      yes_no_protocol ▷ [⊕ yes_no_question; ⊖ Y].
    Proof.
      exists yes_no_questioner_yes_role, yes_no_valuation, [].
      split; [simpl; auto | vm_compute; reflexivity].
    Qed.

    Lemma paper_yes_no_prefix_answerer_no :
      yes_no_protocol ▷ [⊖ yes_no_question; ⊕ N].
    Proof.
      exists yes_no_answerer_no_role, yes_no_valuation, [].
      split; [simpl; auto | vm_compute; reflexivity].
    Qed.

    Lemma paper_yes_no_prefix_questioner_no :
      yes_no_protocol ▷ [⊕ yes_no_question; ⊖ N].
    Proof.
      exists yes_no_questioner_no_role, yes_no_valuation, [].
      split; [simpl; auto | vm_compute; reflexivity].
    Qed.

    (** The concrete execution prefix [T2] from the paper: spawn the
        questioner send, then spawn an answerer receive justified by that
        send. *)
    Theorem paper_yes_no_T2_reachable :
      yes_no_protocol ⊨ yes_no_T2.
    Proof.
      unfold yes_no_T2.
      apply (PoolSpawnRecv yes_no_protocol [] [[⊕ yes_no_question]]
        yes_no_question).
      - apply (PoolSpawnSend yes_no_protocol [] [] yes_no_question).
        + constructor.
        + exact paper_yes_no_prefix_questioner_yes_send.
      - unfold event_occurred; simpl; tauto.
      - exact paper_yes_no_prefix_answerer_common.
    Qed.

    Theorem paper_yes_no_yes_pool_reachable :
      yes_no_protocol ⊨ yes_no_yes_pool.
    Proof.
      unfold yes_no_yes_pool.
      apply (PoolExtendRecv yes_no_protocol
        []
        [⊕ yes_no_question]
        []
        [[⊖ yes_no_question; ⊕ Y]]
        Y).
      - apply (PoolExtendSend yes_no_protocol
          []
          [⊖ yes_no_question]
          [[⊕ yes_no_question]]
          []
          Y).
        + exact paper_yes_no_T2_reachable.
        + exact paper_yes_no_prefix_answerer_yes.
      - unfold event_occurred; simpl; tauto.
      - exact paper_yes_no_prefix_questioner_yes.
    Qed.

    Theorem paper_yes_no_no_pool_reachable :
      yes_no_protocol ⊨ yes_no_no_pool.
    Proof.
      unfold yes_no_no_pool.
      apply (PoolExtendRecv yes_no_protocol
        []
        [⊕ yes_no_question]
        []
        [[⊖ yes_no_question; ⊕ N]]
        N).
      - apply (PoolExtendSend yes_no_protocol
          []
          [⊖ yes_no_question]
          [[⊕ yes_no_question]]
          []
          N).
        + exact paper_yes_no_T2_reachable.
        + exact paper_yes_no_prefix_answerer_no.
      - unfold event_occurred; simpl; tauto.
      - exact paper_yes_no_prefix_questioner_no.
    Qed.

    (** From the same uncommitted pool [T2], the answerer may take the yes
        branch.  This is the formal counterpart of the left branch in the
        Section 4.3 discussion. *)
    Theorem paper_yes_no_yes_pool_reachable_from_T2 :
      yes_no_protocol ⊨ᶠ yes_no_T2 →* yes_no_yes_pool.
    Proof.
      unfold yes_no_T2, yes_no_yes_pool.
      apply (PoolExtendRecv yes_no_protocol
        yes_no_T2
        [⊕ yes_no_question]
        []
        [[⊖ yes_no_question; ⊕ Y]]
        Y).
      - apply (PoolExtendSend yes_no_protocol
          yes_no_T2
          [⊖ yes_no_question]
          [[⊕ yes_no_question]]
          []
          Y).
        + apply PoolBase.
        + exact paper_yes_no_prefix_answerer_yes.
      - unfold event_occurred; simpl; tauto.
      - exact paper_yes_no_prefix_questioner_yes.
    Qed.

    Theorem paper_yes_no_no_pool_reachable_from_T2 :
      yes_no_protocol ⊨ᶠ yes_no_T2 →* yes_no_no_pool.
    Proof.
      unfold yes_no_T2, yes_no_no_pool.
      apply (PoolExtendRecv yes_no_protocol
        yes_no_T2
        [⊕ yes_no_question]
        []
        [[⊖ yes_no_question; ⊕ N]]
        N).
      - apply (PoolExtendSend yes_no_protocol
          yes_no_T2
          [⊖ yes_no_question]
          [[⊕ yes_no_question]]
          []
          N).
        + apply PoolBase.
        + exact paper_yes_no_prefix_answerer_no.
      - unfold event_occurred; simpl; tauto.
      - exact paper_yes_no_prefix_questioner_no.
    Qed.

    (** Composing reachability of [T2] with the yes continuation gives the full
        yes-answer execution from the empty pool. *)
    Theorem paper_yes_no_yes_pool_reachable_via_T2 :
      yes_no_protocol ⊨ yes_no_yes_pool.
    Proof.
      eapply pool_reachable_from_trans.
      - exact paper_yes_no_T2_reachable.
      - exact paper_yes_no_yes_pool_reachable_from_T2.
    Qed.

    Theorem paper_yes_no_no_pool_reachable_via_T2 :
      yes_no_protocol ⊨ yes_no_no_pool.
    Proof.
      eapply pool_reachable_from_trans.
      - exact paper_yes_no_T2_reachable.
      - exact paper_yes_no_no_pool_reachable_from_T2.
    Qed.

    (** Soundness witnesses for the two yes-or-no executions.  These are
        instances of the paper theorem that reachable pools generate bundles
        representing their executed prefixes. *)
    Theorem paper_yes_no_yes_soundness_witness :
      exists G full_trace pool_strand,
        extends_pool_trace yes_no_yes_pool full_trace /\
        IndBundle G /\
        represents_pool G yes_no_yes_pool full_trace pool_strand.
    Proof.
      exact (bundle_of_reachable
        yes_no_protocol yes_no_yes_pool paper_yes_no_yes_pool_reachable).
    Qed.

    Theorem paper_yes_no_no_soundness_witness :
      exists G full_trace pool_strand,
        extends_pool_trace yes_no_no_pool full_trace /\
        IndBundle G /\
        represents_pool G yes_no_no_pool full_trace pool_strand.
    Proof.
      exact (bundle_of_reachable
        yes_no_protocol yes_no_no_pool paper_yes_no_no_pool_reachable).
    Qed.

    Theorem paper_yes_no_yes_computable_witness :
      inhabited (reachable_poolT yes_no_protocol yes_no_yes_pool).
    Proof.
      apply reachable_poolT_inhabited_of_prop.
      exact paper_yes_no_yes_pool_reachable.
    Qed.

    Theorem paper_yes_no_no_computable_witness :
      inhabited (reachable_poolT yes_no_protocol yes_no_no_pool).
    Proof.
      apply reachable_poolT_inhabited_of_prop.
      exact paper_yes_no_no_pool_reachable.
    Qed.

    (** Full-trace functions used to compute concrete bundles from the
        Type-level reachability witnesses below.  Each executed thread is
        already complete in these small examples, so the suffixes are empty. *)
    Definition yes_no_yes_full_trace (i : nat) : list sT :=
      match i with
      | 0 => [⊕ yes_no_question; ⊖ Y]
      | 1 => [⊖ yes_no_question; ⊕ Y]
      | _ => []
      end.

    Definition yes_no_no_full_trace (i : nat) : list sT :=
      match i with
      | 0 => [⊕ yes_no_question; ⊖ N]
      | 1 => [⊖ yes_no_question; ⊕ N]
      | _ => []
      end.

    Lemma yes_no_yes_full_trace_extends :
      extends_pool_trace yes_no_yes_pool yes_no_yes_full_trace.
    Proof.
      unfold extends_pool_trace, yes_no_yes_pool, yes_no_yes_full_trace.
      intros [|[|i]] th Hnth; simpl in Hnth.
      - inversion Hnth; subst. exists []. reflexivity.
      - inversion Hnth; subst. exists []. reflexivity.
      - destruct i; discriminate Hnth.
    Qed.

    Lemma yes_no_no_full_trace_extends :
      extends_pool_trace yes_no_no_pool yes_no_no_full_trace.
    Proof.
      unfold extends_pool_trace, yes_no_no_pool, yes_no_no_full_trace.
      intros [|[|i]] th Hnth; simpl in Hnth.
      - inversion Hnth; subst. exists []. reflexivity.
      - inversion Hnth; subst. exists []. reflexivity.
      - destruct i; discriminate Hnth.
    Qed.

    (** Executable reachability witnesses for the yes and no branches.  Unlike
        the Prop-level reachability proofs, these retain the indexed send
        occurrences used to construct communication edges. *)
    Definition paper_yes_no_yes_poolT :
      reachable_poolT yes_no_protocol yes_no_yes_pool.
    Proof.
      unfold yes_no_yes_pool, yes_no_T2.
      eapply (PoolExtendRecvT yes_no_protocol []
        [⊕ yes_no_question] [] [[⊖ yes_no_question; ⊕ Y]]
        1 1 Y).
      - eapply (PoolExtendSendT yes_no_protocol []
          [⊖ yes_no_question] [[⊕ yes_no_question]] [] Y).
        + eapply (PoolSpawnRecvT yes_no_protocol []
            [[⊕ yes_no_question]] 0 0 yes_no_question).
          * eapply (PoolSpawnSendT yes_no_protocol [] []
              yes_no_question).
            -- apply PoolBaseT.
            -- exact paper_yes_no_prefix_questioner_yes_send.
          * apply (EventAt [[⊕ yes_no_question]] 0 0
              [⊕ yes_no_question] (⊕ yes_no_question));
              reflexivity.
          * exact paper_yes_no_prefix_answerer_common.
        + exact paper_yes_no_prefix_answerer_yes.
      - apply (EventAt
            ([[⊕ yes_no_question]] ++
             [[⊖ yes_no_question; ⊕ Y]])
            1 1
            [⊖ yes_no_question; ⊕ Y]
            (⊕ Y));
          reflexivity.
      - exact paper_yes_no_prefix_questioner_yes.
    Defined.

    Definition paper_yes_no_no_poolT :
      reachable_poolT yes_no_protocol yes_no_no_pool.
    Proof.
      unfold yes_no_no_pool, yes_no_T2.
      eapply (PoolExtendRecvT yes_no_protocol []
        [⊕ yes_no_question] [] [[⊖ yes_no_question; ⊕ N]]
        1 1 N).
      - eapply (PoolExtendSendT yes_no_protocol []
          [⊖ yes_no_question] [[⊕ yes_no_question]] [] N).
        + eapply (PoolSpawnRecvT yes_no_protocol []
            [[⊕ yes_no_question]] 0 0 yes_no_question).
          * eapply (PoolSpawnSendT yes_no_protocol [] []
              yes_no_question).
            -- apply PoolBaseT.
            -- exact paper_yes_no_prefix_questioner_yes_send.
          * apply (EventAt [[⊕ yes_no_question]] 0 0
              [⊕ yes_no_question] (⊕ yes_no_question));
              reflexivity.
          * exact paper_yes_no_prefix_answerer_common.
        + exact paper_yes_no_prefix_answerer_no.
      - apply (EventAt
            ([[⊕ yes_no_question]] ++
             [[⊖ yes_no_question; ⊕ N]])
            1 1
            [⊖ yes_no_question; ⊕ N]
            (⊕ N));
          reflexivity.
      - exact paper_yes_no_prefix_questioner_no.
    Defined.

    (** Labelled version of the yes-answer execution shown in Section 4.5.
        The labels make explicit the nodes created by the four steps and the
        two communication sources:

        - the answerer's receive of the question uses node [(0,0)];
        - the questioner's receive of [Y] uses node [(1,1)].
     *)
    Definition paper_yes_no_yes_labels : list step_label :=
      [
        {| dst := {| ref_thread := 0; ref_index := 0 |};
           ev := ⊕ yes_no_question;
           src := None |};
        {| dst := {| ref_thread := 1; ref_index := 0 |};
           ev := ⊖ yes_no_question;
           src := Some {| ref_thread := 0; ref_index := 0 |} |};
        {| dst := {| ref_thread := 1; ref_index := 1 |};
           ev := ⊕ Y;
           src := None |};
        {| dst := {| ref_thread := 0; ref_index := 1 |};
           ev := ⊖ Y;
           src := Some {| ref_thread := 1; ref_index := 1 |} |}
      ].

    Definition paper_yes_no_yes_labelled_execution :
      { ls : list step_label &
        yes_no_protocol ⊩ᵀ [] -[ ls ]→* yes_no_yes_pool } :=
      reachable_poolT_has_labelsT paper_yes_no_yes_poolT.

    Example paper_yes_no_yes_labelled_execution_labels :
      projT1 paper_yes_no_yes_labelled_execution = paper_yes_no_yes_labels.
    Proof.
      vm_compute.
      reflexivity.
    Qed.

    (** It is possible to display the labelled yes execution and the generated
        labels by running:

<<
Compute paper_yes_no_yes_labelled_execution.
Compute projT1 paper_yes_no_yes_labelled_execution.
Compute paper_yes_no_yes_labels.
>>
     *)

    (** Concrete bundle extracted from the executable yes-branch derivation.
        This is the form to inspect when comparing the Section 4.3 yes trace
        with the bundle construction theorem. *)
    Definition paper_yes_no_yes_computed_bundle : bundle_type :=
      computed_bundle_of
        (bundle_derivation_of_reachableT_with_trace
          yes_no_protocol
          yes_no_yes_pool
          paper_yes_no_yes_poolT
          yes_no_yes_full_trace
          yes_no_yes_full_trace_extends).

    (** Concrete bundle extracted from the executable no-branch derivation.
        Together with [paper_yes_no_yes_computed_bundle], this shows that the
        common pool [T2] can be completed by either branch. *)
    Definition paper_yes_no_no_computed_bundle : bundle_type :=
      computed_bundle_of
        (bundle_derivation_of_reachableT_with_trace
          yes_no_protocol
          yes_no_no_pool
          paper_yes_no_no_poolT
          yes_no_no_full_trace
          yes_no_no_full_trace_extends).

    (** It is possible to display the concrete yes-or-no bundles by running:

<<
Compute paper_yes_no_yes_computed_bundle.
Compute paper_yes_no_no_computed_bundle.
>>
     *)

    (** The computed yes bundle satisfies the same representation property as
        the abstract soundness theorem. *)
    Example paper_yes_no_yes_computed_bundle_sound :
      IndBundle paper_yes_no_yes_computed_bundle /\
      represents_pool_canonical
        paper_yes_no_yes_computed_bundle
        yes_no_yes_pool
        yes_no_yes_full_trace.
    Proof.
      exact (reachable_poolT_computed_bundle_sound
        yes_no_protocol
        yes_no_yes_pool
        paper_yes_no_yes_poolT
        yes_no_yes_full_trace
        yes_no_yes_full_trace_extends).
    Qed.

    (** The computed no bundle satisfies the same representation property as
        the abstract soundness theorem. *)
    Example paper_yes_no_no_computed_bundle_sound :
      IndBundle paper_yes_no_no_computed_bundle /\
      represents_pool_canonical
        paper_yes_no_no_computed_bundle
        yes_no_no_pool
        yes_no_no_full_trace.
    Proof.
      exact (reachable_poolT_computed_bundle_sound
        yes_no_protocol
        yes_no_no_pool
        paper_yes_no_no_poolT
        yes_no_no_full_trace
        yes_no_no_full_trace_extends).
    Qed.

    Local Close Scope paper_yes_no_scope.

  End YesOrNoProtocol.

  (** ** Paper Section 7.3: Concurrent Yahalom worked example *)

  Section ConcurrentYahalom.

    (** Symbolic variables for the Concurrent Yahalom roles in the worked
        example.  They match the paper's role listing: principals [a], [b],
        and [s], nonces [n-a] and [n-b], and the session key [k]. *)
    Let a : tvar S_Name := mkTVar "a".
    Let b : tvar S_Name := mkTVar "b".
    Let s : tvar S_Name := mkTVar "s".
    Let na : tvar S_Text := mkTVar "n-a".
    Let nb : tvar S_Text := mkTVar "n-b".
    Let k : tvar S_Skey := mkTVar "k".
    
    Notation "'A'" := (MkName 0)
      : paper_yahalom_scope.
    Notation "'B'" := (MkName 1)
      : paper_yahalom_scope.
    Notation "'S'" := (MkName 2)
      : paper_yahalom_scope.
    Notation "'Na'" := (MkText 0)
      : paper_yahalom_scope.
    Notation "'Nb'" := (MkText 1)
      : paper_yahalom_scope.
    Notation "'K0'" := (skey 0)
      : paper_yahalom_scope.
    Notation "'M0'" := (M_Skey (skey 0))
      : paper_yahalom_scope.
    Notation "'Ltk' a b" :=
      (M_Skey (EmbeddedTraceStrands.TermNat.ltk a b))
      (at level 31,
       a at level 0,
       b at level 0) : paper_yahalom_scope.
    Notation "'tag1'" := (MkTag 0)
      : paper_yahalom_scope.
    Notation "'tag2'" := (MkTag 1)
      : paper_yahalom_scope.

    Local Open Scope paper_yahalom_scope.

    (** Initiator role from the worked Yahalom example.  The two tags keep the
        peer confirmations distinct. *)
    Definition concurrent_yahalom_init_role : role :=
      DEFROLE "init"
      VARS [
        [a; b; s] IS S_Name;
        [na; nb] IS S_Text;
        [k] IS S_Skey ]
      TRACE
        [ send cat{a; b; na};
          recv enc{a; b; k; na; nb}_(ltk a s);
          send enc{tag1; a; b; na; nb}_k;
          recv enc{tag2; a; b; na; nb}_k ]
      NONORIG
        []
      UNIQORIG
        [].

    (** Responder role, symmetric to the initiator after the first request. *)
    Definition concurrent_yahalom_resp_role : role :=
      DEFROLE "resp"
      VARS [
        [a; b; s] IS S_Name;
        [na; nb] IS S_Text;
        [k] IS S_Skey ]
      TRACE
        [ send cat{a; b; nb};
          recv enc{a; b; k; na; nb}_(ltk b s);
          send enc{tag2; a; b; na; nb}_k;
          recv enc{tag1; a; b; na; nb}_k ]
      NONORIG
        []
      UNIQORIG
        [].

    (** Server role.  The server receives both requests, sends both tickets,
        and uniquely originates the session key [k]. *)
    Definition concurrent_yahalom_serv_role : role :=
      DEFROLE "serv"
      VARS [
        [a; b; s] IS S_Name;
        [na; nb] IS S_Text;
        [k] IS S_Skey ]
      TRACE
        [ recv cat{a; b; na};
          recv cat{a; b; nb};
          send enc{a; b; k; na; nb}_(ltk a s);
          send enc{a; b; k; na; nb}_(ltk b s) ]
      NONORIG
        []
      UNIQORIG
        vars{k}.

    (** The Concurrent Yahalom protocol used in the worked example. *)
    Definition concurrent_yahalom_protocol : protocol :=
      mkProtocol [
        concurrent_yahalom_init_role;
        concurrent_yahalom_resp_role;
        concurrent_yahalom_serv_role
      ].

    Theorem paper_concurrent_yahalom_protocol_well_formed :
      wf_protocol_no_mesg_origination concurrent_yahalom_protocol.
    Proof.
      unfold wf_protocol_no_mesg_origination,
        wf_role_no_mesg_origination,
        concurrent_yahalom_protocol,
      concurrent_yahalom_init_role,
        concurrent_yahalom_resp_role,
        concurrent_yahalom_serv_role.
      simpl.
      intros r [<- | [<- | [<- | []]]]; simpl; firstorder.
    Qed.

    (** Ground atoms for the worked run.  With
        [paper_yahalom_scope] open, the run can use the paper names
        [A], [B], [S], [Na], [Nb], [K0], [tag1], and [tag2]. *)

    (** The valuation instantiating the three symbolic Yahalom roles with the
        concrete run shown in the paper. *)
    Definition concurrent_yahalom_valuation : valuation :=
      eta {{ a := A }}
          {{ b := B }}
          {{ s := S }}
          {{ na := Na }}
          {{ nb := Nb }}
          {{ k := K0 }}.

    (** Ground requests, tickets, and confirmations for the worked execution. *)
    Definition cy_req_a : Mesg :=
      A ⋅ B ⋅ Na.

    Definition cy_req_b : Mesg :=
      A ⋅ B ⋅ Nb.

    Definition cy_tic_a : Mesg :=
      ⟨ A ⋅ B ⋅ M0 ⋅ Na ⋅ Nb ⟩_ Ltk A S.

    Definition cy_tic_b : Mesg :=
      ⟨ A ⋅ B ⋅ M0 ⋅ Na ⋅ Nb ⟩_ Ltk B S.

    Definition cy_conf_a : Mesg :=
      ⟨ tag1 ⋅ A ⋅ B ⋅ Na ⋅ Nb ⟩_ M0.

    Definition cy_conf_b : Mesg :=
      ⟨ tag2 ⋅ A ⋅ B ⋅ Na ⋅ Nb ⟩_ M0.

    (** Final thread traces for the initiator, responder, and server strands
        in the worked example. *)
    Definition cy_init_trace : list sT :=
      [⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a; ⊖ cy_conf_b].

    Definition cy_resp_trace : list sT :=
      [⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b].

    Definition cy_serv_trace : list sT :=
      [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b].

    Definition concurrent_yahalom_pool : thread_pool :=
      [cy_init_trace] ⋈ cy_resp_trace ⋈ [cy_serv_trace].

    (** Intermediate pools from the operational history.  The final pool
        [concurrent_yahalom_pool] is [T11] in the paper. *)
    Definition cy_T1 : thread_pool :=
      [[⊕ cy_req_a]].

    Definition cy_T2 : thread_pool :=
      [[⊕ cy_req_a]] ⋈ [⊕ cy_req_b].

    Definition cy_T3 : thread_pool :=
      [[⊕ cy_req_a]] ⋈ [⊕ cy_req_b] ⋈ [[⊖ cy_req_a]].

    Definition cy_T4 : thread_pool :=
      [[⊕ cy_req_a]] ⋈ [⊕ cy_req_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b]].

    Definition cy_T5 : thread_pool :=
      [[⊕ cy_req_a]] ⋈ [⊕ cy_req_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a]].

    Definition cy_T6 : thread_pool :=
      [[⊕ cy_req_a]] ⋈ [⊕ cy_req_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]].

    Definition cy_T7 : thread_pool :=
      [[⊕ cy_req_a; ⊖ cy_tic_a]] ⋈ [⊕ cy_req_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]].

    Definition cy_T8 : thread_pool :=
      [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]] ⋈ [⊕ cy_req_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]].

    Definition cy_T9 : thread_pool :=
      [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]] ⋈
      [⊕ cy_req_b; ⊖ cy_tic_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]].

    Definition cy_T10 : thread_pool :=
      [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]] ⋈
      [⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b] ⋈
      [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]].

    Ltac cy_prefix role suffix :=
      exists role, concurrent_yahalom_valuation, suffix;
      split; [simpl; auto | vm_compute; reflexivity].

    (** Prefix witnesses used by the operational rules in the Yahalom
        schedule. *)
    Lemma paper_cy_prefix_init_send :
      concurrent_yahalom_protocol ▷ [⊕ cy_req_a].
    Proof.
      cy_prefix concurrent_yahalom_init_role
        [⊖ cy_tic_a; ⊕ cy_conf_a; ⊖ cy_conf_b].
    Qed.

    Lemma paper_cy_prefix_resp_send :
      concurrent_yahalom_protocol ▷ [⊕ cy_req_b].
    Proof.
      cy_prefix concurrent_yahalom_resp_role
        [⊖ cy_tic_b; ⊕ cy_conf_b; ⊖ cy_conf_a].
    Qed.

    Lemma paper_cy_prefix_serv_recv_a :
      concurrent_yahalom_protocol ▷ [⊖ cy_req_a].
    Proof.
      cy_prefix concurrent_yahalom_serv_role
        [⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b].
    Qed.

    Lemma paper_cy_prefix_serv_recv_b :
      concurrent_yahalom_protocol ▷ [⊖ cy_req_a; ⊖ cy_req_b].
    Proof.
      cy_prefix concurrent_yahalom_serv_role
        [⊕ cy_tic_a; ⊕ cy_tic_b].
    Qed.

    Lemma paper_cy_prefix_serv_send_a :
      concurrent_yahalom_protocol ▷
        [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a].
    Proof.
      cy_prefix concurrent_yahalom_serv_role [⊕ cy_tic_b].
    Qed.

    Lemma paper_cy_prefix_serv_send_b :
      concurrent_yahalom_protocol ▷
        [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b].
    Proof.
      cy_prefix concurrent_yahalom_serv_role (@nil sT).
    Qed.

    Lemma paper_cy_prefix_init_recv_ticket :
      concurrent_yahalom_protocol ▷ [⊕ cy_req_a; ⊖ cy_tic_a].
    Proof.
      cy_prefix concurrent_yahalom_init_role
        [⊕ cy_conf_a; ⊖ cy_conf_b].
    Qed.

    Lemma paper_cy_prefix_init_send_conf :
      concurrent_yahalom_protocol ▷
        [⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a].
    Proof.
      cy_prefix concurrent_yahalom_init_role [⊖ cy_conf_b].
    Qed.

    Lemma paper_cy_prefix_resp_recv_ticket :
      concurrent_yahalom_protocol ▷ [⊕ cy_req_b; ⊖ cy_tic_b].
    Proof.
      cy_prefix concurrent_yahalom_resp_role
        [⊕ cy_conf_b; ⊖ cy_conf_a].
    Qed.

    Lemma paper_cy_prefix_resp_send_conf :
      concurrent_yahalom_protocol ▷
        [⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b].
    Proof.
      cy_prefix concurrent_yahalom_resp_role [⊖ cy_conf_a].
    Qed.

    Lemma paper_cy_prefix_init_recv_conf :
      concurrent_yahalom_protocol ▷
        [⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a; ⊖ cy_conf_b].
    Proof.
      cy_prefix concurrent_yahalom_init_role (@nil sT).
    Qed.

    (** The following reachability lemmas formalize the linear schedule in the
        worked example.  This is one schedule compatible with the Yahalom
        bundle; independent events could be swapped, but this order matches
        the displayed sequence [T0], ..., [T11]. *)
    Lemma paper_concurrent_yahalom_T1_reachable :
      concurrent_yahalom_protocol ⊨ cy_T1.
    Proof.
      unfold cy_T1.
      apply (PoolSpawnSend concurrent_yahalom_protocol [] [] (cy_req_a)).
      - constructor.
      - exact paper_cy_prefix_init_send.
    Qed.

    Lemma paper_concurrent_yahalom_T2_reachable :
      concurrent_yahalom_protocol ⊨ cy_T2.
    Proof.
      unfold cy_T2.
      apply (PoolSpawnSend concurrent_yahalom_protocol [] cy_T1 (cy_req_b)).
      - exact paper_concurrent_yahalom_T1_reachable.
      - exact paper_cy_prefix_resp_send.
    Qed.

    Lemma paper_concurrent_yahalom_T3_reachable :
      concurrent_yahalom_protocol ⊨ cy_T3.
    Proof.
      unfold cy_T3.
      apply (PoolSpawnRecv concurrent_yahalom_protocol [] cy_T2 (cy_req_a)).
      - exact paper_concurrent_yahalom_T2_reachable.
      - unfold cy_T2, event_occurred; simpl; auto.
      - exact paper_cy_prefix_serv_recv_a.
    Qed.

    Lemma paper_concurrent_yahalom_T4_reachable :
      concurrent_yahalom_protocol ⊨ cy_T4.
    Proof.
      unfold cy_T4.
      apply (PoolExtendRecv concurrent_yahalom_protocol
        []
        [⊖ cy_req_a]
        [[⊕ cy_req_a]; [⊕ cy_req_b]]
        []
        (cy_req_b)).
      - exact paper_concurrent_yahalom_T3_reachable.
      - unfold event_occurred; simpl; tauto.
      - exact paper_cy_prefix_serv_recv_b.
    Qed.

    Lemma paper_concurrent_yahalom_T5_reachable :
      concurrent_yahalom_protocol ⊨ cy_T5.
    Proof.
      unfold cy_T5.
      apply (PoolExtendSend concurrent_yahalom_protocol
        []
        [⊖ cy_req_a; ⊖ cy_req_b]
        [[⊕ cy_req_a]; [⊕ cy_req_b]]
        []
        (cy_tic_a)).
      - exact paper_concurrent_yahalom_T4_reachable.
      - exact paper_cy_prefix_serv_send_a.
    Qed.

    Lemma paper_concurrent_yahalom_T6_reachable :
      concurrent_yahalom_protocol ⊨ cy_T6.
    Proof.
      unfold cy_T6.
      apply (PoolExtendSend concurrent_yahalom_protocol
        []
        [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a]
        [[⊕ cy_req_a]; [⊕ cy_req_b]]
        []
        (cy_tic_b)).
      - exact paper_concurrent_yahalom_T5_reachable.
      - exact paper_cy_prefix_serv_send_b.
    Qed.

    Lemma paper_concurrent_yahalom_T7_reachable :
      concurrent_yahalom_protocol ⊨ cy_T7.
    Proof.
      unfold cy_T7.
      apply (PoolExtendRecv concurrent_yahalom_protocol
        []
        [⊕ cy_req_a]
        []
        [[⊕ cy_req_b];
         [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
        (cy_tic_a)).
      - exact paper_concurrent_yahalom_T6_reachable.
      - unfold event_occurred; simpl; tauto.
      - exact paper_cy_prefix_init_recv_ticket.
    Qed.

    Lemma paper_concurrent_yahalom_T8_reachable :
      concurrent_yahalom_protocol ⊨ cy_T8.
    Proof.
      unfold cy_T8.
      apply (PoolExtendSend concurrent_yahalom_protocol
        []
        [⊕ cy_req_a; ⊖ cy_tic_a]
        []
        [[⊕ cy_req_b];
         [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
        (cy_conf_a)).
      - exact paper_concurrent_yahalom_T7_reachable.
      - exact paper_cy_prefix_init_send_conf.
    Qed.

    Lemma paper_concurrent_yahalom_T9_reachable :
      concurrent_yahalom_protocol ⊨ cy_T9.
    Proof.
      unfold cy_T9.
      apply (PoolExtendRecv concurrent_yahalom_protocol
        []
        [⊕ cy_req_b]
        [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]]
        [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
        (cy_tic_b)).
      - exact paper_concurrent_yahalom_T8_reachable.
      - unfold event_occurred; simpl; tauto.
      - exact paper_cy_prefix_resp_recv_ticket.
    Qed.

    Lemma paper_concurrent_yahalom_T10_reachable :
      concurrent_yahalom_protocol ⊨ cy_T10.
    Proof.
      unfold cy_T10.
      apply (PoolExtendSend concurrent_yahalom_protocol
        []
        [⊕ cy_req_b; ⊖ cy_tic_b]
        [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]]
        [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
        (cy_conf_b)).
      - exact paper_concurrent_yahalom_T9_reachable.
      - exact paper_cy_prefix_resp_send_conf.
    Qed.

    (** Final Prop-level reachability theorem for the worked Yahalom pool
        [T11]. *)
    Theorem paper_concurrent_yahalom_pool_reachable :
      concurrent_yahalom_protocol ⊨ concurrent_yahalom_pool.
    Proof.
      unfold concurrent_yahalom_pool, cy_init_trace, cy_resp_trace, cy_serv_trace.
      apply (PoolExtendRecv concurrent_yahalom_protocol
        []
        [⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]
        []
        [[⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b];
         [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
        (cy_conf_b)).
      - exact paper_concurrent_yahalom_T10_reachable.
      - unfold event_occurred; simpl; tauto.
      - exact paper_cy_prefix_init_recv_conf.
    Qed.

    (** Soundness instance for the worked example: the reachable pool produces
        an inductive bundle that represents the three executed thread traces. *)
    Theorem paper_concurrent_yahalom_soundness_witness :
      exists G full_trace pool_strand,
        extends_pool_trace concurrent_yahalom_pool full_trace /\
        IndBundle G /\
        represents_pool G concurrent_yahalom_pool full_trace pool_strand.
    Proof.
      exact (bundle_of_reachable
        concurrent_yahalom_protocol
        concurrent_yahalom_pool
        paper_concurrent_yahalom_pool_reachable).
    Qed.

    (** Prop-to-Type bridge for the same execution.  This establishes that a
        witness-carrying reachability derivation exists. *)
    Theorem paper_concurrent_yahalom_computable_witness :
      inhabited
        (reachable_poolT concurrent_yahalom_protocol concurrent_yahalom_pool).
    Proof.
      apply reachable_poolT_inhabited_of_prop.
      exact paper_concurrent_yahalom_pool_reachable.
    Qed.

    (** Full trace assignment used by the computed bundle: thread [0] is the
        initiator, thread [1] the responder, and thread [2] the server. *)
    Definition concurrent_yahalom_full_trace (i : nat) : list sT :=
      match i with
      | 0 => cy_init_trace
      | 1 => cy_resp_trace
      | 2 => cy_serv_trace
      | _ => []
      end.

    Lemma concurrent_yahalom_full_trace_extends :
      extends_pool_trace
        concurrent_yahalom_pool
        concurrent_yahalom_full_trace.
    Proof.
      unfold extends_pool_trace,
        concurrent_yahalom_pool,
        concurrent_yahalom_full_trace.
      intros [|[|[|i]]] th Hnth; simpl in Hnth.
      - inversion Hnth; subst. exists []. reflexivity.
      - inversion Hnth; subst. exists []. reflexivity.
      - inversion Hnth; subst. exists []. reflexivity.
      - destruct i; discriminate Hnth.
    Qed.

    (** Executable reachability witness for the worked schedule.  Each receive
        rule records the indexed send occurrence that becomes a communication
        edge in [paper_concurrent_yahalom_computed_bundle]. *)
    Definition paper_concurrent_yahalom_poolT :
      reachable_poolT concurrent_yahalom_protocol concurrent_yahalom_pool.
    Proof.
      unfold concurrent_yahalom_pool, cy_init_trace, cy_resp_trace, cy_serv_trace.
      eapply (PoolExtendRecvT concurrent_yahalom_protocol []
        [⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]
        []
        [[⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b];
         [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
        1 2 (cy_conf_b)).
      - eapply (PoolExtendSendT concurrent_yahalom_protocol []
          [⊕ cy_req_b; ⊖ cy_tic_b]
          [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]]
          [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
          (cy_conf_b)).
        + eapply (PoolExtendRecvT concurrent_yahalom_protocol []
            [⊕ cy_req_b]
            [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a]]
            [[⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
            2 3 (cy_tic_b)).
          * eapply (PoolExtendSendT concurrent_yahalom_protocol []
              [⊕ cy_req_a; ⊖ cy_tic_a]
              []
              [[⊕ cy_req_b];
               [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
              (cy_conf_a)).
            -- eapply (PoolExtendRecvT concurrent_yahalom_protocol []
                [⊕ cy_req_a]
                []
                [[⊕ cy_req_b];
                 [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
                2 2 (cy_tic_a)).
               ++ eapply (PoolExtendSendT concurrent_yahalom_protocol []
                   [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a]
                   [[⊕ cy_req_a]; [⊕ cy_req_b]]
                   []
                   (cy_tic_b)).
                  ** eapply (PoolExtendSendT concurrent_yahalom_protocol []
                       [⊖ cy_req_a; ⊖ cy_req_b]
                       [[⊕ cy_req_a]; [⊕ cy_req_b]]
                       []
                       (cy_tic_a)).
                     --- eapply (PoolExtendRecvT concurrent_yahalom_protocol []
                           [⊖ cy_req_a]
                           [[⊕ cy_req_a]; [⊕ cy_req_b]]
                           []
                           1 0 (cy_req_b)).
                         +++ eapply (PoolSpawnRecvT
                               concurrent_yahalom_protocol []
                               cy_T2 0 0 (cy_req_a)).
                             *** eapply (PoolSpawnSendT
                                   concurrent_yahalom_protocol []
                                   cy_T1 (cy_req_b)).
                                 ---- eapply (PoolSpawnSendT
                                        concurrent_yahalom_protocol []
                                        [] (cy_req_a)).
                                      ++++ apply PoolBaseT.
                                      ++++ exact paper_cy_prefix_init_send.
                                 ---- exact paper_cy_prefix_resp_send.
                             *** unfold cy_T2.
                                 apply (EventAt
                                   [[⊕ cy_req_a]; [⊕ cy_req_b]]
                                   0 0 [⊕ cy_req_a] (⊕ cy_req_a));
                                   reflexivity.
                             *** exact paper_cy_prefix_serv_recv_a.
                         +++ unfold cy_T3.
                             apply (EventAt
                               [[⊕ cy_req_a]; [⊕ cy_req_b]; [⊖ cy_req_a]]
                               1 0 [⊕ cy_req_b] (⊕ cy_req_b));
                               reflexivity.
                         +++ exact paper_cy_prefix_serv_recv_b.
                     --- exact paper_cy_prefix_serv_send_a.
                  ** exact paper_cy_prefix_serv_send_b.
               ++ unfold cy_T6.
                  apply (EventAt
                    [[⊕ cy_req_a]; [⊕ cy_req_b];
                     [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
                    2 2
                    [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]
                    (⊕ cy_tic_a));
                    reflexivity.
               ++ exact paper_cy_prefix_init_recv_ticket.
            -- exact paper_cy_prefix_init_send_conf.
          * unfold cy_T8.
            apply (EventAt
              [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a];
               [⊕ cy_req_b];
               [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
              2 3
              [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]
              (⊕ cy_tic_b));
              reflexivity.
          * exact paper_cy_prefix_resp_recv_ticket.
        + exact paper_cy_prefix_resp_send_conf.
      - unfold cy_T10.
        apply (EventAt
          [[⊕ cy_req_a; ⊖ cy_tic_a; ⊕ cy_conf_a];
           [⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b];
           [⊖ cy_req_a; ⊖ cy_req_b; ⊕ cy_tic_a; ⊕ cy_tic_b]]
          1 2
          [⊕ cy_req_b; ⊖ cy_tic_b; ⊕ cy_conf_b]
          (⊕ cy_conf_b));
          reflexivity.
      - exact paper_cy_prefix_init_recv_conf.
    Defined.

    (** Bundle computed from the executable Concurrent Yahalom reachability
        witness.  This is the concrete bundle used for the worked example in
        Section 7.3: the thread pool supplies the strands, and the indexed
        receives in [paper_concurrent_yahalom_poolT] supply the communication
        edges. *)
    Definition paper_concurrent_yahalom_computed_bundle : bundle_type :=
      computed_bundle_of
        (bundle_derivation_of_reachableT_with_trace
          concurrent_yahalom_protocol
          concurrent_yahalom_pool
          paper_concurrent_yahalom_poolT
          concurrent_yahalom_full_trace
          concurrent_yahalom_full_trace_extends).

    (** It is possible to display the concrete Yahalom bundle by running:

<<
    Compute paper_concurrent_yahalom_computed_bundle.
>>
*)

    (** Named strands used to state the Section 7.3 edge set in the same
        initiator/responder/server terminology as the paper. *)
    Definition cy_init_strand : Σ := (0, cy_init_trace).
    Definition cy_resp_strand : Σ := (1, cy_resp_trace).
    Definition cy_serv_strand : Σ := (2, cy_serv_trace).

    (** Section 7.3 communication edges computed from the executable
        reachability witness.  They are listed in reverse construction order,
        because each new receive edge is consed onto the bundle edge list. *)
    Example paper_concurrent_yahalom_computed_bundle_inter_edges :
      inter paper_concurrent_yahalom_computed_bundle = [
        ((cy_resp_strand, 2), (cy_init_strand, 3));
        ((cy_serv_strand, 3), (cy_resp_strand, 1));
        ((cy_serv_strand, 2), (cy_init_strand, 1));
        ((cy_resp_strand, 0), (cy_serv_strand, 1));
        ((cy_init_strand, 0), (cy_serv_strand, 0))
      ].
    Proof.
      reflexivity.
    Qed.

    (** The computed Yahalom bundle satisfies the canonical representation
        property promised by the bundle soundness theorem. *)
    Example paper_concurrent_yahalom_computed_bundle_sound :
      IndBundle paper_concurrent_yahalom_computed_bundle /\
      represents_pool_canonical
        paper_concurrent_yahalom_computed_bundle
        concurrent_yahalom_pool
        concurrent_yahalom_full_trace.
    Proof.
      exact (reachable_poolT_computed_bundle_sound
        concurrent_yahalom_protocol
        concurrent_yahalom_pool
        paper_concurrent_yahalom_poolT
        concurrent_yahalom_full_trace
        concurrent_yahalom_full_trace_extends).
    Qed.

    (** The definitions above are the documentable endpoints for the worked
        example: [paper_concurrent_yahalom_computed_bundle] is the ground
        bundle, [paper_concurrent_yahalom_computed_bundle_inter_edges] records
        its communication edges, and
        [paper_concurrent_yahalom_computed_bundle_sound] checks that the
        computed object represents the final pool [T11]. *)
    Local Close Scope paper_yahalom_scope.
  End ConcurrentYahalom.

End PaperExamples.
