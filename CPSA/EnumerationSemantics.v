From Stdlib Require Import List ListSet Lia Arith.PeanoNat.
Import ListNotations.

From strandsrocq.Common Require Import Enumerate BundleSizeInductionFixed.
From strandsrocq.CPSA Require Import
  RoleSyntax ChoiceRoles Semantics ComputableSemantics LabelledSemantics.
From strandsrocq.CPSA.Instances Require Import DefaultInstances.

Import CPSA_Direct_Syntax.
Import ChoiceRoles.
Import CPSA_Semantics.
Import CPSA_Computable_Semantics.
Import CPSA_Labelled_Semantics.

Module BundleSinkInduction := BundleSizeInductionFixed
  strandsrocq.CPSA.Instances.EmbeddedTraceStrands.TermNat
  strandsrocq.CPSA.Instances.EmbeddedTraceStrands.EmbeddedTraceInstance.EmbeddedTraceStrands
  strandsrocq.CPSA.Instances.EmbeddedTraceStrands.EmbeddedTraceInstance.EmbeddedTraceStrandSpace
  strandsrocq.CPSA.Instances.DefaultInstances.DefaultInstance.BundleInstance
  strandsrocq.CPSA.Instances.DefaultInstances.DefaultInstance.BundleInductiveInstance.

Open Scope list_scope.
Open Scope cpsa_direct_syntax_scope.

(** * Compatible enumerations and labelled executions

    This file proves the scheduling conjecture from the paper without changing
    the general enumeration and sink-induction developments.  An enumeration
    is represented in the direction [nat -> node]: [f i] is the node scheduled
    at position [i]. *)
Module CPSA_Enumeration_Semantics.

  Definition causal_lt (B : bundle_type) (n n' : node__t) : Prop :=
    edges B ⊢ n ≺ n'.

  Definition compatible_bundle_enumeration
    (B : bundle_type) (f : nat -> node__t) : Prop :=
    Enumerate.compat_enum (causal_lt B) f (nodes B).

  Definition remove_sink_node := BundleSinkInduction.remove_node.

  Lemma compatible_bundle_enumeration_nodup :
    forall B f,
      compatible_bundle_enumeration B f ->
      NoDup (nodes B).
  Proof.
    intros B f Hcompat.
    unfold compatible_bundle_enumeration in Hcompat.
    now apply (Enumerate.compat_enum_nodups eq_node__t_dec) in Hcompat.
  Qed.

  Lemma compatible_last_in :
    forall B f k,
      compatible_bundle_enumeration B f ->
      length (nodes B) = S k ->
      In (f k) (nodes B).
  Proof.
    intros B f k [_ Henum] Hlen.
    eapply Enumerate.enumerates_in.
    - exact Henum.
    - lia.
  Qed.

  Lemma compatible_last_is_sink :
    forall B f k,
      is_bundle B ->
      compatible_bundle_enumeration B f ->
      length (nodes B) = S k ->
      sink (f k) B.
  Proof.
    intros B f k Hbundle [Hcompat Henum] Hlen.
    split.
    - unfold is_node_of.
      eapply Enumerate.enumerates_in; eauto; lia.
    - intros n Hn Hneq Hle.
      apply bundle_le_then_lt in Hle as [Heq | Hlt].
      + now apply Hneq.
      + destruct (Enumerate.enumerates_exists_index n Henum Hn)
          as [j [Hj Hfj]].
        subst n.
        specialize (Hcompat k j ltac:(lia) Hj Hlt).
        lia.
  Qed.

  Lemma remove_sink_node_is_bundle :
    forall B f m,
      is_bundle B ->
      compatible_bundle_enumeration B f ->
      sink m B ->
      is_bundle (remove_sink_node m B).
  Proof.
    intros B f m Hbundle Hcompat Hsink.
    unfold remove_sink_node.
    eapply is_bundle_remove_sink; eauto.
    now apply compatible_bundle_enumeration_nodup with (f := f).
  Qed.

  Lemma remove_sink_node_length :
    forall B f m,
      compatible_bundle_enumeration B f ->
      In m (nodes B) ->
      S (length (nodes (remove_sink_node m B))) = length (nodes B).
  Proof.
    intros B f m Hcompat Hm.
    unfold remove_sink_node; simpl.
    rewrite <- Enumerate.list_remove_eq_set_remove.
    apply Enumerate.remove_length_pred.
    - now apply compatible_bundle_enumeration_nodup with (f := f).
    - exact Hm.
    - now apply compatible_bundle_enumeration_nodup with (f := f).
  Qed.

  Lemma removed_causal_lt_incl :
    forall B m n n',
      causal_lt (remove_sink_node m B) n n' ->
      causal_lt B n n'.
  Proof.
    intros B m n n' Hlt.
    unfold causal_lt, remove_sink_node, edges in *; simpl in *.
    eapply bundle_lt_incl; [| exact Hlt].
    intros e He.
    apply set_union_iff in He as [He | He]; apply set_union_iff.
    - left. now apply remove_edges_to_iff in He as [He _].
    - right. now apply remove_edges_to_iff in He as [He _].
  Qed.

  Lemma compatible_remove_last :
    forall B f k,
      compatible_bundle_enumeration B f ->
      length (nodes B) = S k ->
      compatible_bundle_enumeration
        (remove_sink_node (f k) B)
        (Enumerate.omit_at f k).
  Proof.
    intros B f k Hcompat Hlen.
    assert (Hlast : In (f k) (nodes B)).
    { now apply compatible_last_in with (f := f) (k := k). }
    assert (Hnodup : NoDup (nodes B)).
    { now apply compatible_bundle_enumeration_nodup with (f := f). }
    assert (Hk : k < length (nodes B)) by lia.
    pose proof (Enumerate.compat_enum_omit eq_node__t_dec Hcompat Hk)
      as Homit.
    unfold compatible_bundle_enumeration in *.
    destruct Homit as [Horder Henum].
    rewrite Enumerate.list_remove_eq_set_remove in Horder, Henum
      by exact Hnodup.
    split.
    - unfold Enumerate.is_compatible in *.
      intros i j Hi Hj Hlt.
      apply Horder.
      + exact Hi.
      + unfold remove_sink_node in Hj; simpl in Hj. exact Hj.
      + now apply removed_causal_lt_incl in Hlt.
    - unfold remove_sink_node; simpl.
      exact Henum.
  Qed.

  Lemma map_labels_snoc_enum :
    forall st ls l f k,
      map (label_dst st) ls =
        Enumerate.list_of_enum (Enumerate.omit_at f k) k ->
      label_dst st l = f k ->
      map (label_dst st) (ls ++ [l]) =
        Enumerate.list_of_enum f (S k).
  Proof.
    intros st ls l f k Hmap Hlast.
    rewrite map_app, Hmap. simpl. rewrite Hlast.
    now rewrite Enumerate.list_of_enum_omit_last.
  Qed.

  Definition enumeration_has_execution
    (B : bundle_type) (P : protocol) (f : nat -> node__t) : Prop :=
    exists T full_trace pool_strand ls,
      inhabited (P ⊩ᵀ [] -[ ls ]→* T) /\
      extends_pool_trace T full_trace /\
      represents_pool B T full_trace pool_strand /\
      map (label_dst pool_strand) ls =
        Enumerate.list_of_enum f (length (nodes B)).

  Lemma enumeration_execution_snoc :
    forall B P f k T T' full_trace pool_strand ls l,
      length (nodes B) = S k ->
      P ⊩ᵀ [] -[ ls ]→* T ->
      P ⊩ᵀ T -[ l ]→ T' ->
      extends_pool_trace T' full_trace ->
      represents_pool B T' full_trace pool_strand ->
      map (label_dst pool_strand) ls =
        Enumerate.list_of_enum (Enumerate.omit_at f k) k ->
      label_dst pool_strand l = f k ->
      enumeration_has_execution B P f.
  Proof.
    intros B P f k T T' full_trace pool_strand ls l
      Hlen Hreach Hstep Hext Hrepr Hmap Hlast.
    exists T', full_trace, pool_strand, (ls ++ [l]).
    split.
    - constructor.
      eapply labelled_reachableT_snoc; eauto.
    - split; [exact Hext |].
      split; [exact Hrepr |].
      rewrite Hlen.
      now apply map_labels_snoc_enum.
  Qed.

  Lemma same_nodes_after_remove :
    forall B f m,
      compatible_bundle_enumeration B f ->
      In m (nodes B) ->
      SameSet (nodes B) (m :: nodes (remove_sink_node m B)).
  Proof.
    intros B f m Hcompat Hm.
    unfold remove_sink_node; simpl.
    eapply SameSet_remove_cons_node.
    - exact Hm.
    - now apply compatible_bundle_enumeration_nodup with (f := f).
    - intros q. reflexivity.
  Qed.

  Lemma removed_node_fresh :
    forall B f m,
      compatible_bundle_enumeration B f ->
      ~ In m (nodes (remove_sink_node m B)).
  Proof.
    intros B f m Hcompat.
    unfold remove_sink_node; simpl.
    intro Hin.
    apply set_remove_node_iff in Hin.
    - tauto.
    - now apply compatible_bundle_enumeration_nodup with (f := f).
  Qed.

  Lemma represented_added_node_to_original :
    forall B B0 m T full_trace pool_strand,
      SameSet (nodes B) (m :: nodes B0) ->
      represents_pool
        {| nodes := m :: nodes B0;
           intra := intra B0;
           inter := inter B0 |}
        T full_trace pool_strand ->
      represents_pool B T full_trace pool_strand.
  Proof.
    intros B B0 m T full_trace pool_strand Hsame Hrepr.
    eapply represents_pool_change_nodes; [| exact Hrepr].
    intros q. symmetry. apply Hsame.
  Qed.

  Theorem compatible_enumeration_has_labelled_execution_tau :
    forall B P f,
      is_bundle B ->
      ofProtocol B P ->
      tau_non_originating B ->
      compatible_bundle_enumeration B f ->
      enumeration_has_execution B P f.
  Proof.
    assert (Hempty :
      forall B P f,
        nodes B = [] ->
        enumeration_has_execution B P f).
    { intros B P f Hnodes.
      exists [], (fun _ => []), (fun _ => (0, [])), [].
      split.
      - constructor. constructor.
      - split.
        + unfold extends_pool_trace.
          intros i th Hnth. destruct i; discriminate.
        + split.
          * unfold represents_pool, is_node_of, set_In.
            intros q. rewrite Hnodes. simpl. split; try contradiction.
            intros [i [th [suffix [Hnth _]]]]. destruct i; discriminate.
          * now rewrite Hnodes. }
    assert (Haux :
      forall B,
        NoDup (nodes B) ->
        is_bundle B ->
        forall P f,
          ofProtocol B P ->
          tau_non_originating B ->
          compatible_bundle_enumeration B f ->
          enumeration_has_execution B P f).
    {
      eapply (@BundleSinkInduction.bundle_sink_induction
        (fun B => forall P f,
          ofProtocol B P ->
          tau_non_originating B ->
          compatible_bundle_enumeration B f ->
          enumeration_has_execution B P f)).
      intros B Hnodup Hbundle IH P f Hproto Htau Hcompat.
      destruct (nodes B) as [|a N] eqn:Hnodes.
        + now apply Hempty.
        + assert (Hlen : length (nodes B) = S (length N)).
        { rewrite Hnodes. reflexivity. }
        set (last := length N).
        remember (f last) as m eqn:Hmdef.
        assert (Hm : In m (nodes B)).
        { rewrite Hmdef. unfold last. eapply compatible_last_in; eauto. }
        assert (Hsink : sink m B).
        { rewrite Hmdef. unfold last. eapply compatible_last_is_sink; eauto. }
        set (B0 := remove_sink_node m B).
        set (f0 := Enumerate.omit_at f last).
        assert (Hbundle0 : is_bundle B0).
        { unfold B0. exact (remove_sink_node_is_bundle
            B f m Hbundle Hcompat Hsink). }
        assert (Hcompat0 : compatible_bundle_enumeration B0 f0).
        { unfold B0, f0. rewrite Hmdef. unfold last.
          now eapply compatible_remove_last. }
        assert (Hlen_last : length (nodes B0) = last).
        { unfold B0, last.
          pose proof (remove_sink_node_length B f m Hcompat Hm).
          lia. }
        assert (Hproto0 : ofProtocol B0 P).
        { intros q Hq. apply Hproto.
          unfold B0, remove_sink_node in Hq. simpl in Hq.
          apply set_remove_node_iff in Hq.
          - tauto.
          - now apply compatible_bundle_enumeration_nodup with (f := f). }
        assert (Htau0 : tau_non_originating B0).
        { intros q Hq Horig. apply (Htau q).
          - unfold B0, remove_sink_node in Hq. simpl in Hq.
            apply set_remove_node_iff in Hq.
            + tauto.
            + now apply compatible_bundle_enumeration_nodup with (f := f).
          - exact Horig. }
        destruct (IH m Hsink P f0 Hproto0 Htau0 Hcompat0)
          as [T [full_trace [pool_strand [ls [Hlabel [Hext [Hrepr Hmap]]]]]]].
        change (map (label_dst pool_strand) ls =
          Enumerate.list_of_enum f0 (length (nodes B0))) in Hmap.
        assert (Hfresh : ~ In m (nodes B0)).
        { unfold B0. now apply removed_node_fresh with (f := f). }
        assert (Hsame : SameSet (nodes B) (m :: nodes B0)).
        { unfold B0. now apply same_nodes_after_remove with (f := f). }
        assert (Hbounds : index m < length (tr (strand m))).
        { exact (bundle_node_in_bounds_without_tau_origin
            B m Hbundle Htau Hm). }
        destruct Hlabel as [Hlabel].
        destruct m as [s i].
        destruct (term (s, i)) as [msg | msg] eqn:Hterm.
        * destruct i as [|i].
          -- assert (Htrace : traceAtNode (s, 0) = [⊕ msg]).
            { eapply traceAtNode_zero; eauto. }
            assert (Hprefix : P ▷ [⊕ msg]).
            { specialize (Hproto (s, 0) Hm). now rewrite Htrace in Hproto. }
            set (new_full :=
              fun j => if Nat.eq_dec j (length T)
                       then tr (strand (s, 0)) else full_trace j).
            set (new_strand :=
              fun j => if Nat.eq_dec j (length T)
                       then strand (s, 0) else pool_strand j).
            assert (Hfull_new :
              tr (strand (s, 0)) =
                [⊕ msg] ++ skipn 1 (tr (strand (s, 0)))).
            { rewrite <- (firstn_skipn 1 (tr (strand (s, 0)))) at 1.
              replace (firstn 1 (tr (strand (s, 0))))
                with (traceAtNode (s, 0)).
              - now rewrite Htrace.
              - unfold traceAtNode. reflexivity. }
            set (lab :=
              {| dst := {| ref_thread := length T; ref_index := 0 |};
                 ev := ⊕ msg; src := None |}).
            assert (Hstep :
              P ⊩ᵀ T -[ lab ]→ T ⋈ [⊕ msg]).
            { unfold lab. now apply TLSpawnSend. }
            eapply enumeration_execution_snoc with
              (k := last) (T := T) (full_trace := new_full)
              (pool_strand := new_strand) (l := lab).
            --- unfold last. exact Hlen.
            --- exact Hlabel.
            --- exact Hstep.
            --- unfold new_full.
                now apply (extends_pool_trace_spawn_any
                  T full_trace (tr (strand (s, 0))) (⊕ msg)).
            --- eapply represented_added_node_to_original; [exact Hsame |].
                unfold new_full, new_strand.
                eapply represents_pool_spawn_any; eauto.
            --- unfold f0 in Hmap. rewrite Hlen_last in Hmap.
                rewrite <- Hmap.
                eapply map_label_dst_reachable_ext; [exact Hlabel |].
                intros j Hj. unfold new_strand.
                destruct (Nat.eq_dec j (length T)); try lia; reflexivity.
            --- unfold label_dst, node_of_ref, lab, new_strand.
                simpl. destruct (Nat.eq_dec (length T) (length T));
                  try contradiction. exact Hmdef.
          -- pose (pred := (s, i)).
            assert (Hpred_edge : pred ⟹ (s, S i)).
            { unfold pred, intrastrand. simpl. now rewrite Nat.add_1_r. }
            pose proof Hbundle as Hparts.
            destruct Hparts as
              [[HsubL [HsubC [HnodesL HnodesC]]]
                [Hinter [Hintra Hacyclic]]].
            assert (Hpred_edge_in : In (pred, (s, S i)) (intra B)).
            { now apply Hintra. }
            assert (Hpred_B : In pred (nodes B)).
            { apply HnodesL. exists (s, S i). now left. }
            assert (Hpred_neq : pred <> (s, S i)).
            { unfold pred. intros Heq. inversion Heq. lia. }
            assert (Hpred_B0 : In pred (nodes B0)).
            { unfold B0, remove_sink_node; simpl.
              apply set_remove_node_iff.
              - now apply compatible_bundle_enumeration_nodup with (f := f).
              - split; [exact Hpred_B |].
                intro Heq. apply Hpred_neq. now rewrite Heq, Hmdef. }
            destruct (proj1 (Hrepr pred) Hpred_B0) as
              [thread_i [th [suffix
                [Hnth [Hstrand_pred [Htr [Hfull Hlt]]]]]]].
            assert (Hstrand_m : strand (s, S i) = pool_strand thread_i).
            { unfold pred in Hstrand_pred. simpl in *. exact Hstrand_pred. }
            assert (Hthread_len : length th = index (s, S i)).
            { eapply represented_thread_stops_before_fresh_successor;
                eauto. }
            assert (Htrace : traceAtNode (s, S i) = th ++ [⊕ msg]).
            { eapply traceAtNode_from_represented_successor; eauto. }
            assert (Hfull_new :
              exists suffix', full_trace thread_i = (th ++ [⊕ msg]) ++ suffix').
            { eapply full_trace_from_represented_successor; eauto. }
            assert (Hprefix : P ▷ th ++ [⊕ msg]).
            { specialize (Hproto (s, S i) Hm). now rewrite Htrace in Hproto. }
            destruct (@nth_error_split thread T thread_i th Hnth)
              as [T1 [T2 [HT Hthread_i]]].
            subst thread_i.
            assert (Hext_new :
              extends_pool_trace (T1 ⋈ (th ++ [⊕ msg]) ⋈ T2) full_trace).
            { apply (extends_pool_trace_extend_any
                T1 th T2 full_trace (⊕ msg)).
              - replace (T1 ⋈ th ⋈ T2) with T
                  by (rewrite HT; reflexivity).
                exact Hext.
              - exact Hfull_new. }
            set (lab :=
              {| dst := {| ref_thread := length T1; ref_index := length th |};
                 ev := ⊕ msg; src := None |}).
            assert (Hstep :
              P ⊩ᵀ (T1 ⋈ th ⋈ T2) -[ lab ]→
                T1 ⋈ (th ++ [⊕ msg]) ⋈ T2).
            { unfold lab. now apply TLExtendSend. }
            assert (Hlabel_split :
              P ⊩ᵀ [] -[ ls ]→* (T1 ⋈ th ⋈ T2)).
            { replace (T1 ⋈ th ⋈ T2) with T
                by (rewrite HT; reflexivity).
              exact Hlabel. }
            assert (Hrepr_split :
              represents_pool B0 (T1 ⋈ th ⋈ T2)
                full_trace pool_strand).
            { replace (T1 ⋈ th ⋈ T2) with T
                by (rewrite HT; reflexivity).
              exact Hrepr. }
            eapply enumeration_execution_snoc with
              (k := last) (T := T1 ⋈ th ⋈ T2)
              (full_trace := full_trace) (pool_strand := pool_strand)
              (l := lab).
            --- unfold last. exact Hlen.
            --- exact Hlabel_split.
            --- exact Hstep.
            --- exact Hext_new.
            --- eapply represented_added_node_to_original; [exact Hsame |].
                eapply represents_pool_extend_any.
                +++ exact Hrepr_split.
                +++ exact Hext_new.
                +++ exact Hfresh.
                +++ exact Hstrand_m.
                +++ exact Htr.
                +++ symmetry. exact Hthread_len.
            --- unfold f0 in Hmap. rewrite Hlen_last in Hmap. exact Hmap.
            --- unfold label_dst, node_of_ref, lab. simpl.
                rewrite <- Hmdef, <- Hstrand_m, Hthread_len.
                reflexivity.
        * pose proof Hbundle as Hparts.
          destruct Hparts as
            [[HsubL [HsubC [HnodesL HnodesC]]]
              [Hinter [Hintra Hacyclic]]].
          assert (Hneg : is_negative (s, i)).
          { unfold is_negative. now rewrite Hterm. }
          destruct (Hinter (s, i) Hm Hneg) as
            [src [Hsrc_edge Hsrc_unique]].
          assert (Hsrc_B : In src (nodes B)).
          { apply HnodesC. exists (s, i). now left. }
          assert (Hinter_edge : src ⟶ (s, i)).
          { now apply HsubC. }
          assert (Hsrc_neq : src <> (s, i)).
          { pose proof Hinter_edge as Hsign.
            apply interstrand_sign in Hsign as [Hpos_src Hneg_m].
            intro Heq. subst src.
            now apply (node_neg_pos_neq Hpos_src Hneg_m). }
          assert (Hsrc_B0 : In src (nodes B0)).
          { unfold B0, remove_sink_node; simpl.
            apply set_remove_node_iff.
            - now apply compatible_bundle_enumeration_nodup with (f := f).
            - split; [exact Hsrc_B |].
              intro Heq. apply Hsrc_neq. now rewrite Heq, Hmdef. }
          unfold interstrand in Hinter_edge.
          rewrite Hterm in Hinter_edge.
          destruct (term src) as [src_msg | src_msg] eqn:Hterm_src;
            try contradiction.
          subst src_msg.
          assert (Hocc : event_occurred T (⊕ msg)).
          { eapply represented_node_event_occurred; eauto. }
          destruct (event_at_inhabited_of_occurred T (⊕ msg) Hocc) as
            [[src_i [src_j Hindexed]]].
          destruct i as [|i].
          -- assert (Htrace : traceAtNode (s, 0) = [⊖ msg]).
             { eapply traceAtNode_zero; eauto. }
             assert (Hprefix : P ▷ [⊖ msg]).
             { specialize (Hproto (s, 0) Hm). now rewrite Htrace in Hproto. }
             set (new_full :=
               fun j => if Nat.eq_dec j (length T)
                        then tr (strand (s, 0)) else full_trace j).
             set (new_strand :=
               fun j => if Nat.eq_dec j (length T)
                        then strand (s, 0) else pool_strand j).
             assert (Hfull_new :
               tr (strand (s, 0)) =
                 [⊖ msg] ++ skipn 1 (tr (strand (s, 0)))).
             { rewrite <- (firstn_skipn 1 (tr (strand (s, 0)))) at 1.
               replace (firstn 1 (tr (strand (s, 0))))
                 with (traceAtNode (s, 0)).
               - now rewrite Htrace.
               - unfold traceAtNode. reflexivity. }
             set (lab :=
               {| dst := {| ref_thread := length T; ref_index := 0 |};
                  ev := ⊖ msg;
                  src := Some {| ref_thread := src_i; ref_index := src_j |} |}).
             assert (Hstep :
               P ⊩ᵀ T -[ lab ]→ T ⋈ [⊖ msg]).
             { unfold lab. now eapply TLSpawnRecv. }
             eapply enumeration_execution_snoc with
               (k := last) (T := T) (full_trace := new_full)
               (pool_strand := new_strand) (l := lab).
             --- unfold last. exact Hlen.
             --- exact Hlabel.
             --- exact Hstep.
             --- unfold new_full.
                 now apply (extends_pool_trace_spawn_any
                   T full_trace (tr (strand (s, 0))) (⊖ msg)).
             --- eapply represented_added_node_to_original; [exact Hsame |].
                 unfold new_full, new_strand.
                 eapply represents_pool_spawn_any; eauto.
             --- unfold f0 in Hmap. rewrite Hlen_last in Hmap.
                 rewrite <- Hmap.
                 eapply map_label_dst_reachable_ext; [exact Hlabel |].
                 intros j Hj. unfold new_strand.
                 destruct (Nat.eq_dec j (length T)); try lia; reflexivity.
             --- unfold label_dst, node_of_ref, lab, new_strand.
                 simpl.
                 destruct (Nat.eq_dec (length T) (length T));
                   try contradiction.
                 exact Hmdef.
          -- pose (pred := (s, i)).
             assert (Hpred_edge : pred ⟹ (s, S i)).
             { unfold pred, intrastrand. simpl. now rewrite Nat.add_1_r. }
             assert (Hpred_edge_in : In (pred, (s, S i)) (intra B)).
             { now apply Hintra. }
             assert (Hpred_B : In pred (nodes B)).
             { apply HnodesL. exists (s, S i). now left. }
             assert (Hpred_neq : pred <> (s, S i)).
             { unfold pred. intros Heq. inversion Heq. lia. }
             assert (Hpred_B0 : In pred (nodes B0)).
             { unfold B0, remove_sink_node; simpl.
               apply set_remove_node_iff.
               - now apply compatible_bundle_enumeration_nodup with (f := f).
               - split; [exact Hpred_B |].
                 intro Heq. apply Hpred_neq. now rewrite Heq, Hmdef. }
             destruct (proj1 (Hrepr pred) Hpred_B0) as
               [thread_i [th [suffix
                 [Hnth [Hstrand_pred [Htr [Hfull Hlt]]]]]]].
             assert (Hstrand_m : strand (s, S i) = pool_strand thread_i).
             { unfold pred in Hstrand_pred. simpl in *. exact Hstrand_pred. }
             assert (Hthread_len : length th = index (s, S i)).
             { eapply represented_thread_stops_before_fresh_successor;
                 eauto. }
             assert (Htrace : traceAtNode (s, S i) = th ++ [⊖ msg]).
             { eapply traceAtNode_from_represented_successor; eauto. }
             assert (Hfull_new :
               exists suffix', full_trace thread_i = (th ++ [⊖ msg]) ++ suffix').
             { eapply full_trace_from_represented_successor; eauto. }
             assert (Hprefix : P ▷ th ++ [⊖ msg]).
             { specialize (Hproto (s, S i) Hm). now rewrite Htrace in Hproto. }
             destruct (@nth_error_split thread T thread_i th Hnth)
               as [T1 [T2 [HT Hthread_i]]].
             subst thread_i.
             assert (Hext_new :
               extends_pool_trace (T1 ⋈ (th ++ [⊖ msg]) ⋈ T2) full_trace).
             { apply (extends_pool_trace_extend_any
                 T1 th T2 full_trace (⊖ msg)).
               - replace (T1 ⋈ th ⋈ T2) with T
                   by (rewrite HT; reflexivity).
                 exact Hext.
               - exact Hfull_new. }
             assert (Hindexed_split :
               T1 ⋈ th ⋈ T2 ↓[src_i,src_j] ⊕ msg).
             { replace (T1 ⋈ th ⋈ T2) with T
                 by (rewrite HT; reflexivity).
               exact Hindexed. }
             set (lab :=
               {| dst := {| ref_thread := length T1; ref_index := length th |};
                  ev := ⊖ msg;
                  src := Some {| ref_thread := src_i; ref_index := src_j |} |}).
             assert (Hstep :
               P ⊩ᵀ (T1 ⋈ th ⋈ T2) -[ lab ]→
                 T1 ⋈ (th ++ [⊖ msg]) ⋈ T2).
             { unfold lab. now eapply TLExtendRecv. }
             assert (Hlabel_split :
               P ⊩ᵀ [] -[ ls ]→* (T1 ⋈ th ⋈ T2)).
             { replace (T1 ⋈ th ⋈ T2) with T
                 by (rewrite HT; reflexivity).
               exact Hlabel. }
             assert (Hrepr_split :
               represents_pool B0 (T1 ⋈ th ⋈ T2)
                 full_trace pool_strand).
             { replace (T1 ⋈ th ⋈ T2) with T
                 by (rewrite HT; reflexivity).
               exact Hrepr. }
             eapply enumeration_execution_snoc with
               (k := last) (T := T1 ⋈ th ⋈ T2)
               (full_trace := full_trace) (pool_strand := pool_strand)
               (l := lab).
             --- unfold last. exact Hlen.
             --- exact Hlabel_split.
             --- exact Hstep.
             --- exact Hext_new.
             --- eapply represented_added_node_to_original; [exact Hsame |].
                 eapply represents_pool_extend_any; eauto.
             --- unfold f0 in Hmap. rewrite Hlen_last in Hmap. exact Hmap.
             --- unfold label_dst, node_of_ref, lab. simpl.
                 rewrite <- Hmdef, <- Hstrand_m, Hthread_len.
                 reflexivity.
    }
    intros B P f Hbundle Hproto Htau Hcompat.
    eapply Haux; eauto.
    now apply compatible_bundle_enumeration_nodup with (f := f).
  Qed.

  (** Paper-level formulation of the scheduling conjecture.  Protocol
      well-formedness discharges the lower-level [tau_non_originating]
      condition, just as in [reachable_of_wf_bundle]. *)
  Corollary compatible_enumeration_has_labelled_execution :
    forall B P f,
      is_bundle B ->
      ofProtocol B P ->
      wf_protocol_no_mesg_origination P ->
      compatible_bundle_enumeration B f ->
      enumeration_has_execution B P f.
  Proof.
    intros B P f Hbundle Hproto Hwf Hcompat.
    eapply compatible_enumeration_has_labelled_execution_tau; eauto.
    now apply wf_protocol_no_mesg_origination_tau_non_originating
      with (P := P).
  Qed.

End CPSA_Enumeration_Semantics.
