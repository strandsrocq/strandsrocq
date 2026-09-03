From Stdlib Require Import List Lia.
Import ListNotations.

From strandsrocq.CPSA Require Import RoleSyntax ChoiceRoles Semantics.
From strandsrocq.CPSA Require Import ProtocolExamples.
From strandsrocq.CPSA.Instances Require Import DefaultInstances.

Import CPSA_Direct_Syntax.
Import ChoiceRoles.
Import CPSA_Semantics.

Open Scope string_scope.
Open Scope list_scope.
Open Scope cpsa_direct_syntax_scope.

(** * Computable CPSA semantics

This module refines the Prop-level operational semantics from
[CPSA_Semantics] into a Type-level presentation.  The extra computational
content records enough information to recover a concrete bundle from a
reachability derivation.

The main additions are indexed pool occurrences, written [T ↓[i,j] e], and a
bundle-producing reachability judgment, written [P ⊨ᵀ[st] T, B].
*)
Module CPSA_Computable_Semantics.

  (** ** Indexed pool occurrences

  [event_at T i j e] records that event [e] occurs at thread [i] and position
  [j] in the pool [T].  Receive steps use this indexed witness so that the
  generated bundle can point to the exact positive node that justifies the
  receive.
  *)
  Inductive event_at (T : thread_pool) : nat -> nat -> sT -> Type :=
  | EventAt :
      forall i j th e,
        nth_error T i = Some th ->
        nth_error th j = Some e ->
        event_at T i j e.

  Notation "T '↓[' i ',' j ']' e" := (event_at T i j e)
    (at level 70) : cpsa_direct_syntax_scope.

  Notation "T '↓[' i ',' j ']' '⊕' m" := (event_at T i j (⊕m))
    (at level 70) : cpsa_direct_syntax_scope.

  (** Indexed occurrence is the computable refinement of ordinary occurrence. *)
  Lemma event_at_occurred :
    forall T i j e,
      T ↓[i,j] e ->
      T ↓ e.
  Proof.
    intros T i j e H.
    destruct H as [i j th e HnthT Hnth].
    apply event_occurred_in.
    exists th.
    split.
    - now apply nth_error_In with (n := i).
    - now apply nth_error_In with (n := j).
  Defined.

  (** Ordinary occurrence contains an indexed witness, but only
      propositionally: this is enough for bridge theorems, not for computation. *)
  Lemma event_at_inhabited_of_occurred :
    forall T e,
      T ↓ e ->
      inhabited { i : nat & { j : nat & T ↓[i,j] e } }.
  Proof.
    intros T e Hocc.
    apply event_occurred_in in Hocc.
    destruct Hocc as [th [HthT HeTh]].
    apply In_nth_error in HthT.
    apply In_nth_error in HeTh.
    destruct HthT as [i HnthT].
    destruct HeTh as [j Hnth].
    constructor.
    exists i, j.
    exact (EventAt T i j th e HnthT Hnth).
  Qed.

  (** ** Type-level pool reachability

  [pool_reachable_fromT] mirrors [pool_reachable_from], but lives in [Type].
  The receive rules carry indexed positive-event witnesses instead of merely
  knowing that some positive event occurred somewhere in the pool.
  *)
  Inductive pool_reachable_fromT
    (P : protocol)
    (T0 : thread_pool)
    : thread_pool -> Type :=
  | PoolBaseT :
      pool_reachable_fromT P T0 T0
  | PoolSpawnSendT :
      forall T m,
        pool_reachable_fromT P T0 T ->
        P ▷ [⊕m] ->
        pool_reachable_fromT P T0 (T ⋈ [⊕m])
  | PoolExtendSendT :
      forall tr T1 T2 m,
        pool_reachable_fromT P T0 (T1 ⋈ tr ⋈ T2) ->
        P ▷ tr ++ [⊕m] ->
        pool_reachable_fromT P T0 (T1 ⋈ (tr ++ [⊕m]) ⋈ T2)
  | PoolSpawnRecvT :
      forall T i j m,
        pool_reachable_fromT P T0 T ->
        T ↓[i,j] ⊕m ->
        P ▷ [⊖m] ->
        pool_reachable_fromT P T0 (T ⋈ [⊖m])
  | PoolExtendRecvT :
      forall tr T1 T2 i j m,
        pool_reachable_fromT P T0 (T1 ⋈ tr ⋈ T2) ->
        T1 ⋈ tr ⋈ T2 ↓[i,j] ⊕m ->
        P ▷ tr ++ [⊖m] ->
        pool_reachable_fromT P T0 (T1 ⋈ (tr ++ [⊖m]) ⋈ T2).

  Definition reachable_poolT P := pool_reachable_fromT P [].

  (** Type-level reachability composes just like the Prop-level semantics. *)
  Lemma pool_reachable_fromT_trans :
    forall P T0 T1 T2,
      pool_reachable_fromT P T0 T1 ->
      pool_reachable_fromT P T1 T2 ->
      pool_reachable_fromT P T0 T2.
  Proof.
    intros P T0 T1 T2 H01 H12.
    induction H12.
    - exact H01.
    - apply PoolSpawnSendT; assumption.
    - apply PoolExtendSendT; assumption.
    - eapply PoolSpawnRecvT; eauto.
    - eapply PoolExtendRecvT; eauto.
  Qed.

  (** Prop-level reachability can be lifted to an inhabited Type-level
      derivation.  The result is intentionally [inhabited], because the
      Prop-level proof does not expose computational content. *)
  Lemma pool_reachable_fromT_inhabited_of_prop :
    forall P T0 T,
      pool_reachable_from P T0 T ->
      inhabited (pool_reachable_fromT P T0 T).
  Proof.
    intros P T0 T Hreach.
    induction Hreach as
      [| T m Hreach IH Hprefix
      | tr T1 T2 m Hreach IH Hprefix
      | T m Hreach IH Hocc Hprefix
      | tr T1 T2 m Hreach IH Hocc Hprefix].
    - constructor. apply PoolBaseT.
    - destruct IH as [d].
      constructor.
      now apply PoolSpawnSendT.
    - destruct IH as [d].
      constructor.
      now apply PoolExtendSendT.
    - destruct IH as [d].
      destruct (event_at_inhabited_of_occurred T (⊕m) Hocc) as
        [[i [j Hindexed]]].
      constructor.
      eapply PoolSpawnRecvT; eauto.
    - destruct IH as [d].
      destruct (event_at_inhabited_of_occurred (T1 ⋈ tr ⋈ T2) (⊕m) Hocc) as
        [[i [j Hindexed]]].
      constructor.
      eapply PoolExtendRecvT; eauto.
  Qed.

  Corollary reachable_poolT_inhabited_of_prop :
    forall P T,
      P ⊨ T ->
      inhabited (reachable_poolT P T).
  Proof.
    intros P T Hreach.
    exact (pool_reachable_fromT_inhabited_of_prop P [] T Hreach).
  Qed.

  (** Forget the computational witnesses and recover the Prop semantics. *)
  Fixpoint erase_pool_reachable_fromT
    {P T0 T}
    (d : pool_reachable_fromT P T0 T)
    : pool_reachable_from P T0 T :=
    match d with
    | PoolBaseT _ _ =>
        PoolBase P T0
    | PoolSpawnSendT _ _ T m d' Hprefix =>
        PoolSpawnSend P T0 T m
          (erase_pool_reachable_fromT d')
          Hprefix
    | PoolExtendSendT _ _ tr T1 T2 m d' Hprefix =>
        PoolExtendSend P T0 tr T1 T2 m
          (erase_pool_reachable_fromT d')
          Hprefix
    | PoolSpawnRecvT _ _ T i j m d' Hocc Hprefix =>
        PoolSpawnRecv P T0 T m
          (erase_pool_reachable_fromT d')
          (event_at_occurred T i j (⊕m) Hocc)
          Hprefix
    | PoolExtendRecvT _ _ tr T1 T2 i j m d' Hocc Hprefix =>
        PoolExtendRecv P T0 tr T1 T2 m
          (erase_pool_reachable_fromT d')
          (event_at_occurred (T1 ⋈ tr ⋈ T2) i j (⊕m) Hocc)
          Hprefix
    end.

  Reserved Notation "P '⊨ᵀ[' st ']' T ',' B" (at level 70).

  (** ** Bundle-producing reachability

  [reachable_pool_bundleT P st T B] builds the final thread pool [T] and the
  bundle [B] in lockstep.  The map [st] assigns a strand identifier to each
  thread index; in the canonical case it is instantiated with the thread's full
  trace.

  Send steps add nodes and intrastrand edges.  Receive steps additionally add
  an interstrand edge from the indexed positive witness [T ↓[i,j] ⊕m] to the
  newly added negative node.
  *)
  Inductive reachable_pool_bundleT
    (P : protocol)
    (st : nat -> Σ)
    : thread_pool -> bundle_type -> Type :=
  | PoolBaseBundleT :
      P ⊨ᵀ[st] [] , {| nodes := []; intra := []; inter := [] |}
  | PoolSpawnSendBundleT :
      forall T B m,
        P ⊨ᵀ[st] T, B ->
        P ▷ [⊕m] ->
        let n := (st (length T), 0) in
        P ⊨ᵀ[st] T ⋈ [⊕m],
          {| nodes := n :: nodes B; intra := intra B; inter := inter B |}
  | PoolExtendSendBundleT :
      forall tr T1 T2 B m,
        P ⊨ᵀ[st] T1 ⋈ tr ⋈ T2, B ->
        P ▷ tr ++ [⊕m] ->
        let n' := (st (length T1), length tr) in
        let n := (st (length T1), length tr - 1) in
        P ⊨ᵀ[st] T1 ⋈ (tr ++ [⊕m]) ⋈ T2,
          {| nodes := n' :: nodes B;
             intra :=
               match tr with
               | [] => intra B
               | _ => (n, n') :: intra B
               end;
             inter := inter B |}
  | PoolSpawnRecvBundleT :
      forall T B i j m,
        P ⊨ᵀ[st] T, B ->
        T ↓[i,j] ⊕m ->
        P ▷ [⊖m] ->
        let src := (st i, j) in
        let dst := (st (length T), 0) in
        P ⊨ᵀ[st] T ⋈ [⊖m],
          {| nodes := dst :: nodes B;
             intra := intra B;
             inter := (src, dst) :: inter B |}
  | PoolExtendRecvBundleT :
      forall tr T1 T2 B i j m,
        P ⊨ᵀ[st] T1 ⋈ tr ⋈ T2, B ->
        T1 ⋈ tr ⋈ T2 ↓[i,j] ⊕m ->
        P ▷ tr ++ [⊖m] ->
        let src := (st i, j) in
        let pred := (st (length T1), length tr - 1) in
        let dst := (st (length T1), length tr) in
        P ⊨ᵀ[st] T1 ⋈ (tr ++ [⊖m]) ⋈ T2,
          {| nodes := dst :: nodes B;
             intra :=
               match tr with
               | [] => intra B
               | _ => (pred, dst) :: intra B
               end;
             inter := (src, dst) :: inter B |}

  where "P '⊨ᵀ[' st ']' T ',' B" :=
    (reachable_pool_bundleT P st T B) : cpsa_direct_syntax_scope.

  (** A bundle derivation contains a plain pool derivation by erasure. *)
  Fixpoint erase_reachable_pool_bundleT
    {P st T B}
    (d : reachable_pool_bundleT P st T B)
    : reachable_poolT P T :=
    match d with
    | PoolBaseBundleT _ _ =>
        PoolBaseT P []
    | PoolSpawnSendBundleT _ _ T B m d' Hprefix =>
        PoolSpawnSendT P [] T m
          (erase_reachable_pool_bundleT d')
          Hprefix
    | PoolExtendSendBundleT _ _ tr T1 T2 B m d' Hprefix =>
        PoolExtendSendT P [] tr T1 T2 m
          (erase_reachable_pool_bundleT d')
          Hprefix
    | PoolSpawnRecvBundleT _ _ T B i j m d' Hocc Hprefix =>
        PoolSpawnRecvT P [] T i j m
          (erase_reachable_pool_bundleT d')
          Hocc
          Hprefix
    | PoolExtendRecvBundleT _ _ tr T1 T2 B i j m d' Hocc Hprefix =>
        PoolExtendRecvT P [] tr T1 T2 i j m
          (erase_reachable_pool_bundleT d')
          Hocc
          Hprefix
    end.

  Definition computed_bundle_of
    {P st T}
    (d : { B : bundle_type & reachable_pool_bundleT P st T B })
    : bundle_type :=
    projT1 d.

  Definition computed_reachability_of
    {P st T}
    (d : { B : bundle_type & reachable_pool_bundleT P st T B })
    : reachable_poolT P T :=
    erase_reachable_pool_bundleT (projT2 d).

  (** ** Communication edges

  [receive_edges_of] extracts the interstrand edges introduced by the receive
  rules of a bundle derivation.  It is useful as a small audit trail for the
  indexed witnesses that generated the communication edges.
  *)
  Fixpoint receive_edges_of
    {P st T B}
    (d : reachable_pool_bundleT P st T B)
    : edge_set__t :=
    match d with
    | PoolBaseBundleT _ _ =>
        []
    | PoolSpawnSendBundleT _ _ _ _ _ d' _ =>
        receive_edges_of d'
    | PoolExtendSendBundleT _ _ _ _ _ _ _ d' _ =>
        receive_edges_of d'
    | PoolSpawnRecvBundleT _ _ T _ i j _ d' _ _ =>
        ((st i, j), (st (length T), 0)) :: receive_edges_of d'
    | PoolExtendRecvBundleT _ _ tr T1 _ _ i j _ d' _ _ =>
        ((st i, j), (st (length T1), length tr)) :: receive_edges_of d'
    end.

  (** The bundle's interstrand edges are exactly the receive-generated edges. *)
  Lemma reachable_pool_bundleT_inter_is_receive_edges :
    forall P st T B (d : reachable_pool_bundleT P st T B),
      inter B = receive_edges_of d.
  Proof.
    intros P st T B d.
    induction d as
      [| T B m d IH Hprefix
      | tr T1 T2 B m d IH Hprefix
      | T B i j m d IH Hocc Hprefix
      | tr T1 T2 B i j m d IH Hocc Hprefix].
    - reflexivity.
    - exact IH.
    - exact IH.
    - simpl. now rewrite IH.
    - simpl. now rewrite IH.
  Qed.

  (** ** Bundle soundness and extraction

  Indexed pool occurrences become canonical bundle nodes with the same term.
  This is the key receive-side lookup used in the soundness proof.
  *)
  Lemma event_at_source_canonical :
    forall G T full_trace i j e,
      represents_pool_canonical G T full_trace ->
      extends_pool_trace T full_trace ->
      T ↓[i,j] e ->
      In ((i, full_trace i), j) (nodes G) /\
      term ((i, full_trace i), j) = e.
  Proof.
    intros G T full_trace i j e Hrepr Hext Hocc.
    destruct Hocc as [i j th e HnthT Hnth].
    split.
    - eapply represents_pool_in; eauto.
      apply nth_error_Some.
      rewrite Hnth.
      discriminate.
    - unfold term, strand, index; simpl.
      destruct (Hext i th HnthT) as [suffix Hfull].
      rewrite Hfull.
      apply nth_error_nth.
      rewrite nth_error_app1.
      + exact Hnth.
      + apply nth_error_Some.
        rewrite Hnth.
        discriminate.
  Qed.

  (** Soundness: a computable bundle derivation produces an inductive bundle
      that canonically represents the final thread pool. *)
  Theorem reachable_pool_bundleT_canonical_sound :
    forall P T B full_trace,
      reachable_pool_bundleT P (fun i => (i, full_trace i)) T B ->
      extends_pool_trace T full_trace ->
      IndBundle B /\ represents_pool_canonical B T full_trace.
  Proof.
    intros P T B full_trace Hder.
    induction Hder as
      [| T B m Hder IH Hprefix
      | tr T1 T2 B m Hder IH Hprefix
      | T B i j m Hder IH Hocc Hprefix
      | tr T1 T2 B i j m Hder IH Hocc Hprefix];
      intros Hext.
    - split.
      + constructor.
      + unfold represents_pool_canonical, represents_pool, is_node_of.
        simpl.
        intros n. split.
        * easy.
        * intros [i [th [suffix [Hnth _]]]].
          destruct i; easy.
    - pose proof (extends_spawn T [⊕ m] full_trace Hext) as Hext_old.
      destruct (IH Hext_old) as [Hbundle Hrepr].
      destruct B as [N L C]; simpl in *.
      split.
      + apply G_pos_zero.
        * exact Hbundle.
        * unfold n.
          exact (represents_pool_spawn_not_in
            {| nodes := N; intra := L; inter := C |} T full_trace Hrepr).
        * destruct (Hext (length T) [⊕m]) as [suffix Hfull].
          -- rewrite nth_error_snoc. reflexivity.
          -- unfold is_positive, term, strand, index; simpl.
             rewrite Hfull. exact I.
        * reflexivity.
      + unfold n.
        apply (represents_pool_spawn
          {| nodes := N; intra := L; inter := C |}
          T full_trace (⊕m) L C); assumption.
    - pose proof (extends_pool_trace_extend T1 tr T2 (⊕m) full_trace Hext)
        as Hext_old.
      destruct (IH Hext_old) as [Hbundle Hrepr].
      destruct B as [N L C]; simpl in *.
      split.
      + destruct tr as [|e tr'].
        * simpl.
          apply G_pos_zero.
          -- exact Hbundle.
          -- apply (represents_pool_not_in_next
               {| nodes := N; intra := L; inter := C |} (T1 ++ [[]] ++ T2)
               full_trace (length T1) [] Hrepr).
             rewrite nth_error_middle. reflexivity.
          -- destruct (Hext (length T1) [⊕m]) as [suffix Hfull].
             ++ change (nth_error (T1 ++ [⊕m] :: T2) (length T1) =
                  Some [⊕m]).
                rewrite nth_error_middle_cons. reflexivity.
             ++ unfold is_positive, term, strand, index; simpl.
                rewrite Hfull. exact I.
          -- reflexivity.
        * apply G_pos.
          -- exact Hbundle.
          -- unfold n.
             replace (length (e :: tr') - 1) with (length tr') by (simpl; lia).
             apply (represents_pool_in
               {| nodes := N; intra := L; inter := C |} (T1 ++ [e :: tr'] ++ T2)
               full_trace (length T1) (e :: tr') (length tr')
               Hrepr Hext_old).
             ++ rewrite nth_error_middle. reflexivity.
             ++ simpl. lia.
          -- unfold n'.
             apply (represents_pool_not_in_next
               {| nodes := N; intra := L; inter := C |} (T1 ++ [e :: tr'] ++ T2)
               full_trace (length T1) (e :: tr') Hrepr).
             rewrite nth_error_middle. reflexivity.
          -- destruct (Hext (length T1) ((e :: tr') ++ [⊕m])) as
               [suffix Hfull].
             ++ change (nth_error (T1 ++ ((e :: tr') ++ [⊕m]) :: T2)
                  (length T1) = Some ((e :: tr') ++ [⊕m])).
                rewrite nth_error_middle_cons. reflexivity.
             ++ unfold n', is_positive, term, strand, index; simpl.
                assert (Hnth :
                  nth (S (length tr')) (full_trace (length T1)) (⊖ τ) = ⊕m).
                { rewrite Hfull.
                  rewrite app_nth1 by (rewrite length_app; simpl; lia).
                  replace (S (length tr')) with (length (e :: tr')) by (simpl; lia).
                  rewrite app_nth2 by lia.
                  replace (length (e :: tr') - length (e :: tr')) with 0 by lia.
                  reflexivity. }
                rewrite Hnth. exact I.
          -- unfold intrastrand, strand, index; simpl.
             repeat f_equal; lia.
      + apply (represents_pool_extend
          {| nodes := N; intra := L; inter := C |}
          T1 tr T2 full_trace (⊕m)
          ((((length T1, full_trace (length T1)), length tr - 1),
            ((length T1, full_trace (length T1)), length tr)) :: L)
          C); assumption.
    - pose proof (extends_spawn T [⊖ m] full_trace Hext) as Hext_old.
      destruct (IH Hext_old) as [Hbundle Hrepr].
      destruct B as [N L C]; simpl in *.
      destruct (event_at_source_canonical {| nodes := N; intra := L; inter := C |}
        T full_trace i j (⊕m)
        Hrepr Hext_old Hocc) as [Hsource_in Hsource_term].
      split.
      + apply G_neg_zero.
        * exact Hbundle.
        * exact Hsource_in.
        * unfold dst.
          exact (represents_pool_spawn_not_in
            {| nodes := N; intra := L; inter := C |} T full_trace Hrepr).
        * destruct (Hext (length T) [⊖m]) as [suffix Hfull].
          -- rewrite nth_error_snoc. reflexivity.
          -- unfold dst.
             change (((i, full_trace i), j) ⟶
               ((length T, full_trace (length T)), 0)).
             unfold interstrand.
             rewrite Hsource_term.
             unfold term, strand, index; simpl.
             rewrite Hfull. reflexivity.
        * reflexivity.
      + unfold dst.
        apply (represents_pool_spawn
          {| nodes := N; intra := L; inter := C |}
          T full_trace (⊖m) L
          ((((i, full_trace i), j),
            ((length T, full_trace (length T)), 0)) :: C)); assumption.
    - pose proof (extends_pool_trace_extend T1 tr T2 (⊖m) full_trace Hext)
        as Hext_old.
      destruct (IH Hext_old) as [Hbundle Hrepr].
      destruct B as [N L C]; simpl in *.
      destruct (event_at_source_canonical {| nodes := N; intra := L; inter := C |}
        (T1 ++ [tr] ++ T2)
        full_trace i j (⊕m) Hrepr Hext_old Hocc) as
        [Hsource_in Hsource_term].
      split.
      + destruct tr as [|e tr'].
        * simpl.
          apply G_neg_zero.
          -- exact Hbundle.
          -- exact Hsource_in.
          -- apply (represents_pool_not_in_next
               {| nodes := N; intra := L; inter := C |} (T1 ++ [[]] ++ T2)
               full_trace (length T1) [] Hrepr).
             rewrite nth_error_middle. reflexivity.
          -- destruct (Hext (length T1) [⊖m]) as [suffix Hfull].
             ++ change (nth_error (T1 ++ [⊖m] :: T2) (length T1) =
                  Some [⊖m]).
                rewrite nth_error_middle_cons. reflexivity.
             ++ unfold dst.
                change (((i, full_trace i), j) ⟶
                  ((length T1, full_trace (length T1)), 0)).
                unfold interstrand.
                rewrite Hsource_term.
                unfold term, strand, index; simpl.
                rewrite Hfull. reflexivity.
          -- reflexivity.
        * apply G_neg.
          -- exact Hbundle.
          -- exact Hsource_in.
          -- unfold pred.
             replace (length (e :: tr') - 1) with (length tr') by (simpl; lia).
             apply (represents_pool_in
               {| nodes := N; intra := L; inter := C |} (T1 ++ [e :: tr'] ++ T2)
               full_trace (length T1) (e :: tr') (length tr')
               Hrepr Hext_old).
             ++ rewrite nth_error_middle. reflexivity.
             ++ simpl. lia.
          -- unfold dst.
             apply (represents_pool_not_in_next
               {| nodes := N; intra := L; inter := C |} (T1 ++ [e :: tr'] ++ T2)
               full_trace (length T1) (e :: tr') Hrepr).
             rewrite nth_error_middle. reflexivity.
          -- destruct (Hext (length T1) ((e :: tr') ++ [⊖m])) as
               [suffix Hfull].
             ++ change (nth_error (T1 ++ ((e :: tr') ++ [⊖m]) :: T2)
                  (length T1) = Some ((e :: tr') ++ [⊖m])).
                rewrite nth_error_middle_cons. reflexivity.
             ++ unfold dst.
                change (((i, full_trace i), j) ⟶
                  ((length T1, full_trace (length T1)), length (e :: tr'))).
                unfold interstrand.
                rewrite Hsource_term.
                unfold term, strand, index; simpl.
                assert (Hnth :
                  nth (S (length tr')) (full_trace (length T1)) (⊖ τ) = ⊖m).
                { rewrite Hfull.
                  rewrite app_nth1 by (rewrite length_app; simpl; lia).
                  replace (S (length tr')) with (length (e :: tr')) by (simpl; lia).
                  rewrite app_nth2 by lia.
                  replace (length (e :: tr') - length (e :: tr')) with 0 by lia.
                  reflexivity. }
                rewrite Hnth.
                reflexivity.
          -- unfold intrastrand, strand, index; simpl.
             repeat f_equal; lia.
      + apply (represents_pool_extend
          {| nodes := N; intra := L; inter := C |}
          T1 tr T2 full_trace (⊖m)
          ((((length T1, full_trace (length T1)), length tr - 1),
            ((length T1, full_trace (length T1)), length tr)) :: L)
          ((((i, full_trace i), j),
            ((length T1, full_trace (length T1)), length tr)) :: C)); assumption.
  Qed.

  (** Every Type-level reachable pool computes a bundle derivation, once a full
      trace is chosen for each thread. *)
  Theorem bundle_derivation_of_reachableT_with_trace :
    forall P T,
      reachable_poolT P T ->
      forall full_trace,
        extends_pool_trace T full_trace ->
        { B : bundle_type &
          reachable_pool_bundleT P (fun i => (i, full_trace i)) T B }.
  Proof.
    intros P T Hreach.
    induction Hreach as
      [| T m Hreach IH Hprefix
      | tr T1 T2 m Hreach IH Hprefix
      | T i j m Hreach IH Hocc Hprefix
      | tr T1 T2 i j m Hreach IH Hocc Hprefix];
      intros full_trace Hext.
    - exists {| nodes := []; intra := []; inter := [] |}.
      apply PoolBaseBundleT.
    - pose proof (extends_spawn T [⊕m] full_trace Hext) as Hext_old.
      destruct (IH full_trace Hext_old) as [B HB].
      exists
        {| nodes := ((length T, full_trace (length T)), 0) :: nodes B;
           intra := intra B;
           inter := inter B |}.
      now apply PoolSpawnSendBundleT.
    - pose proof (extends_pool_trace_extend T1 tr T2 (⊕m) full_trace Hext)
        as Hext_old.
      destruct (IH full_trace Hext_old) as [B HB].
      exists
        {| nodes := ((length T1, full_trace (length T1)), length tr) :: nodes B;
           intra :=
             match tr with
             | [] => intra B
             | _ =>
                 ((((length T1, full_trace (length T1)), length tr - 1),
                   ((length T1, full_trace (length T1)), length tr)) :: intra B)
             end;
           inter := inter B |}.
      now apply PoolExtendSendBundleT.
    - pose proof (extends_spawn T [⊖m] full_trace Hext) as Hext_old.
      destruct (IH full_trace Hext_old) as [B HB].
      exists
        {| nodes := ((length T, full_trace (length T)), 0) :: nodes B;
           intra := intra B;
           inter :=
             ((((i, full_trace i), j),
               ((length T, full_trace (length T)), 0)) :: inter B) |}.
      eapply (PoolSpawnRecvBundleT
        P (fun i => (i, full_trace i)) T B i j m); eauto.
    - pose proof (extends_pool_trace_extend T1 tr T2 (⊖m) full_trace Hext)
        as Hext_old.
      destruct (IH full_trace Hext_old) as [B HB].
      exists
        {| nodes := ((length T1, full_trace (length T1)), length tr) :: nodes B;
           intra :=
             match tr with
             | [] => intra B
             | _ =>
                 ((((length T1, full_trace (length T1)), length tr - 1),
                   ((length T1, full_trace (length T1)), length tr)) :: intra B)
             end;
           inter :=
             ((((i, full_trace i), j),
               ((length T1, full_trace (length T1)), length tr)) :: inter B) |}.
      eapply (PoolExtendRecvBundleT
        P (fun i => (i, full_trace i)) tr T1 T2 B i j m); eauto.
  Defined.

  (** Type-level counterpart of [bundle_of_reachable_with_trace]: the computed
      bundle is an inductive bundle and canonically represents the pool. *)
  Theorem bundle_of_reachableT_with_trace :
    forall P T,
      reachable_poolT P T ->
      forall full_trace,
        extends_pool_trace T full_trace ->
        { B : bundle_type &
          IndBundle B /\ represents_pool_canonical B T full_trace }.
  Proof.
    intros P T Hreach full_trace Hext.
    destruct (bundle_derivation_of_reachableT_with_trace P T Hreach full_trace Hext)
      as [B HB].
    exists B.
    exact (reachable_pool_bundleT_canonical_sound P T B full_trace HB Hext).
  Defined.

  (** The computed bundle extracted from a Type-level derivation satisfies the
      soundness invariant without exposing the dependent pair. *)
  Corollary reachable_poolT_computed_bundle_sound :
    forall P T (d : reachable_poolT P T) full_trace
      (Hext : extends_pool_trace T full_trace),
      let B := computed_bundle_of
        (bundle_derivation_of_reachableT_with_trace P T d full_trace Hext) in
      IndBundle B /\ represents_pool_canonical B T full_trace.
  Proof.
    intros P T d full_trace Hext Bdef.
    unfold Bdef.
    destruct (bundle_derivation_of_reachableT_with_trace P T d full_trace Hext)
      as [B HB].
    exact (reachable_pool_bundleT_canonical_sound P T B full_trace HB Hext).
  Qed.

  (** Prop-friendly completeness bridge: every compatible bundle represented by
      the Prop-level completeness theorem gives an inhabited Type-level
      reachability derivation.  This deliberately preserves the non-computing
      nature of the bundle-to-pool direction. *)
  Theorem reachable_poolT_inhabited_of_bundle :
    forall G P,
      IndBundle G ->
      ofProtocol G P ->
      tau_non_originating G ->
      exists T full_trace pool_strand,
        inhabited (reachable_poolT P T) /\
          extends_pool_trace T full_trace /\
          represents_pool G T full_trace pool_strand.
  Proof.
    intros G P Hbundle Hproto Htau.
    destruct (reachable_of_bundle G P Hbundle Hproto Htau)
      as [T [full_trace [pool_strand [Hreach [Hext Hrepr]]]]].
    exists T, full_trace, pool_strand.
    split.
    - now apply reachable_poolT_inhabited_of_prop.
    - split; assumption.
  Qed.

  Module Examples.

    (** ** Example

    The example constructs a Type-level derivation for [example_protocol] and
    computes the corresponding bundle through
    [bundle_derivation_of_reachableT_with_trace].
    The resulting bundle is definitionally equal to the hand-written bundle
    from [ProtocolExamples].
    *)
    Import ProtocolExamples.

    Local Coercion M_Name : Name >-> Mesg.
    Local Coercion M_Text : Text >-> Mesg.
    Local Coercion M_Akey : Akey >-> Mesg.

    Definition example_thread_strand (i : nat) : Σ :=
      match i with
      | 0 => example_init_strand
      | 1 => example_resp_strand
      | _ => (i, [])
      end.

    Definition reachable_pool_example_bundleT :
      { B : bundle_type &
        example_protocol ⊨ᵀ[example_thread_strand]
          reachable_pool_example_pool, B }.
    Proof.
      eexists.
      unfold reachable_pool_example_pool, example_init_trace, example_resp_trace.
      eapply (PoolExtendRecvBundleT
        example_protocol example_thread_strand
        [⊕ A ⋅ t] [] [[⊖ A ⋅ t; ⊕ ⟨ A ⋅ t ⟩_(K B)]]
        _ 1 1).
      - eapply (PoolExtendSendBundleT
          example_protocol example_thread_strand
          [⊖ A ⋅ t] [[⊕ A ⋅ t]] [] _).
        + eapply (PoolSpawnRecvBundleT
            example_protocol example_thread_strand
            [[⊕ A ⋅ t]] _ 0 0).
          * eapply (PoolSpawnSendBundleT
              example_protocol example_thread_strand [] _).
            -- apply PoolBaseBundleT.
            -- exists init_role,
                (eta
                  {{ n := t }}
                  {{ a := A }}
                  {{ b := B }}),
                [⊖ ⟨ A ⋅ t ⟩_(K B)].
               split; simpl; auto.
          * apply (EventAt [[⊕ A ⋅ t]] 0 0 [⊕ A ⋅ t] (⊕ A ⋅ t));
              reflexivity.
          * exists resp_role,
              (eta
                {{ n := t }}
                {{ a := A }}
                {{ b := B }}),
              [⊕ ⟨ A ⋅ t ⟩_(K B)].
            split; simpl; auto.
        + exists resp_role,
            (eta
              {{ n := t }}
              {{ a := A }}
              {{ b := B }}),
            [].
          split; simpl; auto.
      - apply (EventAt
            ([[⊕ A ⋅ t]] ++ [[⊖ A ⋅ t; ⊕ ⟨ A ⋅ t ⟩_(K B)]])
            1 1
            [⊖ A ⋅ t; ⊕ ⟨ A ⋅ t ⟩_(K B)]
            (⊕ ⟨ A ⋅ t ⟩_(K B)));
          reflexivity.
      - exact role_prefix_example.
    Defined.

    Example computed_example_bundle_is_expected :
      computed_bundle_of reachable_pool_example_bundleT =
      reachable_pool_example_bundle.
    Proof.
      reflexivity.
    Qed.

    Example computed_example_erases :
      example_protocol ⊨ reachable_pool_example_pool.
    Proof.
      exact (erase_pool_reachable_fromT
        (computed_reachability_of reachable_pool_example_bundleT)).
    Qed.

    Definition reachable_pool_exampleT :
      reachable_poolT example_protocol reachable_pool_example_pool.
    Proof.
      unfold reachable_pool_example_pool, example_init_trace, example_resp_trace.
      eapply (PoolExtendRecvT
        example_protocol []
        [⊕ A ⋅ t] [] [[⊖ A ⋅ t; ⊕ ⟨ A ⋅ t ⟩_(K B)]]
        1 1).
      - eapply (PoolExtendSendT
          example_protocol []
          [⊖ A ⋅ t] [[⊕ A ⋅ t]] [] (⟨ A ⋅ t ⟩_(K B))).
        + eapply (PoolSpawnRecvT
            example_protocol [] [[⊕ A ⋅ t]] 0 0 (A ⋅ t)).
          * eapply (PoolSpawnSendT
              example_protocol [] [] (A ⋅ t)).
            -- apply PoolBaseT.
            -- exists init_role,
                (eta
                  {{ n := t }}
                  {{ a := A }}
                  {{ b := B }}),
                [⊖ ⟨ A ⋅ t ⟩_(K B)].
               split; simpl; auto.
          * apply (EventAt [[⊕ A ⋅ t]] 0 0 [⊕ A ⋅ t] (⊕ A ⋅ t));
              reflexivity.
          * exists resp_role,
              (eta
                {{ n := t }}
                {{ a := A }}
                {{ b := B }}),
              [⊕ ⟨ A ⋅ t ⟩_(K B)].
            split; simpl; auto.
        + exists resp_role,
            (eta
              {{ n := t }}
              {{ a := A }}
              {{ b := B }}),
            [].
          split; simpl; auto.
      - apply (EventAt
            ([[⊕ A ⋅ t]] ++ [[⊖ A ⋅ t; ⊕ ⟨ A ⋅ t ⟩_(K B)]])
            1 1
            [⊖ A ⋅ t; ⊕ ⟨ A ⋅ t ⟩_(K B)]
            (⊕ ⟨ A ⋅ t ⟩_(K B)));
          reflexivity.
      - exact role_prefix_example.
    Defined.

    Definition reachable_pool_example_computed_bundle : bundle_type :=
      computed_bundle_of
        (bundle_derivation_of_reachableT_with_trace
          example_protocol
          reachable_pool_example_pool
          reachable_pool_exampleT
          example_full_trace
          reachable_pool_example_full_trace_extends).

    (** Running [Compute reachable_pool_example_computed_bundle] we obtain:

<<
= {|
    nodes :=
      [(0, [⊕ A ⋅ $ t; ⊖ ⟨ A ⋅ $ t ⟩_ K B], 1);
       (1, [⊖ A ⋅ $ t; ⊕ ⟨ A ⋅ $ t ⟩_ K B], 1);
       (1, [⊖ A ⋅ $ t; ⊕ ⟨ A ⋅ $ t ⟩_ K B], 0);
       (0, [⊕ A ⋅ $ t; ⊖ ⟨ A ⋅ $ t ⟩_ K B], 0)];

    intra :=
      [((0, [⊕ A ⋅ $ t; ⊖ ⟨ A ⋅ $ t ⟩_ K B], 0),
        (0, [⊕ A ⋅ $ t; ⊖ ⟨ A ⋅ $ t ⟩_ K B], 1));
       ((1, [⊖ A ⋅ $ t; ⊕ ⟨ A ⋅ $ t ⟩_ K B], 0),
        (1, [⊖ A ⋅ $ t; ⊕ ⟨ A ⋅ $ t ⟩_ K B], 1))];

    inter :=
      [((1, [⊖ A ⋅ $ t; ⊕ ⟨ A ⋅ $ t ⟩_ K B], 1),
        (0, [⊕ A ⋅ $ t; ⊖ ⟨ A ⋅ $ t ⟩_ K B], 1));
       ((0, [⊕ A ⋅ $ t; ⊖ ⟨ A ⋅ $ t ⟩_ K B], 0),
        (1, [⊖ A ⋅ $ t; ⊕ ⟨ A ⋅ $ t ⟩_ K B], 0))]
  |}
  : bundle_type
>>
    *)
    Example reachable_pool_example_computed_bundle_is_expected :
      reachable_pool_example_computed_bundle =
      reachable_pool_example_bundle.
    Proof.
      reflexivity.
    Qed.

    Example reachable_pool_example_computed_bundle_sound :
      IndBundle reachable_pool_example_computed_bundle /\
      represents_pool_canonical
        reachable_pool_example_computed_bundle
        reachable_pool_example_pool
        example_full_trace.
    Proof.
      exact (reachable_poolT_computed_bundle_sound
        example_protocol
        reachable_pool_example_pool
        reachable_pool_exampleT
        example_full_trace
        reachable_pool_example_full_trace_extends).
    Qed.

  End Examples.

End CPSA_Computable_Semantics.
