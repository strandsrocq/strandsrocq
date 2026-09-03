Require Import Stdlib.Lists.List.
Require Import Stdlib.Lists.ListSet.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Sorting.Permutation.
From Stdlib Require Import Lia.
Require Import Stdlib.Relations.Relations.

Require Import Strands.
Require Import Bundles.
Require Import RelMinimal.
Require Import BundleInductive.

Import Stdlib.Lists.List.ListNotations.

Open Scope list_scope.
Set Implicit Arguments.

Module Type BundleSizeInductionSig
  (Import T : TermSig)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St)
  (Import B : BundleSig T St SSp)
  (Import BI : BundleInductiveSig T St SSp B). 

  Definition bundle_size (B : bundle_type) : nat := length (nodes B).

  Theorem bundle_size_induction : forall (P : bundle_type -> Prop),
      (forall B n, is_bundle B -> 
                   (forall C,
                       is_bundle C ->
                       bundle_size C < n ->
                       P C) ->
                   bundle_size B <= n -> P B) ->
      forall n B, is_bundle B -> bundle_size B <= n -> P B.
  Proof.
    unfold bundle_size. 
    intros P IH n. induction n.
    - intros.  apply IH with (n:=0); try assumption.
      intros. lia.
    - intros.  apply IH with (n:=S n); try assumption.
      + intros. apply IHn; try assumption; try lia.
  Qed.

      

  Corollary bundle_size_induction_cor1: forall (P : bundle_type -> Prop),
      (forall B n, is_bundle B -> 
                   (forall C,
                       is_bundle C ->
                       bundle_size C < n ->
                       P C) ->
                   bundle_size B <= n -> P B) ->
      forall B, is_bundle B -> P B.
  Proof.
    intros P IH B Hbundle.  apply bundle_size_induction with (n:=bundle_size B); try assumption; try lia.
  Qed.

  Corollary bundle_size_induction_cor : forall (P : bundle_type -> Prop),
      (forall B, is_bundle B -> 
                   (forall C,
                       is_bundle C ->
                       bundle_size C < bundle_size B ->
                       P C) ->
                   P B) ->
      forall B, is_bundle B -> P B.
  Proof.
    intros P IH.  apply bundle_size_induction_cor1.
    intros B n HbundleB IHC Hsize.  apply IH.
    - assumption.
    - intros C HnundleC HsizeC.  apply IHC; try assumption; try lia.
  Qed.

  Definition dedup_bundle (B : bundle_type) : bundle_type :=
    {| nodes := nodup eq_node__t_dec (nodes B);
      intra := nodup eq_edge__t_dec (intra B);
      inter := nodup eq_edge__t_dec (inter B) |}.

  Lemma is_bundle_dedup : forall (B : bundle_type),
      is_bundle B -> is_bundle (dedup_bundle B).
  Proof.
    unfold is_bundle.  unfold dedup_bundle.  unfold is_sub.  
    unfold is_edge_of. unfold is_node_of. unfold incident_to. unfold set_In. simpl. 
    intros B [[Hsub_intra [Hsub_inter [Hsub_intranode Hsub_internode]]]
                [Hinter [Hintra Hacyclic]]]. 
    repeat split.
    - intros n1 n2 Hedge.  apply Hsub_intra.  
      rewrite nodup_In in Hedge.  exact Hedge.
    - intros n1 n2 Hedge.  apply Hsub_inter.
      rewrite nodup_In in Hedge.  exact Hedge.
    - intros n [n' [Hright | Hleft]]; apply nodup_In; apply Hsub_intranode.
      + apply nodup_In in Hright. exists n'. left. assumption.
      + apply nodup_In in Hleft. exists n'. right. assumption.
    - intros n [n' [Hright | Hleft]]; apply nodup_In; apply Hsub_internode.
      + apply nodup_In in Hright. exists n'. left. assumption.
      + apply nodup_In in Hleft. exists n'. right. assumption.
    - intros n1 HinN1 Hneg. specialize Hinter with (n1:=n1).
      assert (exists ! n2 : node__t, In (n2, n1) (inter B)).
      {apply Hinter.
       - apply nodup_In in HinN1. assumption.
       - assumption. }
      destruct H as [n2]. destruct H.
      rewrite <- unique_existence. split.
      + exists n2.  apply nodup_In. assumption.
      + unfold uniqueness.  intros x y Hx Hy.
        apply nodup_In in Hx.  apply nodup_In in Hy.
        apply H0 in Hx. apply H0 in Hy.
        rewrite <- Hx. rewrite <- Hy. reflexivity.
    - intros x y.  rewrite nodup_In. rewrite nodup_In. apply Hintra.
    - unfold edges.  simpl. intros n Hedge.
      specialize bundle_lt_incl with
        (E:=set_union eq_edge__t_dec (nodup eq_edge__t_dec (intra B))
              (nodup eq_edge__t_dec (inter B)))
        (E':=set_union eq_edge__t_dec (intra B) (inter B))
        (n1:=n) (n2:=n).
      intros.  apply H in Hedge. 
      + unfold edges in Hacyclic. specialize Hacyclic with (n:=n).
        apply Hacyclic in Hedge.  contradiction.
      + intros e Hnodup.  apply set_union_iff.  
        apply set_union_iff in Hnodup.
        destruct Hnodup.
        * left.  apply nodup_In in H0. assumption.
        * right. apply nodup_In in H0. assumption.
  Qed.

  Lemma dedup_ordering : forall B m n, 
      edges B ⊢ m ⪯ n <-> edges (dedup_bundle B) ⊢ m ⪯ n.
  Proof.
    intros B m n. split.
    - apply bundle_le_sub. unfold dedup_bundle.  unfold edges. simpl.
      intros e HB.
      apply set_union_intro. apply set_union_elim in HB.
      destruct HB.
      + left. apply nodup_In.   assumption.
      + right. apply nodup_In. assumption.
    - apply bundle_le_sub. unfold dedup_bundle.  unfold edges. simpl.
      intros e HB.
      apply set_union_intro. apply set_union_elim in HB.
      destruct HB.
      + left.  apply nodup_In in H.  assumption.
      + right. apply nodup_In in H. assumption.
  Qed.

  Lemma dedup_nodes : forall B n,
      In n (nodes B) <-> In n (nodes (dedup_bundle B)).
  Proof.  
    intros B n. destruct B. unfold dedup_bundle. unfold nodes.
    split; apply nodup_In.
  Qed.

  Lemma dedup_sink : forall B m,
      is_bundle B -> sink m B ->
      sink m (dedup_bundle B).
  Proof.
    unfold sink. unfold is_node_of.   unfold set_In.
    intros B m Hbundle [Hm Hmax]. split.
    - rewrite <- dedup_nodes; assumption.
    - intros n Hn Huneq.
      rewrite <- dedup_ordering.
      rewrite <- dedup_nodes in Hn. apply Hmax; try assumption.
  Qed.      

  Definition remove_node (m : node__t) (B : bundle_type) :=
    let B' := dedup_bundle B in 
    {| nodes := set_remove eq_node__t_dec m (nodes B'); 
      intra := remove_edges_to m (intra B');
      inter := remove_edges_to m (inter B') |}.

   Lemma remove_sink_bundle : forall B m,
      is_bundle B ->      
      sink m B ->
      is_bundle (remove_node m B).
  Proof.
    intros B m Hbundle Hsink.  
    unfold remove_node.
    assert (is_bundle (dedup_bundle B)).
    {apply is_bundle_dedup; assumption. }
    apply is_bundle_remove_sink.
    - assumption.
    - unfold dedup_bundle.  simpl. apply NoDup_nodup.
    - apply dedup_sink; assumption.
  Qed.

  Lemma length_nodup : forall B (l : list B) (eq_dec : forall x y, {x=y}+{x<>y}),
      length (nodup eq_dec l) <= length l.
  Proof.
    intros B l eq_dec. induction l.
    - reflexivity.
    - simpl. assert (exists b, in_dec eq_dec a l=b).
      {exists (in_dec eq_dec a l). reflexivity. }
      destruct H as [b]. destruct b.
      + rewrite H.  lia.
      + rewrite H. rewrite length_cons. lia.
  Qed.

  Lemma dedup_le : forall B,
      bundle_size (dedup_bundle B) <= bundle_size B.
  Proof.
    intros B. destruct B.  
    unfold bundle_size.  unfold dedup_bundle. unfold nodes. simpl.
    apply length_nodup.
  Qed.

  Lemma NoDup_dedup : forall B, 
      NoDup (nodes (dedup_bundle B)).
  Proof.
    intros B. destruct B. simpl. apply NoDup_nodup.
  Qed. 

  Lemma remove_sink_smaller : forall B m,
      is_bundle B ->
      NoDup (nodes B) ->
      sink m B ->
      bundle_size (remove_node m B) < bundle_size B.
  Proof.
    intros B m Hbundle HNoDup Hsink.
    unfold remove_node. unfold bundle_size. simpl.
    assert (length (set_remove eq_node__t_dec m (nodup eq_node__t_dec (nodes B))) <
              length (nodup eq_node__t_dec (nodes B))).
    {apply set_remove_length_lt.
     rewrite nodup_fixed_point.
     - unfold sink in Hsink. destruct Hsink.
       unfold is_node_of in H. unfold set_In in H. assumption.
     - assumption. }
    assert (length (nodup eq_node__t_dec (nodes B)) <=
              length (nodes B)).
    {apply length_nodup. }
    lia.
  Qed. 

   Lemma remove_sink_dedup_smaller : forall B m,
      is_bundle B ->
      sink m B ->
      bundle_size (remove_node m (dedup_bundle B)) < bundle_size B.
  Proof.
    intros B m Hbundle Hsink.
    specialize remove_sink_smaller with (B:=(dedup_bundle B)) (m:=m).
    specialize dedup_le with (B:=B).  
    intros Hdedup Hsmaller. apply dedup_sink in Hsink; try assumption.
    apply is_bundle_dedup in Hbundle. 
    apply Nat.lt_le_trans with (m:=bundle_size(dedup_bundle B)); try assumption.
    apply Hsmaller; try assumption.
    apply NoDup_dedup.
  Qed. 

  (* Definition empty_bundle := {| nodes := []; intra := []; inter := [] |}.
   *)

  Corollary bundle_sink_induction : forall (P : bundle_type -> Prop),
      (forall B,
          (forall m, is_bundle B -> sink m B ->
                     P (remove_node m (dedup_bundle B))) ->
          P B) ->
      forall B, is_bundle B -> P B.
  Proof.
    intros P HIHm. apply bundle_size_induction_cor.
    intros B Hbundle HIHsize.  apply HIHm.
    intros m _ Hsink.  apply HIHsize.
    - assert (is_bundle (dedup_bundle B)).
      {apply is_bundle_dedup. assumption. }
      apply remove_sink_bundle; try assumption.
      apply dedup_sink; try assumption.
    - apply remove_sink_dedup_smaller; try assumption.
  Qed.

  Corollary bundle_sink_induction_alt : forall (P : bundle_type -> Prop),
      (forall B,
          (forall m, NoDup (nodes B) -> is_bundle B -> sink m B -> 
                     P (remove_node m B)) ->
          P B) ->
      forall B, NoDup (nodes B) -> is_bundle B -> P B.
  Proof.
    intros P HIHm B HNoDup. apply bundle_size_induction_cor.
    intros B0 HbundleB0 HIHsize.  apply HIHm.
    intros m HNoDup0 _  Hsink.  apply HIHsize.
    apply remove_sink_bundle; try assumption.
    apply remove_sink_smaller; try assumption.
  Qed.  

  


End BundleSizeInductionSig. 
       
