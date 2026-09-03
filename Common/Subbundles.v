

From Stdlib Require Import Init.Datatypes.
From Stdlib Require Import Arith.
From Stdlib Require Import ListSet.
From Stdlib Require Import Lists.List.
(* From Stdlib Require Import Lists.List Stdlib.Lists.ListSet Stdlib.Bool.Bool Stdlib.Bool.Sumbool. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From Stdlib Require Import Relations.Relation_Operators.
Require Import RelMinimal.
Import Nat.

Require Import Strands.
Require Import BundleRelations.
Require Import Bundles.

Import Stdlib.Lists.List.ListNotations.

Open Scope list_scope.

Set Implicit Arguments.

Module Subbundles  
    (Import T : TermSig)
    (Import St : StrandSig T)
    (Import SSp : StrandSpaceSig T St)
    (Import B : BundleSig T St SSp).

(*         
    1. Define sub_structure : bundle_type -> bundle_type -> Prop
    to mean that the nodes of b1 are included in the nodes of
    b2, and each (intra,inter) edge of b1 is an edge of b2.
*)

(* Observation: It would be nice to have the proof of b1 being a bundle embedded in the bundle record as an SProp -- having an SProp would allow us to forget how the bundle was proved to be such (directly or via InductiveBundle) and just focus on the properties it has even when comparing with other bundles. 
Of course this would change the Definition(s) below, but would make them a little bit more "name" accurate. 
*)
Definition sub_structure (b1 : bundle_type) (b2 : bundle_type) : Prop := 
    (forall n, is_node_of n b1 -> is_node_of n b2) /\ 
    (forall e, In e (intra b1) -> In e (intra b2)) /\ 
    (forall e, In e (inter b1) -> In e (inter b2)).

(* 
    2. Define sub_bundle : bundle_type -> bundle_type -> Prop
    meaning that b1 is a sub-structure of b2 and b1, b2 are
    both bundles. 
*)
Definition sub_bundle (b1 : bundle_type) (b2 : bundle_type) : Prop := 
    sub_structure b1 b2 /\ is_bundle b1 /\ is_bundle b2.

(*        
3.  Lemma: Suppose that b2 is a bundle, and b1 is a substructure of b2.
            Then b1 is a bundle iff

            (a) the nodes of b1 are downward closed relative to the
                ordering of b2, and

            (b) an edge is in intra (respectively inter) of b1 iff it
                is in intra (respectively inter) of b2 and both
                endpoints are nodes in b1.
*)
Lemma sub_structure_char_bundle (b1 : bundle_type) (b2 : bundle_type) :
    sub_structure b1 b2 ->
        is_bundle b2 ->
            (is_bundle b1 <-> 
                (* (a) the nodes of b1 are downward closed relative to the
                ordering of b2, and *)
                (forall n2, is_node_of n2 b1 -> 
                    exists n1, is_node_of n1 b1 /\ (edges b2) ⊢ n1 ≺ n2) /\
                (* (b) an edge is in intra (respectively inter) of b1 iff it
                is in intra (respectively inter) of b2 and both
                endpoints are nodes in b1. *)
                (forall n1 n2, 
                    (In (n1, n2) (intra b1) <-> In (n1, n2) (intra b2)) /\ 
                    is_node_of n1 b1 /\ 
                    is_node_of n2 b1
                ) /\
                (forall n1 n2, 
                    (In (n1, n2) (inter b1) <-> In (n1, n2) (inter b2)) /\ 
                    is_node_of n1 b1 /\ 
                    is_node_of n2 b1
                )
            ). 
Proof. 
Admitted.

(* 4.  Lemma:
    Suppose b1 is a sub-bundle of b2 and l is the list of
    nodes of b2 but not b1 (so l is the set-difference).  
    If n
    is preceq-b2 minimal in l, then b1' is a sub-bundle of b2,
    where

    nodes b1' = add n (nodes b1);

    intra b1' = union (intra b1) (goes-to n (intra b2))

    inter b1' = union (inter b1) (goes-to n (inter b2))

    writing (goes-to n edges) for the subset of edges of the
    form (n_0,n) for some n_0. 
*)
Definition goes_to (n : node__t) (es : set edge__t) : set edge__t :=
    ListSet.set_fold_left 
      (fun acc e =>
         if eq_node__t_dec n (snd e)
         then ListSet.set_add eq_edge__t_dec e acc
         else acc) 
      es 
      (ListSet.empty_set edge__t).

Lemma subbundle_add_minimal_node (b1 : bundle_type) (b2 : bundle_type) :
    sub_bundle b1 b2 ->
        let l := ListSet.set_diff eq_node__t_dec (nodes b2) (nodes b1) in
        forall n, is_minimal (bundle_le (edges b2)) n l -> 
            let b1' := {| 
                nodes := ListSet.set_add eq_node__t_dec n (nodes b1); 
                intra := ListSet.set_union eq_edge__t_dec (intra b1) (goes_to n (intra b1));
                inter := ListSet.set_union eq_edge__t_dec (inter b1) (goes_to n (inter b1));
            |} in 
            sub_bundle b1' b2.
Proof.
Admitted.

(* **************** *)
(*

        1.  Define sub_structure : bundle_type -> bundle_type -> Prop
            to mean that the nodes of b1 are included in the nodes of
            b2, and each (intra,inter) edge of b1 is an edge of b2.

        2.  Define sub_bundle : bundle_type -> bundle_type -> Prop
            meaning that b1 is a sub-structure of b2 and b1, b2 are
            both bundles.

        3.  Lemma:  Suppose that b2 is a bundle, and b1 is a
            substructure of b2.

            Then b1 is a bundle iff

            (a) the nodes of b1 are downward closed relative to the
                ordering of b2, and

            (b) an edge is in intra (respectively inter) of b1 iff it
                is in intra (respectively inter) of b2 and both
                endpoints are nodes in b1.

        4.  Suppose b1 is a sub-bundle of b2 and l is the list of
            nodes of b2 but not b1 (so l is the set-difference).  If n
            is preceq-b2 minimal in l, then b1' is a sub-bundle of b2,
            where

            nodes b1' = add n (nodes b1);

            intra b1' = union (intra b1) (goes-to n (intra b2))

            inter b1' = union (inter b1) (goes-to n (inter b2))

            writing (goes-to n edges) for the subset of edges of the
            form (n_0,n) for some n_0.

        5.  Now in Semantics.v, we should be able to prove by
            induction on the set-difference l that:

            Theorem:  Suppose that b1 is a sub-bundle of b2 with
            set-difference l, and tau_non_originating.  Then:

            exists T T2 full_trace pool_strand, P ⊨ T /\
              extends_pool_trace T full_trace /\ represents_pool b1 T
              full_trace pool_strand

            and pool_reachable_from P T T2 /\ extends_pool_trace T2
              full_trace /\ represents_pool b2 T2 full_trace
              pool_strand.

            In the induction step we use the theorem in (4) to find
            the node and edges to add, and that determines an
            operational semantics step.  

*) 
End Subbundles.
