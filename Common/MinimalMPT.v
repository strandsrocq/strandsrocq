Require Import Coq.Init.Datatypes.
Require Import Arith.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.SetoidList.
Require Import Lia.
Require Import Relations.
Require Import Bool.

Import Coq.Lists.List.ListNotations.
Import Nat.
Open Scope list_scope.

Require Import RelMinimal.
Require Import Strands.
Require Import StrandsTactics.
Require Import Bundles.

Require Import UTerms.

Set Implicit Arguments.

Module MPT
  (Import U : UniverseSig)
  (Import T : UTermSig U)
  (Import St : StrandSig T)
  (Import SSp : StrandSpaceSig T St)
  (Import B : BundleSig T St SSp).
  (* New technique that generates a Prop covering all the cases
    Highlights:
    - can be "computed" by simpl and solved by "intuition"
    - adds a clause with the node index

    Acronyms:
    - mpti: minimal positive in trace with index
    - mpt:  minimal positive in trace
  *)

  Module Import StT := StrandsTactics U T St SSp.

  Section MPT.
    Definition is_mpti n i j α p :=
      (forall w, w < j-i -> ~p (uns (nth w α (⊖ τ)))) /\
      i <= j /\
      p (uns (nth (j-i) α (⊖ τ))) /\
      is_positive_term (nth (j-i) α (⊖ τ)) /\
      index n = j.

    Definition is_mpt n i α p :=
      exists j : nat,
        j < i /\
        is_mpti n 0 j α p /\
        index n = j.

    (* couldn't find this lemma in the standard libraries *)
    Lemma nth_S_cons_element :
      forall (a : sT) α d w, nth (w+1) (a :: α) d = nth w α d.
    Proof.
      intros a α d w. destruct w; try easy. simpl. now rewrite add_1_r.
    Qed.

    Lemma is_mpti_overflow1 :
      forall α n i j p, j < i -> ~ is_mpti n i j α p.
    Proof.
      unfold is_mpti; lia.
    Qed.
    Lemma is_mpti_overflow2 :
      forall n i j α p, length α <= j-i -> ~ is_mpti n i j α p.
    Proof.
      intros n i j α p Hlen. unfold not. unfold is_mpti.
      now rewrite (nth_overflow _ _ Hlen).
    Qed.
    Lemma is_mpti_head :
      forall t α n i j p, j = i -> is_mpti n i j (t :: α) p <-> p (uns t) /\ is_positive_term t /\ index n = i.
    Proof.
      intros. subst.
      unfold is_mpti. rewrite sub_diag. simpl. split; try easy.
    Qed.
    Lemma is_mpti_cons :
      forall t α n i j p, i < j -> is_mpti n i j (t :: α) p <-> (is_mpti n (i+1) j α p /\ ~ p (uns t)).
    Proof.
      intros t α n i j p Hlt.
      unfold is_mpti.
      assert ((forall w : nat, w < j - i -> ~ p (uns (nth w (t :: α) (⊖ τ))))  <->
                (forall w : nat, w < j - (i + 1) -> ~ p (uns (nth w α (⊖ τ)))) /\ ~ p (uns t)) as Hmin. {
                  split.
                  - intros Hall. split.
                    + intros w Hlt1. assert (w + 1 < j - i) by lia.
                      specialize (Hall (w+1) H).
                      now rewrite nth_S_cons_element in Hall.
                    + assert (0 < j - i) by lia. now specialize (Hall 0 H).
                  - intros Hall w Hlt1. destruct (eq_dec w 0).
                    + now subst.
                    + assert (w - 1 < j - (i + 1)) by lia.
                      destruct Hall as [Hall _].
                      specialize (Hall (w-1) H). rewrite <-(nth_S_cons_element t _ _ (w-1)) in Hall. now assert (w-1+1=w) by lia; rewrite H0 in Hall.
                }
      rewrite Hmin.
      assert (i <= j <-> i+1 <= j) by lia; rewrite H.
      assert (p (uns (nth (j - i) (t :: α) (⊖ τ))) =
                p (uns (nth (j - (i + 1)) α (⊖ τ)) )). {
                  rewrite <-(nth_S_cons_element t _ _ (j- (i+1))).
                  assert (j - (i + 1) + 1 = j-i) by lia. now rewrite H0.
                }
      rewrite H0.
      assert (is_positive_term (nth (j - i) (t :: α) (⊖ τ)) =
                is_positive_term (nth (j - (i + 1)) α (⊖ τ))). {
                  rewrite <-(nth_S_cons_element t _ _ (j- (i+1))).
                  assert (j - (i + 1) + 1 = j-i) by lia. now rewrite H1.
                }
      rewrite H1.
      intuition.
    Qed.

    (*
      Construct a Prop which is true if it holds (is_mpti (j-i) α p)
    *)
    Fixpoint mpti (n : node__t) (i : nat) (j : nat) (tr: list sT) (p : A -> Prop) : Prop :=
      match tr with
      | [] => False
      | t :: tr' =>
          if (lt_dec i j) then
            ~ p (uns t) /\ mpti n (i+1) j tr' p
          else if (eq_dec i j) then
            p (uns t) /\ is_positive_term t /\ index n = i
          else False
      end.

    Lemma mpti_overflow1 :
      forall α n i j p, j < i -> ~ mpti n i j α p.
    Proof.
      intros. unfold mpti. destruct α; try easy.
      destruct (lt_dec i j); try lia.
      destruct (eq_dec i j); try easy; try lia.
    Qed.
    Lemma mpti_overflow2 :
      forall α n i j p, length α <= j-i -> ~ mpti n i j α p.
    Proof.
      induction α.
      - easy.
      - intros n i j p Hlt. simpl.
        destruct (lt_dec i j).
        + simpl in Hlt.
          assert (length α <= j - (i+1)) as Hlia by lia.
          now specialize (IHα n (i+1) j p Hlia ).
        + simpl in Hlt. destruct (eq_dec i j); try lia.
    Qed.
    Lemma mpti_head :
      forall t α n i j p, j = i -> mpti n i j (t :: α) p <-> (p (uns t) /\ is_positive_term t /\ index n = i).
    Proof.
      intros. subst.
      unfold mpti.
      destruct (lt_dec); try lia.
      destruct (eq_dec); try easy.
    Qed.
    Lemma mpti_cons :
      forall t α n i j p, i < j -> mpti n i j (t :: α) p <-> (mpti n (i+1) j α p /\ ~ p (uns t)).
    Proof.
      intros.
      unfold mpti.
      now destruct (lt_dec); try lia.
    Qed.

    Lemma is_mpti_iff_mpti:
      forall α n i j p,
      is_mpti n i j α p <-> mpti n i j α p.
    Proof.
      induction α.
      - intros n i j p. simpl. unfold is_mpti, is_positive_term. now destruct (j-i).
      - intros n i j p.
        destruct (lt_dec j i) as [Hlt|Hgte].
        + specialize (mpti_overflow1 (a :: α) n p Hlt).
          now specialize (is_mpti_overflow1 (n:=n) (α:=a :: α) (p:=p) Hlt).
        + destruct (eq_dec j i) as [Heq|Hneq].
          * specialize (mpti_head a α n (i:=i) (j:=j) p Heq).
            specialize (is_mpti_head a α n (i:=i) (j:=j) p Heq). intuition.
          * assert (i < j) as Hlt by lia.
            specialize (mpti_cons a α n (i:=i) (j:=j) p Hlt) as H1.
            specialize (is_mpti_cons a α n (i:=i) (j:=j) p Hlt) as H2.
            specialize (IHα n (i+1) j p). intuition.
    Qed.

    (*
      Construct a Prop that is true if (is_mpt n i α p)
    *)
    Fixpoint mpt (n : node__t) (i : nat) tr p : Prop :=
      match i with
      | 0 => False
      | S j =>
          mpt n j tr p \/
          (mpti n 0 j tr p)
      end.

    Lemma is_mpt_then_mpt:
      forall n p α i,
      is_mpt n i α p -> mpt n i α p.
    Proof.
      induction i as [| i0 IH].
      - intros Hprop. now inversion Hprop.
      - intros Hprop. inversion Hprop as [j [Hlt [Hmin Hind]]].
        apply (is_mpti_iff_mpti) in Hmin as Hminprop.
        destruct (eq_dec j i0).
        + simpl. right. now subst.
        + assert (is_mpt n i0 α p) as H1. {
            exists j. split; try lia. split; try easy.
          }
          simpl. left. now specialize (IH H1).
    Qed.

    Lemma is_mpti_then_is_mpt :
      forall n α p,
      is_mpti n 0 (index n) α p ->
      is_mpt n (length α) α p.
    Proof.
      intros. unfold is_mpt.
      destruct (lt_dec (index n) (length α)) as [Hlt|Hgte].
      - now exists (index n).
      - assert (length α <= (index n) - 0) as Hlen by lia.
        now specialize (is_mpti_overflow2 (n:=n) (p:=p) Hlen) as Hover.
    Qed.

    Lemma originates_then_is_mpt :
      forall t n, originates t n ->
      is_mpt n
        (length (tr (strand n)))
        (tr (strand n))
        (fun x => t ⊏ x).
    Proof.
      intros t n Horig. simpl.
      unfold is_mpt.
      exists (index n). split. 2:split; try easy.
      - now apply (originates_lt (t:=t)).
      - unfold is_mpti.
        destruct Horig as [Hpos [Hsub Hmin]].
        rewrite sub_0_r.
        repeat split; try easy.
        intros w Hlt.
        assert ((strand n, w) ⟹+ n) as Hintra by (now apply lt_intrastrand_index).
        now specialize (Hmin _ Hintra).
        lia.
      Qed.

    Lemma originates_then_mpt:
      forall (α:list sT) (n:node__t) (t:A),
        α = tr (strand n) -> originates t n ->
          mpt n (length α) α (fun x => t ⊏ x).
    Proof.
      intros α n t Htrace Horig.
      apply originates_then_is_mpt in Horig.
      apply is_mpt_then_mpt.
      now rewrite Htrace.
    Qed.

    Lemma is_mpti_then_originates:
      forall t n,
      is_mpti n 0 (index n) (tr (strand n)) (fun x => t ⊏ x) ->
      originates t n.
    Proof.
      intros t n Hmpti.
      unfold is_mpti in Hmpti.
      destruct Hmpti as [Hmin [Hleq [Hp [Hpos Hind]]]].
      rewrite sub_0_r in *.
      unfold originates. repeat split; try easy.
      intros n' Hintra.
      apply intrastrand_same in Hintra as Hstrand.
      apply intrastrand_index_lt in Hintra as Hindex.
      specialize (Hmin (index n') Hindex).
      now rewrite <-Hstrand in Hmin.
    Qed.

    Corollary mpti_then_originates :
      forall t n,
      mpti n 0 (index n) (tr (strand n)) (fun x => t ⊏ x) ->
      originates t n.
    Proof.
      intros t n Hmpti.
      apply is_mpti_iff_mpti in Hmpti.
      now apply is_mpti_then_originates.
    Qed.

    (* some extra results *)
    Lemma is_mpti_unique :
      forall n α p,
      is_mpti n 0 (index n) α p ->
      forall j, j <> index n -> ~ is_mpti n 0 j α p.
    Proof.
      intros n α p His_mpti j Hneq.
      unfold not. intros Hcontra.
      destruct (lt_dec (index n) j) as [Hlt|Hgte].
      - destruct Hcontra as [Hnotp _].
        destruct His_mpti as [_ [_ [Hinp _]]].
        rewrite (sub_0_r) in *.
        now specialize (Hnotp (index n) Hlt).
      - assert (j < index n) as Hlt by lia.
        destruct Hcontra as [_ [_ [Hinp _]]].
        destruct His_mpti as [Hnotp _].
        rewrite (sub_0_r) in *.
        now specialize (Hnotp j Hlt).
    Qed.
  End MPT.

  Section MinimalMPT.
    Import B.
    Variable p : A -> Prop.
    Variable C : edge_set__t.

    Hypothesis C_is_bundle : is_bundle C.
    Hypothesis p_dec : forall t, { p t } + { ~ p t }.

    Definition N := filter (fun n => if (p_dec (uns_term n)) then true else false) (nodes_of C).

    Lemma N_iff_inC_p :
      forall n, In n N <-> In n (nodes_of C) /\ p (uns_term n).
    Proof.
      intros n.
      unfold N. rewrite (filter_In).
      now destruct (p_dec).
    Qed.

    Lemma N_is_sign_closed : sign_closed C N.
    Proof.
      intros Hsub m m' Hinm Hinm' Huns.
      repeat rewrite N_iff_inC_p.
      now rewrite Huns.
    Qed.

    Hypothesis np : node__t.
    Definition NW := filter (fun n => if (p_dec (uns_term n)) then if (bundle_ltb C_is_bundle n np) then true else false else false) (nodes_of C).
    Lemma NW_iff_inC_p :
      forall n, In n NW <-> In n (nodes_of C) /\ p (uns_term n) /\ C ⊢ n ≺ np.
    Proof.
      intros n.
      unfold NW. rewrite (filter_In).
      destruct (p_dec); destruct (bundle_ltb C_is_bundle n np) eqn:Hltb; try rewrite <-(bundle_ltb_iff_bundle_lt) in Hltb; try easy.
      rewrite (bundle_ltb_iff_bundle_lt). rewrite Hltb. easy.
    Qed.
    Lemma NW_is_weak_sign_closed : sign_closed_weak C NW.
    Proof.
      unfold sign_closed_weak.
      intros Hsub m Hinm Hnegm.
      (* rewrite (NW_iff_inC_p) in Hinm. *)
      specialize (Hsub _ Hinm).
      specialize (interstrand_exists_prec_positive_lt_uns C_is_bundle m) as Hexists.
      st_implication Hexists.
      destruct Hexists as [m' [Hnode [Hpos [Hect Huns]]]].
      exists m'.
      unfold set_In in Hinm. rewrite (NW_iff_inC_p) in Hinm.
      repeat split; try easy.
      unfold set_In.
      rewrite (NW_iff_inC_p).
      repeat split; try easy.
      - now rewrite <-Huns.
      - now apply (bundle_lt_multi Hect).
    Qed.

    Lemma minimal_N_then_is_mpti :
      forall α n,
      α = tr (strand n) ->
      set_In n N -> is_minimal (bundle_le C) n N ->
      is_mpti n 0 (index n) (α) p.
    Proof.
      intros α n Htrace Hin Hmin.
      unfold is_mpti.
      assert (Hin':=Hin).
      apply (N_iff_inC_p) in Hin as [HinC Hp].
      rewrite sub_0_r.
      assert (Hmin':=Hmin).
      unfold is_minimal in Hmin.
      specialize (C_is_bundle) as Hbundle.
      rewrite Htrace.
      repeat split; try lia; try easy.
      - intros w Hindex.
        (* Search (index ?X < index ?Y).
        Search (?X ⟹+ ?Y). *)
        specialize (index_lt_strand_implies_is_node_of C_is_bundle ((strand n), w) n) as Hin. simpl in Hin.
        st_implication Hin.
        specialize (Hmin Hin' (strand n, w) ).
        destruct (p_dec (uns_term ((strand n),w))); try easy.
        specialize (N_iff_inC_p ((strand n),w)) as [_ HinN].
        st_implication HinN.
        assert ((strand n, w) <> n). { unfold not. intros H. rewrite <-H in Hindex. simpl in Hindex. lia. }
        st_implication Hmin.
        specialize (index_le_strand_implies_bundle_le C_is_bundle ((strand n), w) n) as Hintra.
        now st_implication Hintra.
      - assert (node_subset_of N C) as Hsubset by
          (intros ? Hin; now apply N_iff_inC_p in Hin).
        specialize (N_is_sign_closed) as Hclosed.
        now specialize (minimal_is_positive C_is_bundle Hsubset Hclosed Hin' Hmin') as Hpos.
    Qed.

    Corollary minimal_N_then_mpti :
      forall α n,
      α = tr (strand n) ->
      set_In n N -> is_minimal (bundle_le C) n N ->
      mpti n 0 (index n) (α) p.
    Proof.
      intros. rewrite <-is_mpti_iff_mpti.
      now apply (minimal_N_then_is_mpti).
    Qed.

    Corollary minimal_N_then_is_mpt :
      forall α n,
      α = tr (strand n) ->
      set_In n N -> is_minimal (bundle_le C) n N ->
      is_mpt n (length α) α p.
    Proof.
      intros. apply is_mpti_then_is_mpt. now apply minimal_N_then_is_mpti.
    Qed.

    Corollary minimal_N_then_mpt :
      forall α n,
      α = tr (strand n) ->
      set_In n N -> is_minimal (bundle_le C) n N ->
      mpt n (length α) α p.
    Proof.
      intros. apply is_mpt_then_mpt. now apply minimal_N_then_is_mpt.
    Qed.

    Lemma minimal_NW_then_is_mpti :
      forall α n,
      α = tr (strand n) ->
      set_In n NW -> is_minimal (bundle_le C) n NW ->
      is_mpti n 0 (index n) (α) p.
    Proof.
      intros α n Htrace Hin Hmin.
      unfold is_mpti.
      assert (Hin':=Hin).
      apply (NW_iff_inC_p) in Hin as [HinC [Hp Hectn]].
      rewrite sub_0_r.
      assert (Hmin':=Hmin).
      unfold is_minimal in Hmin.
      specialize (C_is_bundle) as Hbundle.
      rewrite Htrace.
      repeat split; try lia; try easy.
      - intros w Hindex.
        (* Search (index ?X < index ?Y).
        Search (?X ⟹+ ?Y). *)
        specialize (index_lt_strand_implies_is_node_of C_is_bundle ((strand n), w) n) as Hin. simpl in Hin.
        st_implication Hin.
        specialize (Hmin Hin' (strand n, w) ).
        destruct (p_dec (uns_term ((strand n),w))); try easy.
        specialize (NW_iff_inC_p ((strand n),w)) as [_ HinN].
        specialize (index_lt_strand_implies_bundle_lt C_is_bundle (strand n, w) n) as Hect.
        st_implication Hect.
        specialize (bundle_lt_multi Hect Hectn) as Hectnp.
        st_implication HinN.
        assert ((strand n, w) <> n). { unfold not. intros H. rewrite <-H in Hindex. simpl in Hindex. lia. }
        st_implication Hmin.
        specialize (index_le_strand_implies_bundle_le C_is_bundle ((strand n), w) n) as Hintra.
        now st_implication Hintra.
      - assert (node_subset_of NW C) as Hsubset by
          (intros ? Hin; now apply NW_iff_inC_p in Hin).
        specialize (NW_is_weak_sign_closed) as Hclosed.
        now specialize (minimal_is_positive_weak Hsubset Hclosed Hin' Hmin') as Hpos.
    Qed.

    Corollary minimal_NW_then_mpti :
      forall α n,
      α = tr (strand n) ->
      set_In n NW -> is_minimal (bundle_le C) n NW ->
      mpti n 0 (index n) (α) p.
    Proof.
      intros. rewrite <-is_mpti_iff_mpti.
      now apply (minimal_NW_then_is_mpti).
    Qed.

    Corollary minimal_NW_then_is_mpt :
      forall α n,
      α = tr (strand n) ->
      set_In n NW -> is_minimal (bundle_le C) n NW ->
      is_mpt n (length α) α p.
    Proof.
      intros. apply is_mpti_then_is_mpt. now apply minimal_NW_then_is_mpti.
    Qed.

    Corollary minimal_NW_then_mpt :
      forall α n,
      α = tr (strand n) ->
      set_In n NW -> is_minimal (bundle_le C) n NW ->
      mpt n (length α) α p.
    Proof.
      intros. apply is_mpt_then_mpt. now apply minimal_NW_then_is_mpt.
    Qed.
  End MinimalMPT.

  Section MinimalOriginatesMPT.
    Import B.

    Variable C : edge_set__t.
    Hypothesis C_is_bundle : is_bundle C.

    Definition p t x := t ⊏ x.
    Lemma p_dec : forall t x : A, { p t x } + { ~ p t x }.
    Proof.
      intros t x. unfold p. destruct (A_subterm_dec t x); auto.
    Qed.
    Definition Nsubt t := N (p t) C (p_dec t).
    Definition Nsubtiff_inC_p t := N_iff_inC_p (p t) C (p_dec t).
    Definition minimal_Nsubt_then_mpt t := minimal_N_then_mpt (p t) C_is_bundle (p_dec t).
    Definition minimal_Nsubt_then_is_mpti t := minimal_N_then_is_mpti (p t) C_is_bundle (p_dec t).

    Corollary minimal_then_originates :
      forall n t,
        In n (Nsubt t) ->
        is_minimal (bundle_le C) n (Nsubt t) ->
        originates t n.
    Proof.
      intros n t Hin Hmin.
      apply mpti_then_originates.
      apply (minimal_N_then_mpti (p t) C_is_bundle (p_dec t)); try easy.
    Qed.

  End MinimalOriginatesMPT.
End MPT.
