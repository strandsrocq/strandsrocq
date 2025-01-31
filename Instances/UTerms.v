Require Import Coq.Init.Datatypes.
Require Import Arith.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.SetoidList.
Require Import Relations.
Require Import Bool.
Require Import Coq.Logic.Decidable.
Import Coq.Lists.List.ListNotations.
Import Nat.

Require Import Strands.
Require Import Bundles.

Open Scope list_scope.

Set Implicit Arguments.

(* The UniverseSig module type defines the atomic terms and keys, and their basic properties *)
Module Type UniverseSig.
  (* Universe of atomic terms and keys *)
  Parameter U : Set.
  Parameter U_leb : U -> U -> bool.

  Axiom U_leb_total :
    forall a b, U_leb a b = true \/ U_leb b a = true.
  Axiom U_leb_antisymmetric :
    forall a b, U_leb a b = true -> U_leb b a = true -> a = b.
  Axiom U_eq_dec :
    forall a a' : U, { a = a' } + { a <> a'}.
End UniverseSig.

Module Type UTermSig (Import Un : UniverseSig) <: TermSig.
  (** *
    Concrete implementation of terms, following the original Strand Spaces paper [IEEE S&P'98].

    We assume a universe [Un] whose equality is decidable. Atomic terms [T] and keys [K] are built from [Un]. Function [inv] returns the inverse of a key. Terms [𝔸] are defined inductively from [T] and [K] using an encryption and a pairing constructor. Recall that [τ] from [Strands.v] represents a void term which never appears in actual protocol traces.

    _NOTE_: Terms can be extended as needed. Proofs over strands, bundles and minimality (i.e., proof techniques) are independent of terms and do not need to be modified or reproved if terms are modified.
  *)

  (* On top of Un's U it we define texts and keys *)
  Inductive T := Text : U -> T. (* Atomic terms *)
  Definition T_leb a b :=
    match (a, b) with (Text ua, Text ub) => U_leb ua ub end.

  Lemma T_leb_antisymmetric :
    forall a b, T_leb a b = true -> T_leb b a = true -> a = b.
  Proof.
    intros. destruct a, b. unfold T_leb in *.
    specialize (U_leb_antisymmetric H H0) as Heq; now subst.
  Qed.

  Lemma T_leb_total :
    forall a b, T_leb a b = true \/ T_leb b a = true.
  Proof.
    intros. destruct a, b. unfold T_leb in *. apply U_leb_total.
  Qed.

  (* We have three disjoint classes of symmetric keys, which is useful, e.g., in the KMP example *)
  Inductive K :=
    | SymK : U -> K (* Symmetric keys - first class*)
    | SymK' : U -> K (* Symmetric keys - second class *)
    | SymKA : U -> K (* Symmetric keys always available to the penetrator *)
    | SymKP : T -> T -> K
    | PubK : T -> K
    | PrivK : T -> K.

  Definition inv k := match k with
    | SymK a => SymK a
    | SymK' a => SymK' a
    | SymKA a => SymKA a
    | SymKP a b => SymKP a b
    | PubK a => PrivK a
    | PrivK a => PubK a
  end.

  Definition PK a := PubK a.

  Lemma PK_injective : forall A B, PK A = PK B -> A = B.
  Proof.
    intros. now inversion H.
  Qed.

  Definition SK a b :=
    if T_leb a b then SymKP a b else SymKP b a.

  Lemma SK_symmetric: forall A B, SK A B = inv (SK A B).
  Proof.
    intros. unfold SK, inv. now destruct (T_leb A B).
  Qed.

  Lemma SK_bidirectional : forall A B, SK A B = SK B A.
  Proof.
    intros. unfold SK. destruct (T_leb A B) eqn:H;  destruct (T_leb B A) eqn:H'; try easy.
    specialize (T_leb_antisymmetric _ _ H H') as H''.
    - now subst.
    - specialize (T_leb_total A B) as Htot. destruct Htot; now rewrite H0 in *.
  Qed.

  Lemma SK_injective : forall A B A' B',
    SK A B = SK A' B' -> (A = A' /\ B = B') \/ (A = B' /\ B = A').
  Proof.
    intros. unfold SK in *. destruct (T_leb A B) eqn:HAB; destruct (T_leb A' B') eqn:HAB'; inversion H; subst; auto.
  Qed.

  Inductive 𝔸 :=
    | A_τ : 𝔸
    | A_T : T -> 𝔸
    | A_K : K -> 𝔸
    | A_encr : K -> 𝔸 -> 𝔸
    | A_join : 𝔸 -> 𝔸 -> 𝔸.

  (* Free encryption here holds as a theorem, bc A is inductively generated. *)
  (* Theorem free_encr : forall m m' K K', ⟨m⟩_K = ⟨m'⟩_K' -> m = m' /\ K = K'.
  Proof.
    intros m m' K K' H.
    inversion H.
    split.
    all: reflexivity.
  Qed. *)
  #[global] Hint Resolve U_eq_dec : core.

  Notation "'$' t" := (A_T t) (at level 9).
  Notation "'#' k" := (A_K k) (at level 9).
  Notation "k '⁻¹'" := (inv k) (at level 8).
  Notation "'⟨' m '⟩_' K" := (A_encr K m) (at level 60).
  Notation "a '⋅' b" := (A_join a b) (at level 60).

  (* Subterm relation *)
  Section Subterm.

    Fixpoint subterm (a a' : 𝔸) := match a' with
      | A_τ | $_ | #_ => a = a'
      | ⟨g⟩_ _  => a = a' \/ subterm a g (* does not enter keys *)
      | g ⋅ h => a = a' \/ subterm a g \/ subterm a h
    end.

    (** Subterm is reflexive *)
    Lemma eq_then_sub : forall a, subterm a a.
    Proof.
      intros a.
      destruct a; simpl; try easy; try now left.
    Qed.

  End Subterm.

  Section TermDecidability.
    Hint Resolve U_eq_dec : core.

    Lemma A_eq_dec : forall a a' : 𝔸, { a = a' } + { a <> a'}.
    Proof.
      repeat (decide equality).
    Defined.

    Lemma A_subterm_dec : forall a a', { subterm a a' } + { ~(subterm a a')}.
    Proof.
      intros a a'. unfold subterm. unfold subterm.
      induction a' as [| | | k a' IHa' | a'1 IHa'1 a'2 IHa'2].
      all: try (repeat decide equality).
      - destruct (A_eq_dec a (⟨a'⟩_k)); auto.
        destruct IHa'; auto.
        right. intro. now destruct H.
      - destruct (A_eq_dec a (a'1 ⋅ a'2)); auto.
        destruct IHa'2; auto; destruct IHa'1; auto.
        right. intro Hcontra.
        repeat (destruct Hcontra as [Hcontra|Hcontra]; auto).
    Defined.

    Lemma T_eq_dec : forall t t' : T, { t = t' } + { t <> t' }.
    Proof.
      intros t t'. repeat (decide equality).
    Defined.

    Lemma K_eq_dec : forall k k' : K, { k = k' } + { k <> k' }.
    Proof.
      intros k k'. repeat (decide equality).
    Defined.

    (** The following lemmas are used in proof automation form [LogicalFacts.v] that allows for simplifying logical propositions leveraging on decidability. *)
    Lemma dec_eq_A : forall (x y: 𝔸),
    decidable (x = y).
    Proof.
      red; intros. destruct (A_eq_dec x y); subst.
      left; auto. right; auto.
    Qed.

    Lemma dec_eq_T : forall (x y : T),
      decidable (x = y).
    Proof.
      red; intros. destruct (T_eq_dec x y); subst.
      left; auto. right; auto.
    Qed.

    Lemma dec_eq_K : forall (x y : K),
      decidable (x = y).
    Proof.
      red; intros. destruct (K_eq_dec x y); subst.
      left; auto. right; auto.
    Qed.

    Lemma dec_subterm : forall (x y : 𝔸),
      decidable (subterm x y).
    Proof.
      red; intros. destruct (A_subterm_dec
      x y); subst.
      left; auto. right; auto.
    Qed.

  End TermDecidability.

  #[global] Hint Resolve dec_eq_A dec_eq_T dec_eq_K dec_subterm : Terms_decidability.

  (** We are now ready to instantiate the generic [TermSig] to the terms defined in the above sections. This makes all general results and proof techniques for strands and bundles available over terms [𝔸]. *)
  Definition A := 𝔸.
  Definition τ := A_τ.
End UTermSig.

Module UTerm (Un : UniverseSig) <: UTermSig Un.
  Include UTermSig Un.
End UTerm.
