From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.

From Stdlib Require Import Logic.Decidable.
Require Import LogicalFacts.

Require Import NS_orig_protocol.
Require Import NS_orig_responder.
Require Import RelMinimal.


Set Implicit Arguments.

(* This section covers the responder's guarantee in the NS protocol *)
Section auth_responder_guarantee.
  Variable s : Σ.
  Variables A B Na Nb : T.
  Variable Tname : T -> Prop.
  Variable C : bundle_type.
  Local Notation E := (edges C).

  Definition K__P_A (k : K) := k <> inv (PK A).

  Hypothesis s_is_NS_resp : NS_responder_strand Tname A B Na Nb s.
  Hypothesis s_strand_of_C : is_strand_of s C.
  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_NS : bundle_in_SS C (NS_StrandSpace Tname K__P_A).

  (*
    We define set NS in term of a characteristic NSp Prop. This set corresponds
    to set S of Lemma 4.4. We exploit the MPT library that provides a
    characterization of minimal elements as a single Prop which can be easily
    destructed and analyzed.

    This new technique does not require the property that regular strands never
    originate pairs [g ⋅ h] such that [s1 ⊏ h] or [s1 ⊏ g] as done in the original
    strand paper. The techniques leverage the fact that Nb is secret before s2.
  *)

  Fixpoint protected a :=
    match a with
    | $t => t <> Nb
    | A_τ | #_ => True
    | ⟨ g ⋅ g' ⟩_(k) =>
        (k = PK A /\ g = $Na /\ g' = $Nb) \/ (* second protocol message *)
        (protected g /\ protected g')
    | ⟨g⟩_(k) => protected g
    | g⋅h => protected g /\ protected h
    end.

  Definition NSp := fun t => ~protected t.
  #[local] Hint Unfold NSp : core.
  #[local] Hint Unfold uns term uns_term : core.

  Lemma protected_dec : forall t, { protected t } + { ~ protected t }.
  Proof.
    intros t.
    induction t; simpl; try tauto.
    - destruct (T_eq_dec t Nb); subst; tauto.
    - destruct t; simpl; try tauto.
      + destruct (T_eq_dec t Nb); subst; tauto.
      + simpl in IHt;
        destruct IHt; try tauto.
        destruct (K_eq_dec k (PK A));
        destruct (A_eq_dec t1 $Na);
        destruct (A_eq_dec t2 $Nb); subst;
        try (right; tauto). left; tauto.
  Qed.

  Lemma dec_protected : forall t, decidable ( protected t ).
  Proof.
    red; intros t. destruct (protected_dec t). now left. now right.
  Qed.
  #[local] Hint Resolve dec_protected : Terms_decidability.

  Lemma NSp_dec : forall t, { NSp t } + { ~ NSp t }.
  Proof.
    intros t. unfold NSp. destruct (protected_dec t).
    right; auto. now left.
  Qed.

  (* The actual set *)
  Definition NS := N NSp C NSp_dec. (* Set S of Lemma 4.4 *)
  Definition NS_iff_inC_NSp := N_iff_inC_p NSp C NSp_dec.

  (* charaterization through the MPT library *)
  Definition minimal_NS_then_mpt  := minimal_N_then_mpt  NSp C_is_bundle NSp_dec.

  (* first part of Lemma 4.4 - S has a minimal node *)
  Lemma NS_non_empty :
      NS <> nil.
  Proof.
    unfold NS.
    specialize (uns_term_of_c s_is_NS_resp) as Hutc.
    assert (NSp (uns_term (s,2))) as Hc. {
      autounfold.
      inversion s_is_NS_resp.
      now simplify_prop in |- *.
    }
    specialize (s_strand_of_C (s,2)) as HinC; simpl in HinC.
    inversion s_is_NS_resp.
    specialize (NS_iff_inC_NSp (s,2)) as [_ Hin].
    specialize (in_nil (a:=(s,2))) as Hcontra.
    st_implication HinC.
    intros Heq. rewrite Heq in Hin. intuition.
  Qed.

  Definition NS_has_minimal := exists_minimal eq_node__t_dec (bundle_le_dec E) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (E:=E)) (NS_non_empty).

  (* Proposition 4.2: Here [B] cannot be bound to the actual responder. This is
     the issue found by Gavin Lowe and then fixed in the NS protocol. A and B do
     not agree on the respective identities: B talks to A but A thinks she is talking
     to B'. *)
  Proposition noninjective_agreement :
    $Na <> $Nb -> originates_at_most_once_in C $Nb ->
      exists (s : Σ) (B' : T),
        NS_initiator_strand Tname A B' Na Nb s /\
        is_strand_of s C.
  Proof.
    intros diff_nonces Nb_originates_at_most_once.
    specialize (NS_has_minimal) as [m [Hin Hmin]]; try easy.
    assert (Hin':=Hin).
    apply (NS_iff_inC_NSp) in Hin' as [HinC HNSp].
    specialize uns_term_of_c as Hc.
    specialize (C_is_bundle) as Hbundle.
    specialize (s_strand_of_C) as Hstrace.
    pose (C_is_NS' := C_is_NS).
    specialize (C_is_NS' m HinC).
    inversion C_is_NS' as [s0 Hpen|A0 B0 Na0 Nb0 s0 Hini|A0 B0 Na0 Nb0 s0 Hres].

    - (* Penetrator *)
      assert (Hpen':=Hpen).
      inversion Hpen as [t i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k Hpenkey i Htrace|k h i Htrace|k h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace.
      all: specialize (minimal_NS_then_mpt Htrace Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      all: simplify_prop in Hmpti; try tauto.

      + simplify_prop in Hand using decidability.
        specialize (index_0_positive_originates m (t:=$Nb)) as Horig1.
        unfold is_positive in Horig1; st_implication Horig1.
        specialize (originates_Nb_implies_c (s:=s) (A:=A) (B:=B) (Na:=Na) (Nb:=Nb) (Tname:=Tname) s_is_NS_resp s_strand_of_C diff_nonces Nb_originates_at_most_once HinC Horig1)  as Horigs.
        rewrite Horigs in Htrace; simpl in Htrace.
        inversion s_is_NS_resp. apply (f_equal tr) in H0; simpl in H0.
        now rewrite <-Htrace in H0.

      + simplify_prop in Hand using decidability.
        destruct h; try tauto; destruct h1;
        unfold protected in *; try tauto.

      + destruct h; try tauto.
        push not in Hand using Terms_decidability.
        simplify_prop in Hand using decidability;
        try (unfold protected in *; tauto).

        (** we eliminate this case by expoiting the fact that the penetrator can never learn a secure symmetric key *)
        specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m,0) m) as Hnodeof;
        st_implication Hnodeof.

        specialize (inv_PK_U_never_originates_regular C_is_NS (U:=A)) as Hnever.
        specialize
          (penetrator_never_learn_secure_decryption_key
            C_is_bundle Hnever Hpen' Htrace Hnodeof) as Hkey.
        st_implication Hkey.

    -
      inversion Hini; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti;
      autounfold in Hmpti; simpl in Hmpti.
      inversion s_is_NS_resp. pose (s' := s).
      simplify_prop in Hmpti using decidability.

      1,2,3: specialize (index_0_positive_originates m (t:=$Nb)) as Horig1;
        unfold is_positive in Horig1; st_implication Horig1;
        specialize (originates_Nb_implies_c (s:=s') (A:=A) (B:=B) (Na:=Na) (Nb:=Nb) (Tname:=Tname) s_is_NS_resp s_strand_of_C diff_nonces Nb_originates_at_most_once HinC Horig1) as Horigs;
        st_implication Horigs; specialize (Horigs m Horig1).

      exists (strand m). exists B0. split; try tauto.
      specialize (last_node_implies_is_strand_of C_is_bundle m) as Hsof. rewrite <-H0 in Hsof.
      st_implication Hsof.

    - inversion Hres; apply (f_equal tr) in H0; simpl in H0.
      specialize (minimal_NS_then_mpt H0 Hin Hmin) as Hmpti; autounfold in Hmpti; simpl in Hmpti.
      inversion s_is_NS_resp. pose (s' := s).
      simplify_prop in Hmpti.
      simplify_prop in Hand using decidability.
      intuition idtac.
      simplify_prop in H7 using decidability.

      specialize (mpti_then_originates ($ Nb) m) as Horig1.
      simplify_term_in Horig1. st_implication Horig1. intuition.
      specialize (originates_Nb_implies_c (s:=s') (A:=A) (B:=B) (Na:=Na) (Nb:=Nb) (Tname:=Tname) s_is_NS_resp s_strand_of_C diff_nonces Nb_originates_at_most_once) as Horigs.
      specialize (Horigs m HinC Horig1).
      rewrite Horigs in H0; simpl in H0.
      inversion H0; subst; tauto.
  Qed.

  (* Proposition 4.8 -  injective agreement as in the original strand spaces paper **)
  Proposition injective_agreement_orig :
    $Na <> $Nb -> originates_at_most_once_in C $Nb ->
    originates_at_most_once_in C $Na ->
      exists !s B',
        NS_initiator_strand Tname A B' Na Nb s /\
        is_strand_of s C.
  Proof.
    intros diff_nonces Nb_originates_at_most_once Huorig.
    specialize (noninjective_agreement) as [s0 [B' [Hinis Hstrand]]]. all: try easy.
    exists s0. unfold unique. split.
    - exists B'. split; try easy.
      intros s' [Hinis' Hstrand'].
      inversion Hinis as [i _ Htraces].
      inversion Hinis' as [i' _ Htraces']. inversion Htraces. simplify_prop in H0.
    -
      intros s' [B'' [[Hinis' Hstrand'] _]].
      pose (s0' := s0).
      pose (s'' := s').
      destruct Hinis.
      destruct Hinis'.
      assert (is_node_of (s0',0) C) as Hnode by (apply Hstrand; [easy | simpl; lia]).
      assert (is_node_of (s'',0) C) as Hnode' by (apply Hstrand'; [easy | simpl; lia]).
      specialize (index_0_positive_originates (s'',0) (t:=$Na)) as Horig'.
      specialize (index_0_positive_originates (s0',0) (t:=$Na)) as Horig.
      assert ($Na ⊏ uns_term (s'', 0) /\ $Na ⊏ uns_term (s0', 0) /\ is_positive (s'',0) /\ is_positive (s0',0) /\ index (s'',0) = 0 /\ index (s0',0) = 0). {
        unfold is_positive. repeat simplify_term. tauto.
      }
      st_implication Horig; st_implication Horig'.
      specialize (Huorig _ _ Hnode Hnode' Horig Horig').
      inversion Huorig; now subst.
  Qed.

  (* We now prove standard injective agreement with no extra assumptions
     with respect to non-injective agreement *)
  Proposition injectivity :
    $Na <> $Nb -> originates_at_most_once_in C $Nb ->
      forall U U' s',
        is_strand_of s' C ->
        NS_responder_strand Tname U U' Na Nb s' ->
        s' = s.
  Proof.
    intros Hdiff Huorig U U' s' Hstrand' Hini'.
    specialize s_is_NS_resp as Hini.
    pose (s1 := s).
    pose (s1' := s').
    destruct Hini.
    destruct Hini'.
    assert (originates $Nb (s1, 1)) as Horig. {
      apply (mpti_then_originates $Nb (s1,1)).
      simplify_term. split. unfold not. intros.
      simplify_prop in H1; subst. split; auto 10.
    }
    assert (originates $Nb (s1', 1)) as Horig'. {
      apply (mpti_then_originates $Nb (s1',1)).
      simplify_term. split. unfold not. intros.
      simplify_prop in H1; subst. split; auto 10.
    }
    assert (is_node_of (s1,1) C) as Hnode by (apply s_strand_of_C; [easy | simpl; lia]).
    assert (is_node_of (s1',1) C) as Hnode' by (apply Hstrand'; [easy | simpl; lia]).
    specialize (Huorig _ _ Hnode Hnode' Horig Horig').
    inversion Huorig; now subst.
  Qed.

  Corollary injective_agreement :
    $Na <> $Nb -> originates_at_most_once_in C $Nb ->
    (
      exists (s : Σ) (B' : T),
        NS_initiator_strand Tname A B' Na Nb s /\
        is_strand_of s C
    )
    /\
    (
      forall s',
        is_strand_of s' C ->
        NS_responder_strand Tname A B Na Nb s' ->
        s' = s
    ).
  Proof.
    intros Hdiff Huniq. split.
    - now apply noninjective_agreement.
    - now apply injectivity.
  Qed.

End auth_responder_guarantee.

Section NSResponderSanity.
  (** * Sanity check: Lowe's attack
    We exhibit the Lowe attack to the original Needham-Schroeder protocol
    as a sanity check: the protocol executes and satisfies all of the assumptions 
    of the security lemmas that, in fact, do not constraint B's identifier.
    So the attack is actually accounted for in the agreement result.
  *)

  Notation A  := (Text 0).
  Notation B  := (Text 1).
  Notation Na := (Text 2).
  Notation Nb := (Text 3).
  Notation P  := (Text 4). (* The Penetrator's participant *)
  Notation Tname := (fun t => t = Text 0 \/ t = Text 1 \/ t = Text 4).

  (* The initiator runs a session with [P], the penetrator *)
  Notation s_ini := (0, [
      ⊕ ⟨ $Na ⋅ $A ⟩_(PK P);
      ⊖ ⟨ $Na ⋅ $Nb ⟩_(PK A);   (* Here [P] is missing, which allows the attack *)
      ⊕ ⟨ $Nb ⟩_(PK P) ]).
  (* The responder believes [A] wants to establish the session with them *)
  Notation s_res := (1, [
      ⊖ ⟨ $Na ⋅ $A ⟩_(PK B);
      ⊕ ⟨ $Na ⋅ $Nb ⟩_(PK A);   (* Here [B] is missing, which allows the attack *)
      ⊖ ⟨ $Nb ⟩_(PK B) ]).
  Notation s_pen_K1 := (2, [
      ⊕ #(inv (PK P)) ]).          (* [P] knows their inverse key *)
      
  Notation s_pen_K2 := (3, [
      ⊕ # (PK B) ]).                (* [P] knows [B]'s public key *)

  Notation s_pen_D1 := (4, [
      ⊖ #(inv (PK P)); 
      ⊖ ⟨ $Na ⋅ $A ⟩_(PK P);
      ⊕ $Na ⋅ $A ]).            (* Decrypt the first message *)
      
  Notation s_pen_E1 := (5, [
      ⊖ # (PK B); 
      ⊖ $Na ⋅ $A; 
      ⊕ ⟨ $Na ⋅ $A ⟩_(PK B) ]). (* Re-encrypt under PK B *)
      
  Notation s_pen_D2 := (6, [
      ⊖ #(inv (PK P)); 
      ⊖ ⟨ $Nb ⟩_(PK P); 
      ⊕ $Nb ]).                 (* Decrypt the last message *)

  Notation s_pen_E2 := (7, [
      ⊖ # (PK B); 
      ⊖ $Nb; 
      ⊕ ⟨ $Nb ⟩_(PK B) ]).      (* Re-encrypt under PK B *)

  (** The Low attack.  The lists are reversed because each [IndBundle] constructor conses onto their heads. *)
  Definition C : bundle_type :=
    {|
      nodes := rev [
        (s_pen_K1,0);   (* P -> P : inv (PK P)            *)
        (s_pen_D1,0);
        (s_pen_K2,0);   (* P -> P : PK B                  *)
        (s_pen_E1,0);
        (s_pen_D2,0);
        (s_pen_E2,0);    
        (s_ini,0);      (* A -> P : ⟨ $Na ⋅ $A ⟩_(PK P)   *)
        (s_pen_D1,1);
        (s_pen_D1,2);   (* P -> P : $Na ⋅ $A              *)
        (s_pen_E1,1);
        (s_pen_E1,2);   (* P -> B : ⟨ $Na ⋅ $A ⟩_(PK B)   *)
        (s_res,0);
        (s_res,1);      (* B -> A : ⟨ $Na ⋅ $Nb ⟩_(PK A)  *)
        (s_ini,1);
        (s_ini,2);      (* A -> P : ⟨ $Nb ⟩_(PK P)        *)
        (s_pen_D2,1);
        (s_pen_D2,2);   (* P -> P : $Nb                   *)
        (s_pen_E2,1);
        (s_pen_E2,2);   (* P -> B : ⟨ $Nb ⟩_(PK B)        *)
        (s_res,2)
      ];
      intra := rev [
        ((s_pen_D1,0),(s_pen_D1,1));
        ((s_pen_D1,1),(s_pen_D1,2));
        ((s_pen_E1,0),(s_pen_E1,1));
        ((s_pen_E1,1),(s_pen_E1,2));
        ((s_res,0),(s_res,1));
        ((s_ini,0),(s_ini,1));
        ((s_ini,1),(s_ini,2));
        ((s_pen_D2,0),(s_pen_D2,1));
        ((s_pen_D2,1),(s_pen_D2,2));
        ((s_pen_E2,0),(s_pen_E2,1));
        ((s_pen_E2,1),(s_pen_E2,2));
        ((s_res,1),(s_res,2))
        ];
      inter := rev [
        ((s_pen_K1,0),(s_pen_D1,0));  (* P -> P : inv (PK P)            *)
        ((s_pen_K2,0),(s_pen_E1,0));  (* P -> P : PK B                  *)
        ((s_pen_K1,0),(s_pen_D2,0));  (* P -> P : inv (PK P)            *)
        ((s_pen_K2,0),(s_pen_E2,0));  (* P -> P : PK B                  *)
        ((s_ini,0),(s_pen_D1,1));     (* A -> P : ⟨ $Na ⋅ $A ⟩_(PK P)   *)
        ((s_pen_D1,2),(s_pen_E1,1));  (* P -> P : $Na ⋅ $A              *)
        ((s_pen_E1,2),(s_res,0));     (* P -> B : ⟨ $Na ⋅ $A ⟩_(PK B)   *)
        ((s_res,1),(s_ini,1));        (* B -> A : ⟨ $Na ⋅ $Nb ⟩_(PK A)  *)
        ((s_ini,2),(s_pen_D2,1));     (* A -> P : ⟨ $Nb ⟩_(PK P)        *)
        ((s_pen_D2,2),(s_pen_E2,1));  (* P -> P : $Nb                   *)
        ((s_pen_E2,2),(s_res,2))      (* P -> B : ⟨ $Nb ⟩_(PK B)        *)
        ]
    |}.

  (** The roles carry a premise: [Tname] must hold of the two names and not of the
      nonces.  This is where the choice of [Tname] is validated, since an empty one
      would leave the roles uninhabited and the whole guarantee vacuous. *)
  Lemma s_ini_NS : NS_initiator_strand Tname A P Na Nb s_ini.
  Proof. solve_role. Qed.
  Lemma s_res_NS : NS_responder_strand Tname A B Na Nb s_res.
  Proof. solve_role. Qed.
  Lemma s_pen_K1_NS : penetrator_strand (K__P_A A) s_pen_K1.
  Proof. solve_role. Qed.
  Lemma s_pen_K2_NS : penetrator_strand (K__P_A A) s_pen_K2.
  Proof. solve_role. Qed.
  Lemma s_pen_E1_NS : penetrator_strand (K__P_A A) s_pen_E1.
  Proof. solve_role. Qed.
  Lemma s_pen_E2_NS : penetrator_strand (K__P_A A) s_pen_E2.
  Proof. solve_role. Qed.
  Lemma s_pen_D1_NS : penetrator_strand (K__P_A A) s_pen_D1.
  Proof. solve_role. Qed.
  Lemma s_pen_D2_NS : penetrator_strand (K__P_A A) s_pen_D2.
  Proof. solve_role. Qed.
    
  Create HintDb sanity.
  #[local] Hint Constructors NS_StrandSpace penetrator_strand : sanity.
  #[local] Hint Resolve s_ini_NS s_res_NS s_pen_D1_NS s_pen_D2_NS s_pen_E1_NS s_pen_E2_NS s_pen_K1_NS s_pen_K2_NS: sanity.

  Lemma C_is_bundle : is_bundle C.
  Proof. ind_bundle. Qed.

  Lemma s_res_strand_C : is_strand_of s_res C.
  Proof. solve_is_strand_of. Qed.

  Lemma C_is_NS : bundle_in_SS C (NS_StrandSpace Tname (K__P_A A)).
  Proof. solve_bundle_in_SS. Qed.

  (** [$Nb] is originated at most once, in fact exactly once at [(s_res,1)]. *)
  Lemma C_Nb_at_most_once : originates_at_most_once_in C $Nb.
  Proof. solve_at_most_once_in. Qed.

  Lemma Na_neq_Nb : $Na <> $Nb.
  Proof. discriminate. Qed.

  (** The conclusion is what we already know by construction since we have exactly one
      initiator and one responder in [C]. So, the important part is that the term
      typechecks, which is possible only if the six hypotheses of [injective_agreement]
      hold at once, i.e., the guarantee is not vacuous. *)
  Lemma injective_agreement_sanity :
    (
      exists (s0 : Σ) (B' : T),
        NS_initiator_strand Tname A B' Na Nb s0 /\
        is_strand_of s0 C
    )
    /\
    (
      forall s' : Σ,
        is_strand_of s' C ->
        NS_responder_strand Tname A B Na Nb s' ->
        s' = s_res
    ).
  Proof.
    exact (
      injective_agreement
        s_res_NS
        s_res_strand_C
        C_is_bundle
        C_is_NS
        Na_neq_Nb
        C_Nb_at_most_once
      ).
  Qed.

End NSResponderSanity.