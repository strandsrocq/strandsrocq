(*
  In this file we finally prove the secrecy guarantees from
    "Secure Key Management Policies in Strand Spaces" by Focardi and Luccio
  using their original closure.
*)
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

Require Import DefaultInstances.
Require Import Penetrator.
Require Import RelMinimal.

Require Import KMP_policies.
Require Import KMP_protocol.
Require Import KMP_closure.

Set Implicit Arguments.

(* This section covers the secrecy guarantees in the protocol KMP as induced by a given policy *)
Section secrecy_guarantee.

  (* Assume a given policy π and its induced strand space Σ *)
  Variable π : policy__t.
  Variable C : edge_set__t.

  Hypothesis C_is_bundle : is_bundle C.
  Hypothesis C_is_KMP : C_is_SS C (KMP_StrandSpace π).

  (*
    Terms have initial type.
    If a key k is s.t. K_d k, then its initial type is the type assigned when it originated; Any other term m (incl. keys such that ~ K_d m) have initial type D.
  *)
  Fixpoint initial_type_rec N (m : 𝔸) : KEY_DATA_T :=
    match m, N with
    | #k, n::NL => match tr (strand n) with
                      | [⊕ ⟨ #k' ⋅ ($KT) ⟩_(mk)] =>
                        if K_eq_dec k k' then
                          (if K_d_dec k then
                            (if K_m_dec mk then
                              (KDn KT)
                            else initial_type_rec NL m)
                          else initial_type_rec NL m)
                        else initial_type_rec NL m
                      | _ => initial_type_rec NL m
                      end
    | _, _ => D
    end.

  Definition initial_type := initial_type_rec (nodes_of C).

  Lemma initial_type_char :
    forall m,
      match m with
      | #k =>
        (K_d k ->
          forall n (KT : KEY_T) mk, K_m mk -> is_node_of n C -> [⊕ ⟨ #k ⋅ $KT ⟩_(mk)] = tr (strand n) ->
            initial_type m = (KDn KT)
        ) /\
        (~K_d k -> initial_type m = D)
      | _ => initial_type m = D
      end.
  Proof.
    intros m.
    destruct m eqn:Hm; unfold initial_type, is_node_of in *;
    unfold C_is_SS, is_node_of in C_is_KMP;
    induction (nodes_of C) as [|n' nl IHnl] ; try easy.
    assert (forall n : node__t, set_In n nl -> KMP_StrandSpace π (strand n)) as C_is_KMP' by (st_implication C_is_KMP).
    split.
    - intros Hd n KT mk Hmk Hin Htr. destruct Hin as [Hneq | Hin].
      + subst. unfold initial_type_rec. rewrite <- Htr. destruct (K_eq_dec k k) as [? | ?]; destruct (K_d_dec k) as [_ | Hnk]; destruct (K_m_dec mk) as [_ | Hnmk]; try easy.
      + destruct (IHnl C_is_KMP') as [IHnld _]. specialize (IHnld Hd n KT mk Hmk Hin Htr) as IHnldn. simpl.
        destruct (tr (strand n')) as [|s0 sl] eqn:Htrn'; try easy.
        destruct s0 as [a|a]; try easy.
        destruct a; try easy.
        destruct a; try easy.
        destruct a1 eqn:Ha1; destruct a2; try easy.
        destruct sl; try easy.
        destruct (K_eq_dec k k1) as [? | ?]; destruct (K_d_dec k1) as [Hk1 | ?]; destruct (K_d_dec k) as [Hk | ?]; destruct (K_m_dec k0) as [Hk0 | ?]; try inversion e as [e']; try rewrite <- e' in *; try easy.
        (* This last case is a contradiction *)
        specialize (C_is_KMP n) as Hn_kmp; specialize (C_is_KMP n') as Hn'_kmp. symmetry in Ha1, e'.
        st_implication Hn_kmp; st_implication Hn'_kmp.
        inversion Hn_kmp as [s0 Hreg |s1 Hpen].
        * inversion Hn'_kmp as [s0' Hreg' |s1' Hpen'].
          --  (* FIXME: cleanup this part *)
              assert (originates #k (strand n, 0)) as Horig.
              {
                unfold originates. repeat split.
                - unfold is_positive, term. simpl. rewrite <- Htr. now simpl.
                - unfold occurs, uns_term, term. simpl. rewrite <- Htr. simpl. intuition.
                - intros n0 Hintra. specialize (intrastrand_index_lt Hintra) as Hlt. simpl in Hlt. lia.
              }
              assert (originates #k (strand n', 0)) as Horig'.
              {
                unfold originates. repeat split.
                - unfold is_positive, term. simpl. rewrite Htrn'. now simpl.
                - unfold occurs, uns_term, term. simpl. rewrite Htrn'. simpl. intuition.
                - intros n0 Hintra. specialize (intrastrand_index_lt Hintra) as Hlt. simpl in Hlt. lia.
              }
              assert (strand n = strand n') as Heqnn'.
              {
                inversion Hreg as [kr mkr KTr [_ [_ [n'' [Horign'' Heq]]]]|?|?|?|?];
                subst; try (now rewrite <-H2 in Htr).

                inversion Htr. inversion Htrn'; subst.
                rewrite H1.
                apply (f_equal tr) in H1; simpl in H1; rewrite <-H0 in H1; inversion H1; subst.
                specialize (Heq (strand n, 0) Horig) as Heqn; specialize (Heq (strand n', 0) Horig') as Heqn'.
                rewrite Heqn in Heqn'. now inversion Heqn'.
              }
              rewrite Heqnn' in Htr; rewrite Htrn' in Htr; now inversion Htr.
          -- inversion Hpen' as [t0 i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k' i Hpenkey Htrace|k' h i Htrace|k' h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace; now rewrite <- Htrace in Htrn'.
        * inversion Hpen as [t0 i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k' i Hpenkey Htrace|k' h i Htrace|k' h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace; now rewrite <- Htrace in Htr.
    - intros Hnk.
      destruct (IHnl C_is_KMP') as [_ IHnlnd]. specialize (IHnlnd Hnk). simpl.
      destruct (tr (strand n')) as [|s0 sl] eqn:Htrn'; try easy.
      destruct s0 as [a|a]; try easy.
      destruct a; try easy.
      destruct a; try easy.
      destruct a1 eqn:Ha1; destruct a2; try easy.
      destruct sl; try easy.
      destruct (K_eq_dec k k1) as [? | ?]; destruct (K_d_dec k1) as [Hk1 | ?]; destruct (K_d_dec k) as [Hk | ?]; destruct (K_m_dec k0) as [Hk0 | ?]; try inversion e as [e']; try rewrite <- e' in *; try easy.
  Qed.

  (* This lemma and the following corollary are useful if we want to prove
     security with terms supporting asymmetric ciphers *)
  Lemma initial_type_symm_K_d :
    forall k, (K_d k /\ k = k ⁻¹) \/ (~K_d k /\ initial_type # k = initial_type # k ⁻¹).
    Proof.
      intros k.
      destruct (K_d_dec k).
      - left. destruct k; easy.
      - right.
        assert (~ K_d k ⁻¹) by ( unfold not, inv; intros; destruct k; try easy ).
        specialize (initial_type_char # k ⁻¹) as Hchar; simpl in Hchar.
        st_implication Hchar. clear Hand. st_implication Hand0.
        specialize (initial_type_char # k) as Hchar; simpl in Hchar;
        st_implication Hchar; clear Hand. st_implication Hand1.
        now rewrite <-Hand0 in Hand1.
    Qed.
  Corollary initial_type_symm :
    forall k, initial_type # k = initial_type # k ⁻¹.
  Proof.
    intros. specialize (initial_type_symm_K_d k) as [[_ Hd]|[_ Hnd]]; try easy.
    now rewrite <-Hd.
  Qed.

  Lemma create_implies_initial_type :
      forall k (KT : KEY_T) mk m,
        K_m mk -> K_d k -> is_node_of m C ->
          [⊕ ⟨ #k ⋅ $KT ⟩_(mk)] = tr (strand m) ->
            initial_type #k = (KDn KT).
  Proof.
    intros k KT mk m Hmk Hk Hisnode Htr.
    specialize (initial_type_char #k) as Hit.
    simpl in Hit; destruct Hit as [Hd Hnd].
    apply (Hd Hk m KT mk Hmk Hisnode Htr).
  Qed.

  (* Assume now to have a clousure ϕ and a reachable relation ℜ, satisfying is_closure *)
  Variable ϕ : cl_policy__t.
  Variable ℜ : reachable__t.
  Definition ϕ_ℜ_closes_π := is_closure π (ϕ, ℜ).

  Definition wf_cipher_master k KT := (ϕ, ℜ) ⊢ KDn KT ∈ initial_type k.
  Lemma wf_cipher_master_dec : forall k KT, {(ϕ, ℜ) ⊢ KDn KT ∈ initial_type k } + {~(ϕ, ℜ) ⊢ KDn KT ∈ initial_type k}.
  Proof.
    intros k KT;
    apply set_In_dec; repeat decide equality; repeat apply U_eq_dec.
  Qed.

  Definition P_wcnmb k k' el :=
    snd (fst el) = Enc /\ set_In (snd el, initial_type k) ℜ /\ set_In (fst (fst el), initial_type k') ℜ.

  Lemma P_wcnmb_dec : forall k k' x, {P_wcnmb k k' x} + {~ P_wcnmb k k' x}.
  Proof.
    intros k k' x.
    unfold P_wcnmb.
    destruct x as [[KT' e] KT]; simpl in *.
    destruct e; try now right.
    destruct (set_In_dec reachable__t_el_eq_dec (KT, initial_type k) ℜ); try tauto.
    destruct (set_In_dec reachable__t_el_eq_dec (KT', initial_type k') ℜ); try tauto.
  Qed.

  Definition wf_cipher_nonmaster k k' :=
    exists KT KT',
          (ϕ, ℜ) ⊢ KT' =[Enc]=> KT /\
          ((ϕ, ℜ) ⊢ KT ∈ initial_type k) /\
          ((ϕ, ℜ) ⊢ KT' ∈ initial_type k').

  Lemma wcnmb_iff_wcnm : forall k k', Exists (P_wcnmb k k') ϕ <-> wf_cipher_nonmaster k k'.
  Proof.
    intros k k'.
    unfold wf_cipher_nonmaster.
    rewrite Exists_exists.
    split.
    - intro Hb. destruct Hb as [[[KT' e] KT] [Hin [Hit Hit']]].
      simpl in *. subst. exists KT, KT'. intuition.
    - intro H. destruct H as [KT [KT' [Henc [Hit Hit']]]].
      exists (KT', Enc, KT). unfold P_wcnmb. intuition.
  Qed.

  Lemma wf_cipher_nonmaster_dec : forall k k', {wf_cipher_nonmaster k k'} + {~ wf_cipher_nonmaster k k'}.
  Proof.
    intros k k'.
    specialize (Exists_dec (P_wcnmb k k') ϕ (P_wcnmb_dec k k')) as Hdec.
    destruct Hdec as [HE|HnE].
    1: left. 2: right.
    all: now rewrite <-wcnmb_iff_wcnm.
  Qed.

  Definition isMK k := match k with | #k' => K_m k' | _ => False end.

  Definition isDK k := match k with | #k' => K_d k' | _ => False end.

  Lemma isDK_dec : forall k, { isDK k } + { ~isDK k }.
  Proof.
    intros k.
    unfold isDK.
    destruct k; try tauto.
    destruct (K_d_dec k); try tauto.
  Qed.

  (* Recall that this should imply that if a term t is accepted by the predicate, then k <> t with K_d k *)
  Fixpoint protected (t : 𝔸) : Prop :=
    match t with
    | ⟨ k ⋅ KT ⟩_(mk) =>
      match KT with
        | $KT' =>
            (isMK #mk -> wf_cipher_master k KT') /\
            (~isMK #mk -> wf_cipher_nonmaster k #mk /\ wf_cipher_nonmaster KT #mk) /\
            (~isDK k -> protected k /\ protected KT)
        | _ => protected k /\ protected KT
      end
    | ⟨ k ⟩_(k') =>
        (wf_cipher_nonmaster k #k') /\ (~isDK k -> protected k)
    | g ⋅ h => protected g /\ protected h
    | _ => (ϕ, ℜ) ⊢ D ∈ (initial_type t)
  end.

  Lemma protected_dec :
    forall t, {protected t} + { ~protected t}.
  Proof.
    intros t.
    induction t as [ | t | k | k t IHt | t1 IHt1 t2 IHt2 ].
    - simpl; destruct (set_In_dec reachable__t_el_eq_dec (D, initial_type τ) ℜ); try tauto.
    - simpl; destruct (set_In_dec reachable__t_el_eq_dec (D, initial_type $t) ℜ); try tauto.
    - simpl; destruct (set_In_dec reachable__t_el_eq_dec (D, initial_type #k) ℜ); try tauto.
    - simpl. destruct t as [ | t | k' | k' t | t1 t2 ].
      + destruct (wf_cipher_nonmaster_dec τ #k); destruct (set_In_dec reachable__t_el_eq_dec (D, initial_type τ) ℜ); try tauto.
      + destruct (wf_cipher_nonmaster_dec $t #k); destruct (set_In_dec reachable__t_el_eq_dec (D, initial_type $t) ℜ); try tauto.
      + destruct (wf_cipher_nonmaster_dec #k' #k); destruct (set_In_dec reachable__t_el_eq_dec (D, initial_type #k') ℜ); destruct (K_d_dec k'); try tauto.
      + destruct (wf_cipher_nonmaster_dec (⟨ t ⟩_ k') #k); destruct (isDK_dec (⟨ t ⟩_ k')); destruct IHt; try tauto.
      + simpl in IHt.
        destruct t2 as [ | t2 | k2 | k2 t2 | t21 t22 ]; try tauto.
        destruct IHt as [[Hp1 Hin] | Hnp ].
        * destruct (K_m_dec k);
          destruct (wf_cipher_master_dec t1 t2);
          destruct (wf_cipher_nonmaster_dec t1 #k);
          destruct (wf_cipher_nonmaster_dec $t2 #k);
          destruct (isDK_dec t1); try tauto.
        * destruct (K_m_dec k);
          destruct (wf_cipher_master_dec t1 t2);
          destruct (wf_cipher_nonmaster_dec t1 #k);
          destruct (wf_cipher_nonmaster_dec $t2 #k);
          destruct (isDK_dec t1); try tauto.
    - simpl. destruct (IHt1); destruct (IHt2); try tauto.
  Qed.

  Definition KMP_p (t : 𝔸) : Prop := ~protected t.

  (* We prove decidability of KMP_p based on protected decidability *)
  Lemma KMP_p_dec :
      forall t, { KMP_p t } + { ~KMP_p t}.
  Proof.
    intros t.
    specialize (protected_dec t) as Hpd.
    intuition.
  Qed.

  Definition N_KMP := N KMP_p C KMP_p_dec.
  Definition N_iff_inC_p_KMP := N_iff_inC_p KMP_p C KMP_p_dec.
  Definition minimal_N_KMP_then_mpt := minimal_N_then_mpt KMP_p C_is_bundle KMP_p_dec.

  Lemma no_minimal_is_regular :
    ϕ_ℜ_closes_π ->
      forall m,
        set_In m N_KMP -> is_minimal (bundle_le C) m N_KMP -> ~KMP_strand π (strand m).
  Proof.
    intros ϕ_ℜ_closes_π m Hin Hmin Hreg.
    specialize initial_type_char as Hit.
    assert (Hin':=Hin); apply N_iff_inC_p_KMP in Hin' as [Hinm HpKMP].

    specialize ϕ_ℜ_closes_π as Hub_clos. destruct Hub_clos as [Hcl [Hcl_refl [Hcl_D [Hcl_ed [Hcl_eh Hcl_et]]]]].

    inversion Hreg as [k mk KT [Hk Hmk] i Htr | k mk KT m' [Hk Hmk] i Htr | k mk KT m' [Hk Hmk] i Htr| k1 k2 mk KT1 KT2 [Hk Hmk] i Htr | k1 k2 mk KT1 KT2 [Hk Hmk] i Htr]; apply (f_equal tr) in Htr; simpl in Htr.
    all: specialize (minimal_N_KMP_then_mpt Htr Hin Hmin) as Hmpti; unfold pred in *; unfold KMP_p in Hmpti; simpl in Hmpti.
    all: simplify_prop in Hmpti.
    - (* Create case *)
      unfold wf_cipher_master, isDK, isMK in *.
      specialize (create_implies_initial_type (k:=k) (KT:=KT) (mk:=mk) m) as Hci. st_implication Hci.
      rewrite Hci in Hand. st_implication Hand.
    - (* Encrypt case *)
      (* simplify_prop in Hmpti. *)
      unfold wf_cipher_master, wf_cipher_nonmaster in *.
      st_implication Hand0.
      apply Hand3. split; try easy. exists D, KT. repeat split; try easy. now apply Hcl.
    - (* Wrap case *)
      (* simplify_prop in Hmpti. *)
      unfold wf_cipher_master, wf_cipher_nonmaster in *.
      st_implication Hand1. st_implication Hand0.
      apply Hand5. split; try easy. exists KT1, KT2. repeat split; try easy. now apply Hcl.
    - (* Unwrap case *)
      (* simplify_prop in Hmpti. *)
      apply Hand4.
      unfold wf_cipher_master, wf_cipher_nonmaster in *.
      st_implication Hand0.
      split; try easy; intros _.
      destruct Hand1 as [KT1' [KT2' [Henc [Hk1 Hk2]]]].
      (* We now apply the rules: 5 twice (eh), 6 (et), 4 (ed) *)
      specialize (Hcl_eh KT2' KT1' (initial_type #k2)) as Hit12; st_implication Hit12.
      specialize (Hcl_eh (initial_type #k2) KT1' KT2) as Hit12'; st_implication Hit12'.
      specialize (Hcl_et KT1' KT2 (initial_type #k1)) as Het; st_implication Het.
      specialize (Hcl KT2 Dec KT1) as Hcl'; st_implication Hcl'.
      specialize (Hcl_ed KT2 (initial_type # k1) KT1) as Hreach; st_implication Hreach.
  Qed.

  Lemma KMP_never_originates_mk :
    forall k, K_m k -> never_originates_regular K__P_md k C.
  Proof.
    intros k0 Hkm n Hnodeof Horig.
    unfold not.
    unfold isMK in *.
    specialize (C_is_KMP n Hnodeof) as Hn_kmp.
    inversion Hn_kmp as [s Hreg|s Hpen]; try easy.
    (* unfold KMP_strand in Hreg; *)
    inversion Hreg as [k mk KT [Hk Hmk] i Htr | k mk KT m' [Hk Hmk] i Htr | k mk KT m' [Hk Hmk] i Htr| k1 k2 mk KT1 KT2 [Hk Hmk] i Htr | k1 k2 mk KT1 KT2 [Hk Hmk] i Htr]; apply (f_equal tr) in Htr; simpl in Htr;
    apply (originates_then_mpt Htr) in Horig; unfold mpt in Horig; simpl in Horig;
    simplify_prop in Horig.
    specialize (K_d_then_not_K_m Hk) as Hkdnkm; try easy.
  Qed.

  Lemma no_minimal_is_penetrator :
    ϕ_ℜ_closes_π ->
      forall m,
        set_In m N_KMP -> is_minimal (bundle_le C) m N_KMP -> ~penetrator_node K__P_md m.
  Proof.
    intros ϕ_ℜ_closes_π m Hin Hmin Hpen.
    (* specialize trace_of_s as Hstr.
    specialize C_is_bundle as Hbundle. *)
    specialize initial_type_char as Hit.
    assert (Hin':=Hin); apply N_iff_inC_p_KMP in Hin' as [Hinm HpKMP].
    specialize ϕ_ℜ_closes_π as Hub_clos. destruct Hub_clos as [Hcl Hub].

    (* unfold penetrator_node, penetrator_strand in Hpen.
    assert (Hpentrace:=Hpen); apply is_penetrator in Hpentrace.
    inversion Hpentrace as [t Htrace|g Htrace|g Htrace|g h Htrace|g h Htrace|k Hpenkey Htrace|k h Htrace|k h Htrace]. *)
    inversion Hpen as [t i Htrace|g i Htrace|g i Htrace|g h i Htrace|g h i Htrace|k i Hpenkey Htrace|k h i Htrace|k h i Htrace]; apply (f_equal tr) in Htrace; simpl in Htrace.

    all: specialize (minimal_N_KMP_then_mpt Htrace Hin Hmin) as Hmpti; unfold pred in *; unfold KMP_p in Hmpti; simpl in Hmpti.
    all: simplify_prop in Hmpti. (* Automatically solves: flush, tee, concatenation, separation *)
    - (* Text case *)
      apply Hand. specialize (Hit $t); simpl in Hit. now rewrite Hit in *.
    - (* Penetrator key case *)
      apply Hand. specialize (Hit #k); simpl in Hit; destruct Hit as [_ Hnkd].
      apply (K__P_md_then_not_K_d) in Hpenkey.
      st_implication Hnkd; now rewrite Hnkd.
    - (* Enc case *)
      destruct h as [|?|?|?|?].
      all: try (unfold wf_cipher_master, wf_cipher_nonmaster in *; simpl in *; apply Hand0; split; try easy; exists D, D; repeat split; try easy).
      + now specialize (Hit (⟨ h ⟩_ k0)); simpl in Hit; rewrite Hit.
      + unfold wf_cipher_master, wf_cipher_nonmaster in *; simpl in *.
        destruct h2 as [|KT'|?|?|?]; try easy.
        apply Hand0; clear Hand0; repeat split; try easy.
        * intros Hkm.
          specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m, 0) m) as Hisnode; st_implication Hisnode.
          unfold K__P_md in Hkm.
          apply K_m_then_not_K__P_md in Hkm as Hknkp.
          specialize (penetrator_bound C_is_bundle Hknkp (KMP_never_originates_mk Hkm) Hisnode) as Hnsub. st_implication Hnsub.
          (* simplify_term_in Hnsub. *)
        * intros. exists D, D. repeat split; try easy.
          destruct h1 eqn:Heqh1.
          all: (specialize (Hit h1); rewrite Heqh1 in Hit; simpl in Hit; try rewrite Hit; try easy).
        * intros. exists D, D. repeat split; try easy.
    - (* Dec case *)
      destruct Hub as [Hrefl [[HDdec HDenc] [Hreach [Hh_enc Ht_enc]]]].
      destruct h as [|h|k0|k0 h|h1 h2].
      all: try tauto.
      + destruct Hand1 as [[KT [KT' [Henc [HKT HKT']]]] _].
        specialize (initial_type_symm k) as Hsymm; rewrite <-Hsymm in Hand.
        (* unfold inv in Hand; simpl in Hand. *)
        specialize (Hh_enc KT' KT (initial_type #k)) as HkeKT; st_implication HkeKT.
        specialize (Ht_enc KT (initial_type #k) (initial_type #k0)) as Hkek0; st_implication Hkek0.
        specialize (Hh_enc (initial_type #k) (initial_type #k0) D) as HDek0; st_implication HDek0.
        specialize (Hreach D (initial_type #k0) D); st_implication Hreach.
      + destruct h1 as [|?|?|k0 a|a1 a2] eqn:Hh1; destruct h2 eqn:Hh2; try (now apply Hand0).
        * (* h1 = τ; h2 = $_ *)
          unfold protected, isDK in *. simpl in *.
          specialize (Hit $t) as Hit0; simpl in Hit0.
          specialize (Hit A_τ) as Hitt; simpl in Hitt. rewrite Hit0, Hitt in *. now apply Hand0.
        * (* h1 = $_; h2 = $_ *)
          unfold protected, isDK in *. simpl in *.
          assert (Hit0:=Hit $t); simpl in Hit0; assert (Hit1:=Hit $t0); simpl in Hit1; rewrite Hit0, Hit1 in *; now apply Hand0.
        * (* h1 = k0;  h2 = $_ *)
          (* apply H0; intros [HKmk_in Hp5]. destruct (K_m_dec k). *)
          destruct (K_m_dec k) as [Hkm | Hnkm].
          -- specialize (index_lt_strand_implies_is_node_of C_is_bundle (strand m, 0) m) as Hisnode; st_implication Hisnode.
             specialize (K_m_then_not_K__P_md Hkm) as Hknkp.
             specialize (penetrator_bound C_is_bundle Hknkp (KMP_never_originates_mk Hkm) Hisnode) as Hnsub. st_implication Hnsub.
             simplify_term_in Hnsub. inversion Hkm. now rewrite <-H in Hnsub.
          -- simplify_prop in Hand1.
             st_implication Hand1.
             unfold wf_cipher_nonmaster in Hand4, Hand6.
             destruct Hand4 as [kKT [kKT' [Hkenc [HkKT HkKT']]]].
             destruct Hand6 as [tKT [tKT' [Htenc [HtKT HtKT']]]].
             specialize (initial_type_symm k) as Hsymm; rewrite <-Hsymm in Hand.

             specialize (Ht_enc D D (initial_type #k)) as HDeitk; st_implication HDeitk;
             specialize (Hh_enc kKT' kKT (initial_type #k)) as HkKT'ekKT; st_implication HkKT'ekKT;
             specialize (Ht_enc kKT (initial_type #k) (initial_type #k0)) as Hikeik0; st_implication Hikeik0;
             specialize (Hh_enc (initial_type #k) (initial_type #k0) D) as HDeik0; st_implication HDeik0;
             specialize (Hreach D (initial_type #k0) D) as HDRk0; st_implication HDRk0;

             specialize (Hh_enc tKT' tKT (initial_type #k)) as HtKT'ekKT; st_implication HtKT'ekKT;
             specialize (Ht_enc tKT (initial_type #k) (initial_type $t)) as Hikeit0; st_implication Hikeit0;
             specialize (Hh_enc (initial_type #k) (initial_type $t) D) as HDeit0; st_implication HDeit0;
             specialize (Hreach D (initial_type $t) D) as HDRt0; st_implication HDRt0;
             simpl in Hand0; tauto.
        * (* h1 = ⟨ a ⟩_ k0); h2 = $_ *)
          specialize (Hit $t); simpl in Hit.
          st_implication Hand1.
          destruct (K_m_dec k) as [Hkm | Hnkm].
          -- apply Hand0; clear Hand0; try easy.
              st_implication Hand2.
              simpl. tauto.
          -- st_implication Hand1. simpl in Hand0. tauto.
        * (* h1 = h1_1 ⋅ h1_2; h2 = $_ *)
          specialize (Hit $t); simpl in Hit.
          st_implication Hand1.
          destruct (K_m_dec k) as [Hkm | Hnkm].
          -- apply Hand0; clear Hand0; try easy.
              st_implication Hand2.
              simpl. tauto.
          -- st_implication Hand1. simpl in Hand0. tauto.
  Qed.

  (* Put everything together: the set N_KMP has no minimal element *)
  Lemma N_KMP_no_minimal :
    ϕ_ℜ_closes_π ->
      forall m, set_In m N_KMP -> ~is_minimal (bundle_le C) m N_KMP.
  Proof.
    intros ϕ_ℜ_closes_π m Hin Hmin.
    specialize (C_is_KMP m) as Hn_kmp.
    assert (Hin':=Hin);
    apply (N_iff_inC_p_KMP) in Hin'.
    st_implication Hn_kmp.
    inversion Hn_kmp as [Hreg|Hpen].
    - now specialize (no_minimal_is_regular ϕ_ℜ_closes_π Hin Hmin) as Hnreg.
    - now specialize (no_minimal_is_penetrator ϕ_ℜ_closes_π Hin Hmin) as Hnpen.
  Qed.

  (* This is Theorem 1 from the paper *)
  Theorem device_key_secrecy:
    ϕ_ℜ_closes_π ->
      forall m, is_node_of m C -> protected (uns_term m).
  Proof.
    intros ϕ_ℜ_closes_π m Hm_in_C.
    destruct (protected_dec (uns_term m)) as [Hprot | Hnprot]; try easy.
    assert (set_In m N_KMP). { apply (N_iff_inC_p_KMP). auto. }
    specialize (N_KMP_no_minimal) as Hnomin.
    assert ({N_KMP = nil} + {N_KMP <> nil}) as N_KMP_empty_dec by (repeat decide equality).
    destruct N_KMP_empty_dec as [Hemp | Hnemp].
    - (* empty *) now rewrite Hemp in H.
    - (* nonempty *)
      specialize (RelMinimal.exists_minimal eq_node__t_dec (bundle_le_dec C) (bundle_le_antisymm C_is_bundle) (bundle_le_trans (C:=C)) Hnemp) as [m' [Hin Hmin]].
      now specialize (Hnomin ϕ_ℜ_closes_π m' Hin).
  Qed.

  (* This is Theorem 2 (Security) from the paper.
    This gives a necessary condition for policies to be secure: a device key k never appears as plaintext if a D is not reachable from k.
  *)
  Corollary secrecy:
    ϕ_ℜ_closes_π ->
      forall k m, is_node_of m C ->
          K_d k ->
            ~ (ϕ, ℜ) ⊢ D ∈ (initial_type #k) ->
              #k <> uns_term m.
  Proof.
    intros ϕ_ℜ_closes_π k m Hm_in_C Hdev Hreach Heq.
    specialize (device_key_secrecy ϕ_ℜ_closes_π m Hm_in_C) as Hsub.
    unfold protected in Hsub.
    destruct (uns_term m); rewrite Heq in Hreach; try easy.
  Qed.

End secrecy_guarantee.
