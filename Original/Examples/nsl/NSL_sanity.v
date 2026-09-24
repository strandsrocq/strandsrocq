(* The NSL honest run, and what the NSL guarantees prove about it. *)
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.
Require Import NSL_protocol.
Require NSL_auth_initiator NSL_auth_responder NSL_auth_responder_simple.
Require NSL_secrecy_initiator NSL_secrecy_initiator_simple.
Require NSL_secrecy_responder NSL_secrecy_responder_simple.

Set Implicit Arguments.

Section NSLSanity.
  (** * Sanity check: an honest run
    We exhibit an honest protocol execution as a sanity check: the protocol executes and satisfies all of the assumptions of the security lemmas.
  *)

  Notation A  := (Text 0).
  Notation B  := (Text 1).
  Notation Na := (Text 2).
  Notation Nb := (Text 3).
  Notation Tname := (fun t => t = Text 0 \/ t = Text 1).

  Notation s_ini := (0, [
      ⊕ ⟨ $Na ⋅ $A ⟩_(PK B);
      ⊖ ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A);
      ⊕ ⟨ $Nb ⟩_(PK B) ]).
  Notation s_res := (1, [
      ⊖ ⟨ $Na ⋅ $A ⟩_(PK B);
      ⊕ ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A);
      ⊖ ⟨ $Nb ⟩_(PK B) ]).

  (** One honest session, the three messages exchanged in order.  The lists are reversed because each [IndBundle] constructor conses onto their heads. *)
  Definition C : bundle_type :=
    {|
      nodes := rev [
        (s_ini,0);
        (s_res,0);
        (s_res,1);
        (s_ini,1);
        (s_ini,2);
        (s_res,2)
      ];
      intra := rev [
        ((s_res,0),(s_res,1));
        ((s_ini,0),(s_ini,1));
        ((s_ini,1),(s_ini,2));
        ((s_res,1),(s_res,2))
        ];
      inter := rev [
        ((s_ini,0),(s_res,0));   (* A -> B : ⟨ $Na ⋅ $A ⟩_(PK B)       *)
        ((s_res,1),(s_ini,1));   (* B -> A : ⟨ $Na ⋅ $Nb ⋅ $B ⟩_(PK A) *)
        ((s_ini,2),(s_res,2))    (* A -> B : ⟨ $Nb ⟩_(PK B)            *)
        ]
    |}.

  (** The roles carry a premise: [Tname] must hold of the two names and not of the nonces.  This is where the choice of [Tname] is validated, since an empty one would leave the roles uninhabited and the whole guarantee vacuous. *)
  Lemma s_ini_NSL : NSL_initiator_strand Tname A B Na Nb s_ini.
  Proof. solve_role. Qed.

  Lemma s_res_NSL : NSL_responder_strand Tname A B Na Nb s_res.
  Proof. solve_role. Qed.

  Create HintDb sanity.
  #[local] Hint Constructors NSL_StrandSpace penetrator_strand : sanity.
  #[local] Hint Resolve s_ini_NSL s_res_NSL : sanity.

  Lemma C_is_bundle : is_bundle C.
  Proof. ind_bundle. Qed.

  Lemma s_ini_strand_C : is_strand_of s_ini C.
  Proof. solve_is_strand_of. Qed.

  Lemma s_res_strand_C : is_strand_of s_res C.
  Proof. solve_is_strand_of. Qed.

  (** [C] belongs to the NSL strand space for every set of penetrator keys. *)
  Lemma C_is_NSL : forall K__P, bundle_in_SS C (NSL_StrandSpace Tname K__P).
  Proof. intros K__P. solve_bundle_in_SS. Qed.

  (** [$Na] is originated at most once, in fact exactly once at [(s_ini,0)]. *)
  Lemma C_Na_at_most_once : originates_at_most_once_in C $Na.
  Proof. solve_at_most_once_in. Qed.

  (** [$Nb] is originated at most once, in fact exactly once at [(s_res,1)]. *)
  Lemma C_Nb_at_most_once : originates_at_most_once_in C $Nb.
  Proof. solve_at_most_once_in. Qed.

  Lemma Na_neq_Nb : $Na <> $Nb.
  Proof. discriminate. Qed.

  (** Each conclusion below is what we already know by construction, since [C] is one honest session. So, the important part is that the term typechecks, which is possible only if the hypotheses of the guarantee hold at once, i.e., the guarantee is not vacuous. *)

  (** ** Initiator authentication, from [NSL_auth_initiator] *)

  Lemma auth_initiator_sanity :
    (
      exists s0 : Σ,
        NSL_responder_strand Tname A B Na Nb s0 /\
        forall i, i < 2 -> is_node_of (s0,i) C
    )
    /\
    (
      forall s' : Σ,
        is_strand_of s' C ->
        NSL_initiator_strand Tname A B Na Nb s' ->
        s' = s_ini
    ).
  Proof.
    exact (
      NSL_auth_initiator.injective_agreement
        s_ini_NSL
        s_ini_strand_C
        C_is_bundle
        (C_is_NSL _)
        C_Na_at_most_once
      ).
  Qed.

  (** ** Responder authentication, from [NSL_auth_responder] and [NSL_auth_responder_simple] *)

  Lemma auth_responder_sanity :
    (
      exists s0 : Σ,
        NSL_initiator_strand Tname A B Na Nb s0 /\
        is_strand_of s0 C
    )
    /\
    (
      forall s' : Σ,
        is_strand_of s' C ->
        NSL_responder_strand Tname A B Na Nb s' ->
        s' = s_res
    ).
  Proof.
    exact (
      NSL_auth_responder.injective_agreement
        s_res_NSL
        s_res_strand_C
        C_is_bundle
        (C_is_NSL _)
        Na_neq_Nb
        C_Nb_at_most_once
      ).
  Qed.

  Lemma auth_responder_simple_sanity :
    (
      exists s0 : Σ,
        NSL_initiator_strand Tname A B Na Nb s0 /\
        is_strand_of s0 C
    )
    /\
    (
      forall s' : Σ,
        is_strand_of s' C ->
        NSL_responder_strand Tname A B Na Nb s' ->
        s' = s_res
    ).
  Proof.
    exact (
      NSL_auth_responder_simple.injective_agreement
        s_res_NSL
        s_res_strand_C
        C_is_bundle
        (C_is_NSL _)
        Na_neq_Nb
        C_Nb_at_most_once
      ).
  Qed.

  (** ** Initiator secrecy, from [NSL_secrecy_initiator] and [NSL_secrecy_initiator_simple] *)

  Lemma secrecy_initiator_sanity :
    forall m,
      is_node_of m C ->
      $Na <> uns_term m.
  Proof.
    exact (
      NSL_secrecy_initiator.secrecy_of_Na_neq
        s_ini_NSL
        s_ini_strand_C
        C_is_bundle
        (C_is_NSL _)
        C_Na_at_most_once
      ).
  Qed.

  Lemma secrecy_initiator_simple_sanity :
    forall m,
      is_node_of m C ->
      $Na <> uns_term m.
  Proof.
    exact (
      NSL_secrecy_initiator_simple.secrecy_of_Na_neq
        s_ini_NSL
        s_ini_strand_C
        C_is_bundle
        (C_is_NSL _)
        C_Na_at_most_once
      ).
  Qed.

  (** ** Responder secrecy, from [NSL_secrecy_responder] and [NSL_secrecy_responder_simple] *)

  Lemma secrecy_responder_sanity :
    forall m,
      is_node_of m C ->
      $Nb <> uns_term m.
  Proof.
    exact (
      NSL_secrecy_responder.secrecy_of_Nb_neq
        s_res_NSL
        s_res_strand_C
        C_is_bundle
        (C_is_NSL _)
        Na_neq_Nb
        C_Nb_at_most_once
      ).
  Qed.

  Lemma secrecy_responder_simple_sanity :
    forall m,
      is_node_of m C ->
      $Nb <> uns_term m.
  Proof.
    exact (
      NSL_secrecy_responder_simple.secrecy_of_Nb_neq
        s_res_NSL
        s_res_strand_C
        C_is_bundle
        (C_is_NSL _)
        Na_neq_Nb
        C_Nb_at_most_once
      ).
  Qed.

End NSLSanity.

Section NSLResponderAttack.
  (** * Sanity check: a nonce collapse
    We exhibit an attack as a second sanity check: responder secrecy and responder agreement both fail exactly when their common hypothesis [$Na <> $Nb] does.  The penetrator chooses a nonce [N], sends it to [B] as [Na], and [B] picks the same [N] as [Nb], so [Nb] is originated by the penetrator itself.  Freshness still holds, since [originates_at_most_once_in] bounds how many nodes originate [Nb] but not which ones, so an origination by the penetrator satisfies it.  No initiator strand occurs in the bundle, so [B] completes a session with nobody.
  *)

  Notation A  := (Text 0).
  Notation B  := (Text 1).
  Notation N  := (Text 2).
  Notation Tname := (fun t => t = Text 0 \/ t = Text 1).

  Notation s_res  := (1, [
      ⊖ ⟨ $N ⋅ $A ⟩_(PK B);
      ⊕ ⟨ $N ⋅ $N ⋅ $B ⟩_(PK A);
      ⊖ ⟨ $N ⟩_(PK B) ]).
  (* the penetrator mints [N] and takes [PK B] once each, and both nodes feed both encryptions *)
  Notation s_N    := (2, [ ⊕ $N ]).
  Notation s_A    := (3, [ ⊕ $A ]).
  Notation s_cat  := (4, [ ⊖ $N; ⊖ $A; ⊕ $N ⋅ $A ]).
  Notation s_kB   := (5, [ ⊕ #(PK B) ]).
  Notation s_enc1 := (6, [ ⊖ #(PK B); ⊖ $N ⋅ $A; ⊕ ⟨ $N ⋅ $A ⟩_(PK B) ]).
  Notation s_enc2 := (7, [ ⊖ #(PK B); ⊖ $N; ⊕ ⟨ $N ⟩_(PK B) ]).

  Definition C' : bundle_type :=
    {|
      nodes := rev [
        (s_N,0);
        (s_A,0);
        (s_cat,0);  (s_cat,1);  (s_cat,2);
        (s_kB,0);
        (s_enc1,0); (s_enc1,1); (s_enc1,2);
        (s_res,0);  (s_res,1);  (* the second message is sent and nobody receives it *)
        (s_enc2,0); (s_enc2,1); (s_enc2,2);
        (s_res,2)
      ];
      intra := rev [
        ((s_cat,0),(s_cat,1));   ((s_cat,1),(s_cat,2));
        ((s_enc1,0),(s_enc1,1)); ((s_enc1,1),(s_enc1,2));
        ((s_res,0),(s_res,1));
        ((s_enc2,0),(s_enc2,1)); ((s_enc2,1),(s_enc2,2));
        ((s_res,1),(s_res,2))
        ];
      inter := rev [
        ((s_N,0),(s_cat,0));      (* P -> P : $N                  *)
        ((s_A,0),(s_cat,1));      (* P -> P : $A                  *)
        ((s_kB,0),(s_enc1,0));    (* P -> P : #(PK B)             *)
        ((s_cat,2),(s_enc1,1));   (* P -> P : $N ⋅ $A             *)
        ((s_enc1,2),(s_res,0));   (* P -> B : ⟨ $N ⋅ $A ⟩_(PK B)  *)
        ((s_kB,0),(s_enc2,0));    (* P -> P : #(PK B), the same node again *)
        ((s_N,0),(s_enc2,1));     (* P -> P : $N, the same node again *)
        ((s_enc2,2),(s_res,2))    (* P -> B : ⟨ $N ⟩_(PK B)       *)
        ]
    |}.

  (** [B] is a legitimate responder, with the same nonce as [Na] and [Nb]. *)
  Lemma s_res_NSL' : NSL_responder_strand Tname A B N N s_res.
  Proof. solve_role. Qed.

  #[local] Hint Constructors NSL_StrandSpace penetrator_strand : sanity.
  #[local] Hint Resolve s_res_NSL' : sanity.

  Lemma C'_is_bundle : is_bundle C'.
  Proof. ind_bundle. Qed.

  Lemma s_res_strand_C' : is_strand_of s_res C'.
  Proof. solve_is_strand_of. Qed.

  (** Nothing here breaks the rules: every strand of [C'] belongs to the NSL strand space, for every set of penetrator keys that contains the public key of [B]. *)
  Lemma C'_is_NSL : forall K__P, K__P (PK B) -> bundle_in_SS C' (NSL_StrandSpace Tname K__P).
  Proof. intros K__P HK. solve_bundle_in_SS. Qed.

  (** The two sets of penetrator keys of the guarantees contain it. *)
  Lemma PK_B_pen_secrecy : NSL_secrecy_responder.K__P_AB A B (PK B).
  Proof. split; discriminate. Qed.

  Lemma PK_B_pen_auth : NSL_auth_responder.K__P_A A (PK B).
  Proof. discriminate. Qed.

  (** Freshness holds: [$N] originates once, at [(s_N,0)], a penetrator node. *)
  Lemma C'_N_at_most_once : originates_at_most_once_in C' $N.
  Proof. solve_at_most_once_in. Qed.

  (** [Nb] is on the network in the clear, at the node where the penetrator mints it. *)
  Lemma Nb_in_the_clear :
    is_node_of (s_N, 0) C' /\ uns_term (s_N, 0) = $N.
  Proof. split; [ indb_in | reflexivity ]. Qed.

  (** Secrecy fails: [$Nb] is the term of a node of [C'].  Every other hypothesis of [secrecy_of_Nb_neq] holds above, so the guarantee does not apply only because [Na] and [Nb] collapse into [N]. *)
  Lemma Nb_not_secret :
    ~ (forall m, is_node_of m C' -> $N <> uns_term m).
  Proof.
    intro H. destruct Nb_in_the_clear as [Hn Ht].
    exact (H _ Hn (eq_sym Ht)).
  Qed.

  (** Agreement fails too: no initiator strand of [C'] has [A] talking to [B].  Again every other hypothesis of [NSL_auth_responder.injective_agreement] holds above. *)
  Lemma no_initiator_for_A :
    ~ (exists s0, NSL_initiator_strand Tname A B N N s0 /\ is_strand_of s0 C').
  Proof. solve_no_strand. Qed.

End NSLResponderAttack.
