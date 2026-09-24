From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
From Stdlib Require Import ListSet.

From strandsrocq.Original.Instances Require Import DefaultInstances.
From strandsrocq.Original.Instances Require Import Penetrator.
Require Import KMP_policies.
Require Import KMP_protocol.
Require Import KMP_policy_examples.

Set Implicit Arguments.

(** Each strand is a legitimate role.  The premises are the typing side of the
    policy: which type may encrypt or decrypt what, and that a created key has a
    type the policy describes. *)
Ltac kmp_role :=
  repeat split; simpl;
  repeat match goal with
         | |- K_d _   => constructor
         | |- K_m _   => constructor
         | |- _ \/ _  => first [ now left | right ]
         | |- _       => reflexivity
         end.

(* The keys the runs use.  [katt] is one the penetrator knows: [K__P_md] holds of
   it, so its initial type is [D], and that is how a datum is modelled here. *)
Notation k0   := (SymK' 0).   (* a data key,            type K2 *)
Notation k1   := (SymK' 1).   (* a key encryption key,  type K1 *)
Notation k2   := (SymK' 2).   (* a device key at the imported type *)
Notation mk   := (SymK 0).    (* the master key *)
Notation katt := (SymKA 0).   (* a key the penetrator already knows *)

Section KMPSanity.
  (** * The honest run
    An honest run under the two level policy: two keys are created, a datum is
    encrypted and decrypted with the data key, and the data key is wrapped and
    unwrapped with the key encryption key.
  *)


  Notation Fresh := (fun a => a = #k0 \/ a = #k1).

  Notation s_c0 := (0, [ ⊕ ⟨ #k0 ⋅ $K2 ⟩_mk ]).
  Notation s_c1 := (1, [ ⊕ ⟨ #k1 ⋅ $K1 ⟩_mk ]).
  Notation s_e  := (2, [ ⊖ #katt; ⊖ ⟨ #k0 ⋅ $K2 ⟩_mk; ⊕ ⟨ #katt ⟩_k0 ]).
  Notation s_d  := (3, [ ⊖ ⟨ #katt ⟩_k0; ⊖ ⟨ #k0 ⋅ $K2 ⟩_mk; ⊕ #katt ]).
  Notation s_w  := (4, [ ⊖ ⟨ #k0 ⋅ $K2 ⟩_mk; ⊖ ⟨ #k1 ⋅ $K1 ⟩_mk; ⊕ ⟨ #k0 ⟩_k1 ]).
  Notation s_u  := (5, [ ⊖ ⟨ #k0 ⟩_k1; ⊖ ⟨ #k1 ⋅ $K1 ⟩_mk; ⊕ ⟨ #k0 ⋅ $K2 ⟩_mk ]).
  Notation s_p  := (6, [ ⊕ #katt ]).   (* the datum comes from the environment *)

  Definition C : bundle_type :=
    {|
      nodes := rev [
        (s_c0,0); (s_c1,0); (s_p,0);
        (s_e,0); (s_e,1); (s_e,2);
        (s_d,0); (s_d,1); (s_d,2);
        (s_w,0); (s_w,1); (s_w,2);
        (s_u,0); (s_u,1); (s_u,2)
      ];
      intra := rev [
        ((s_e,0),(s_e,1)); ((s_e,1),(s_e,2));
        ((s_d,0),(s_d,1)); ((s_d,1),(s_d,2));
        ((s_w,0),(s_w,1)); ((s_w,1),(s_w,2));
        ((s_u,0),(s_u,1)); ((s_u,1),(s_u,2))
      ];
      inter := rev [
        ((s_p,0), (s_e,0));    (* the datum                  *)
        ((s_c0,0),(s_e,1));    (* the data key, to encrypt   *)
        ((s_e,2), (s_d,0));    (* the ciphertext             *)
        ((s_c0,0),(s_d,1));    (* the data key, to decrypt   *)
        ((s_c0,0),(s_w,0));    (* the data key, to be wrapped *)
        ((s_c1,0),(s_w,1));    (* the key encryption key     *)
        ((s_w,2), (s_u,0));    (* the wrapped key            *)
        ((s_c1,0),(s_u,1))     (* the key encryption key     *)
      ]
    |}.

  Lemma s_c0_KMP : KMP_strand hierarchy_policy Fresh s_c0.
  Proof. apply KMP_C; kmp_role. Qed.
  Lemma s_c1_KMP : KMP_strand hierarchy_policy Fresh s_c1.
  Proof. apply KMP_C; kmp_role. Qed.
  Lemma s_e_KMP : KMP_strand hierarchy_policy Fresh s_e.
  Proof. apply KMP_E; kmp_role. Qed.
  Lemma s_d_KMP : KMP_strand hierarchy_policy Fresh s_d.
  Proof. apply KMP_D; kmp_role. Qed.
  Lemma s_w_KMP : KMP_strand hierarchy_policy Fresh s_w.
  Proof. apply KMP_W; kmp_role. Qed.
  Lemma s_u_KMP : KMP_strand hierarchy_policy Fresh s_u.
  Proof. apply KMP_U; kmp_role. Qed.
  Lemma s_p_pen : penetrator_strand K__P_md s_p.
  Proof. apply PT_K. exact I. Qed.

  Create HintDb sanity.
  #[local] Hint Constructors KMP_StrandSpace : sanity.
  #[local] Hint Resolve s_c0_KMP s_c1_KMP s_e_KMP s_d_KMP s_w_KMP s_u_KMP s_p_pen : sanity.

  Lemma C_is_bundle : is_bundle C.
  Proof. ind_bundle. Qed.

  Lemma C_is_KMP : bundle_in_SS C (KMP_StrandSpace hierarchy_policy Fresh).
  Proof. solve_bundle_in_SS. Qed.

  (** The bridge the fix introduced: both keys the roles declare fresh really do
      originate at most once here, each at its own creation event. *)
  Lemma C_fresh_sound : forall t, Fresh t -> originates_at_most_once_in C t.
  Proof. intros t [Ht|Ht]; rewrite Ht; solve_at_most_once_in. Qed.

End KMPSanity.

Section KMPTypeConfusion.
  (** * The type confusion run
    The run the leaky policy allows.  Granting [K1] keys the right to unwrap at
    type [K1] lets a key be wrapped at one level and imported at the other, so the
    same key ends up holding two handles with two different types. This allows for
    a classic wrap-the-decrypt attack using such a key.
  *)


  Notation Fresh := (fun a => a = #k0 \/ a = #k1).

  Notation s_c0 := (0, [ ⊕ ⟨ #k0 ⋅ $K2 ⟩_mk ]).
  Notation s_c1 := (1, [ ⊕ ⟨ #k1 ⋅ $K1 ⟩_mk ]).
  Notation s_w  := (2, [ ⊖ ⟨ #k0 ⋅ $K2 ⟩_mk; ⊖ ⟨ #k1 ⋅ $K1 ⟩_mk; ⊕ ⟨ #k0 ⟩_k1 ]).
  Notation s_u  := (3, [ ⊖ ⟨ #k0 ⟩_k1; ⊖ ⟨ #k1 ⋅ $K1 ⟩_mk; ⊕ ⟨ #k0 ⋅ $K1 ⟩_mk ]).
  Notation s_w2 := (4, [ ⊖ ⟨ #k0 ⋅ $K2 ⟩_mk; ⊖ ⟨ #k0 ⋅ $K1 ⟩_mk; ⊕ ⟨ #k0 ⟩_k0 ]).  (* Wrap    *)
  Notation s_d2 := (5, [ ⊖ ⟨ #k0 ⟩_k0; ⊖ ⟨ #k0 ⋅ $K2 ⟩_mk; ⊕ #k0 ]).               (* Decrypt *)

  Definition C' : bundle_type :=
    {|
      nodes := rev [
        (s_c0,0); (s_c1,0);
        (s_w,0); (s_w,1); (s_w,2);
        (s_u,0); (s_u,1); (s_u,2);
        (s_w2,0); (s_w2,1); (s_w2,2);
        (s_d2,0); (s_d2,1); (s_d2,2)
      ];
      intra := rev [
        ((s_w,0),(s_w,1));   ((s_w,1),(s_w,2));
        ((s_u,0),(s_u,1));   ((s_u,1),(s_u,2));
        ((s_w2,0),(s_w2,1)); ((s_w2,1),(s_w2,2));
        ((s_d2,0),(s_d2,1)); ((s_d2,1),(s_d2,2))
      ];
      inter := rev [
        ((s_c0,0),(s_w,0));    (* the data key, to be wrapped         *)
        ((s_c1,0),(s_w,1));    (* the key encryption key, wrapping    *)
        ((s_w,2), (s_u,0));    (* the wrapped key, fed back in        *)
        ((s_c1,0),(s_u,1));    (* the key encryption key, unwrapping  *)
        ((s_c0,0),(s_w2,0));   (* [k0] again, now as the key to wrap   *)
        ((s_u,2),  (s_w2,1));  (* and as the key that wraps it         *)
        ((s_w2,2), (s_d2,0));  (* the self wrap, decrypted as data     *)
        ((s_c0,0),(s_d2,1))    (* under [k0]'s own data key handle     *)
      ]
    |}.

  Lemma s_c0_leaky : KMP_strand leaky_policy Fresh s_c0.
  Proof. apply KMP_C; kmp_role. Qed.
  Lemma s_c1_leaky : KMP_strand leaky_policy Fresh s_c1.
  Proof. apply KMP_C; kmp_role. Qed.
  Lemma s_w_leaky : KMP_strand leaky_policy Fresh s_w.
  Proof. apply KMP_W; kmp_role. Qed.

  (** The only strand the original policy would refuse: it imports [k0] at [K1],
      and it typechecks exactly because of the entry we added. *)
  Lemma s_u_leaky : KMP_strand leaky_policy Fresh s_u.
  Proof. apply KMP_U; kmp_role. Qed.

  (** The forbidden configuration, reached legitimately: [k0] holds both handles at
      once, so the device can be asked to wrap [k0] under [k0] itself. *)
  Lemma s_w2_leaky : KMP_strand leaky_policy Fresh s_w2.
  Proof. apply KMP_W; kmp_role. Qed.

  (** And the last step: [k0] still has its original data key handle, and the policy
      lets a data key decrypt.  The device hands the key back in the clear. *)
  Lemma s_d2_leaky : KMP_strand leaky_policy Fresh s_d2.
  Proof. apply KMP_D; kmp_role. Qed.

  #[local] Hint Constructors KMP_StrandSpace : sanity.
  #[local] Hint Resolve s_c0_leaky s_c1_leaky s_w_leaky s_u_leaky s_w2_leaky s_d2_leaky : sanity.

  Lemma C'_is_bundle : is_bundle C'.
  Proof. ind_bundle. Qed.

  Lemma C'_is_KMP : bundle_in_SS C' (KMP_StrandSpace leaky_policy Fresh).
  Proof. solve_bundle_in_SS. Qed.

  Lemma C'_fresh_sound : forall t, Fresh t -> originates_at_most_once_in C' t.
  Proof. intros t [Ht|Ht]; rewrite Ht; solve_at_most_once_in. Qed.

  Lemma k0_also_imported_as_a_KEK :
    is_node_of (s_u, 2) C' /\ uns_term (s_u, 2) = ⟨ #k0 ⋅ $K1 ⟩_mk.
  Proof. split; [ indb_in | reflexivity ]. Qed.

  (** The forbidden configuration reached: the device is asked to wrap [k0] under
      [k0] itself, which only the second handle makes possible. *)
  Lemma k0_is_wrapped_under_itself :
    is_node_of (s_w2, 2) C' /\ uns_term (s_w2, 2) = ⟨ #k0 ⟩_k0.
  Proof. split; [ indb_in | reflexivity ]. Qed.

  (** The attack, completed: [k0] was created as a device key and never wrapped under
      anything the penetrator knows, yet here it is on the network as itself. *)
  Lemma k0_appears_in_the_clear :
    is_node_of (s_d2, 2) C' /\ uns_term (s_d2, 2) = #k0.
  Proof. split; [ indb_in | reflexivity ]. Qed.

End KMPTypeConfusion.

(* Encrypt-then-unwrap: the penetrator has the device encrypt a key it already
   knows, then has that ciphertext imported as a key, so it ends up holding a valid
   device handle for a key of its own choosing.

   Importing an attacker key becomes a secrecy flaw exactly when that key may then
   be used to wrap other keys: the penetrator would collect the wraps and open them
   with a key it knows.  The secure templates policy prevents that step, since the
   type it stamps on an imported key may encrypt data and nothing of key type. *)
Section KMPKeyInjection.
  (** * The key injection run *)

  Notation Fresh := (fun a => a = #k2).

  Notation s_p := (0, [ ⊕ #katt ]).
  Notation s_c := (1, [ ⊕ ⟨ #k2 ⋅ $K2 ⟩_mk ]).
  Notation s_e := (2, [ ⊖ #katt; ⊖ ⟨ #k2 ⋅ $K2 ⟩_mk; ⊕ ⟨ #katt ⟩_k2 ]).
  Notation s_u := (3, [ ⊖ ⟨ #katt ⟩_k2; ⊖ ⟨ #k2 ⋅ $K2 ⟩_mk; ⊕ ⟨ #katt ⋅ $K2 ⟩_mk ]).

  Definition C'' : bundle_type :=
    {|
      nodes := rev [
        (s_p,0); (s_c,0);
        (s_e,0); (s_e,1); (s_e,2);
        (s_u,0); (s_u,1); (s_u,2)
      ];
      intra := rev [
        ((s_e,0),(s_e,1)); ((s_e,1),(s_e,2));
        ((s_u,0),(s_u,1)); ((s_u,1),(s_u,2))
      ];
      inter := rev [
        ((s_p,0),(s_e,0));   (* the key the penetrator chose            *)
        ((s_c,0),(s_e,1));   (* a device handle, to encrypt with        *)
        ((s_e,2),(s_u,0));   (* the ciphertext, fed back as if a wrap   *)
        ((s_c,0),(s_u,1))    (* the same handle, now to unwrap with     *)
      ]
    |}.

  (** Every step is a legitimate role under the policy the paper calls secure. *)
  Lemma etu_penetrator : penetrator_strand K__P_md s_p.
  Proof. apply PT_K. exact I. Qed.
  Lemma etu_create : KMP_strand secure_templates Fresh s_c.
  Proof. apply KMP_C; kmp_role. Qed.
  Lemma etu_encrypt : KMP_strand secure_templates Fresh s_e.
  Proof. apply KMP_E; kmp_role. Qed.
  Lemma etu_unwrap : KMP_strand secure_templates Fresh s_u.
  Proof. apply KMP_U; kmp_role. Qed.

  #[local] Hint Constructors KMP_StrandSpace : sanity.
  #[local] Hint Resolve etu_penetrator etu_create etu_encrypt etu_unwrap : sanity.

  Lemma C''_is_bundle : is_bundle C''.
  Proof. ind_bundle. Qed.

  Lemma C''_is_KMP : bundle_in_SS C'' (KMP_StrandSpace secure_templates Fresh).
  Proof. solve_bundle_in_SS. Qed.

  Lemma C''_fresh_sound : forall t, Fresh t -> originates_at_most_once_in C'' t.
  Proof. intros t Ht; rewrite Ht; solve_at_most_once_in. Qed.

  (** The run ends with the penetrator holding a device handle, stamped with the
      imported type, for a key it picked itself. *)
  Lemma attacker_key_has_a_device_handle :
    is_node_of (s_u, 2) C'' /\ uns_term (s_u, 2) = ⟨ #katt ⋅ $K2 ⟩_mk.
  Proof. split; [ indb_in | reflexivity ]. Qed.

  (** The injected key is not a device key, so [secrecy] says nothing about it and
      is not contradicted: it speaks only of keys the device generated. *)
  Lemma injected_key_is_not_a_device_key : ~ K_d katt.
  Proof. intro H; inversion H. Qed.

  (** And here the injection leads nowhere: no key can be wrapped under [katt],
      because the imported type may encrypt data and nothing of key type.  This is
      the step a policy has to forbid. *)
  Lemma nothing_wraps_under_the_injected_key :
    forall KT, ~ set_In (K2, Enc, KDn KT) secure_templates.
  Proof. intros KT H; simpl in H; intuition discriminate. Qed.

End KMPKeyInjection.
