From strandsrocq.CPSA.Instances Require Import DefaultInstances.

(* Create a concrete instance of Terms *)

Lemma test :
  forall (t t':Text) (n n':Name) (k k':Skey) (a a' b b':Mesg),
  (t = t) ->
  (k = k) ->
  (a = a) ->
  (M_Text t = M_Text t /\ t = t) ->
  (t = t \/ t = t) ->
  (False -> t = t) ->
  (t = t') ->
  (M_Text t = M_Text t) ->
  (M_Text t = M_Text t' /\ t = t) ->
  (M_Skey k = M_Skey k) ->
  (M_Skey k = M_Skey k') ->
  (M_Skey k = M_Text t) ->
  (M_Skey k <> M_Text t) ->
  (K n = K n) ->
  (K n = K n') ->
  (a ⋅ a' = M_Text t) ->
  (a ⋅ a' = b ⋅ b') ->
  (~~M_Skey k = M_Text t) ->
  (#a = #a') ->
  (M_Skey k <> M_Text t) /\ (M_Skey k = M_Skey k') /\ (M_Skey k = M_Text t) /\ (M_Skey k = M_Skey k).
Proof.
  intros.
  (* simplify_prop in |- *.
  simplify_prop in H16. *)
  simplify_prop in * |-.
Qed.
