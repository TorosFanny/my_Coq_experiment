Inductive reFalse : Prop :=
 | re : reFalse -> reFalse.

Theorem reFalse_is_False : reFalse -> False.
Proof.
 intros.
 induction H.
 exact IHreFalse.
Qed.
(*
Result for command Check reFalse_ind . :
reFalse_ind
     : forall P : Prop, (reFalse -> P -> P) -> reFalse -> P
*)
