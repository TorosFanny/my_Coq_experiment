Inductive reFalse : Prop :=
 | re : reFalse -> reFalse.

Theorem reFalse_is_False : reFalse -> False.
Proof.
 intros.
 induction H.
 exact IHreFalse.
Qed.
