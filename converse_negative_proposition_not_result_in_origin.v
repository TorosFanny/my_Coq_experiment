Theorem converse_negative_proposition_not_result_in_origin : (forall (P Q : Prop), ((~Q -> ~P) -> P -> Q)) -> (forall (D : Prop), (~~D -> D)).
Proof.
  intuition.
  apply (H True D).
  intros.
  apply (H0 H1).
  apply I.
Qed.