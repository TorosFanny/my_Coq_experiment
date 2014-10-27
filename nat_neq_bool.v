Lemma bool_has_two : exists b1 b2 : bool, forall b3 : bool, b3 = b1 \/ b3 = b2.
Proof.
  exists true.
  exists false.
  intros.
  destruct b3.
  left. reflexivity.
  right. reflexivity.
Qed.

Lemma not_nat_has_two : (exists n1 n2 : nat, forall n3 : nat, n3 = n1 \/ n3 = n2) -> False.
Proof.
  intros.
Admitted.

Theorem nat_neq_bool : nat <> bool.
Proof.
  unfold not.
  intros.
  apply not_nat_has_two.
  rewrite H.
  apply bool_has_two.
Qed.
  