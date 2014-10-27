Theorem forallCommutative1 : forall (S1 S2 : Set) (P : S1 -> Prop) (Q : S2 -> Prop) (R : S1 -> S2 -> Prop) (x : S1) (y : S2), (P x -> Q y -> R x y) -> (Q y -> P x -> R x y).
Proof.
  intros.
  auto.
Qed.

Theorem forallCommutative2 (S1 S2 : Set) (P : S1 -> Prop) (Q : S2 -> Prop) (R : S1 -> S2 -> Prop) : forall (x : S1) (y : S2), (P x -> Q y -> R x y) -> (Q y -> P x -> R x y).
Proof.
  intros.
  auto.
Qed.