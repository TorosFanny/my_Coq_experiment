Theorem extensionality : forall {A B : Type} (f g : A -> B) (x : A), f x = g x -> f = g.
Proof.
  intros.
  generalize dependent x.
Abort.