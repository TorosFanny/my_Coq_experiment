Theorem eq_comm: forall (X : Type) (n m : X), n=m -> m=n.
Proof.
  intros X n.
  apply (eq_ind n (fun m => m = n)).
  apply eq_refl.
Qed.