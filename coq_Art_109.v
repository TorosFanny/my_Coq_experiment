Theorem nnnpnp : forall P : Prop, ~~~P -> ~P.
Proof.
  intros.
  unfold not. unfold not in H.
  intros.
  apply H.
  intros.
  apply (H1 H0).
Qed.

Theorem nnnppq : forall P Q : Prop, ~~~P -> P -> Q.
Proof.
  intros.
  unfold not in H.
  assert (~P) as nP.
    apply (nnnpnp P H).
  unfold not in nP.
  apply False_ind.
  apply (nP H0).
Qed.