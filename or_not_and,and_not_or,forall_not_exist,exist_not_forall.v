Theorem a1 : forall (P Q : Prop), (P /\ Q) -> ~(~P \/ ~Q).
Proof.
  unfold not.
  intros.
  case H0; intros; case H; intros.
  apply (H1 H2).
  apply (H1 H3).
Qed.

Theorem a2 : forall (P Q : Prop), (P \/ Q) -> ~(~P /\ ~Q).
Proof.
  unfold not.
  intros.
  case H; intros; case H0; intros.
  apply (H2 H1).
  apply (H3 H1).
Qed.

Theorem e1 : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros.
  case H0; intros.
  apply (H1 (H x)).
Qed.

Theorem e2 : forall (X:Type) (P : X -> Prop),
  (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
  unfold not.
  intros.
  case H; intros.
  apply (H0 x H1).
Qed.
  