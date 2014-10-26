Lemma blah: forall (P Q: Prop), (forall (f:Prop -> Prop), f Q -> f P) -> P = Q.
  intros P Q H.
  apply (H (fun x => x = Q)).
  reflexivity.
Qed.

Section S.

Hypothesis prop_subst:
  forall (f : Prop -> Prop) (P Q : Prop), 
    (P <-> Q) -> ((f P) <-> (f Q)).

Lemma prop_subst_is_ext: forall P Q, (P <-> Q) -> P = Q.
  intros.
  apply blah.
  intro f.
  destruct (prop_subst f P Q).
  assumption.
  assumption.
Qed.

End S.

Check prop_subst_is_ext.