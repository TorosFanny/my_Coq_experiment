Theorem yes_no : forall (P:Prop), P /\ ~P -> False.
Proof.
  intros.
  apply (@and_ind P (~P) False).
  unfold not.
  intros.
  auto.
  exact H.
Qed.

Definition hd : forall (X:Type) (lis:list X), lis <> nil -> X :=
fun (X : Type) (lis : list X) (H : lis <> nil) =>
list_rect (fun lis0 : list X => lis0 <> nil -> X)
  (fun H0 : nil <> nil => False_rect X (H0 eq_refl))
  (fun (a : X) (lis0 : list X) (_ : lis0 <> nil -> X)
     (_ : (a :: lis0)%list <> nil) => a) lis H.

Open Scope list.
Definition head : forall {X:Type} (lis:list X), lis <> nil -> X.
Proof.
  intros.
  induction lis.
    unfold not in H.
    apply (False_rect X (H eq_refl)).
    
    apply a.
Qed.
Close Scope list.