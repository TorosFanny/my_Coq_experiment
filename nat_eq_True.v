Theorem nat_eq_nat : nat = nat.
Proof.
  trivial.
Qed.

Theorem True_neq_False : ~(True = False).
Proof.
  unfold not.
  intros.
  symmetry in H.
  rewrite H.
  trivial.
Qed.

Theorem Prop_eq_prod : forall (a : Prop) (b : Prop), a = b -> (a -> b).
Proof.
  intros.
  rewrite <- H.
  trivial.
Qed.

Theorem Set_eq_prod : forall (a : Set) (b : Set), a = b -> (a -> b).
Proof.
  intros.
  rewrite <- H.
  trivial.
Qed.

Lemma Type_eq_prod : forall (a : Type) (b : Type), a = b -> (a -> b).
Proof.
  intros.
  rewrite <- H.
  trivial.
Qed.
(*
Theorem eq_prod : forall (X : Type) (a : X) (b : X), a = b -> (a -> b).

  Error: In environment
  X : Type
  a : X
  b : X
  The term "a" has type "X" which should be Set, Prop or Type.
*)

Theorem nat_neq_False : ~(nat = False).
Proof.
  unfold not.
  intros.
  apply (Type_eq_prod nat False) in H. (*这个地方只能写成Type_eq_prod nat False, 不知道为什么*)
  inversion H.
  apply 0.
(*
Error: Illegal application (Type Error): 
The term "Type_eq_prod" of type "forall a b : Type, a = b -> a -> b"
cannot be applied to the terms
 "nat" : "Set"
 "False" : "Prop"
 "H" : "nat = False"
 "0" : "nat"
The 3rd term has type "nat = False" which should be coercible to
 "nat = False".
*)
Abort.

Theorem nat_neq_bool : ~(nat = bool).
Proof.
  unfold not.
  intros.
Abort.

Theorem nat_neq_true : ~(nat = True).
Proof.
  unfold not.
  intros.
Abort.

Theorem nat_neq_False : ~(nat = False).
Proof.
  unfold not.
  intros.
  symmetry in H.
  rewrite H.
  trivial.
Qed.