Lemma nat_neq_False_2 : (nat = False) -> (False : Type(*or Set*)).
Proof.
  intros H.
  rewrite <- H.
  apply 0.
Qed.

Lemma nat_neq_False_3 : ~(nat = False).
Proof.
  intros H.
  destruct (nat_neq_False_2 H).
Qed.

Inductive Fal : Type :=. (*Fal's type can be Prop, Set, Type*)
Inductive Fel : Set :=. (*Fel's type can be Set, Type not including Prop*)