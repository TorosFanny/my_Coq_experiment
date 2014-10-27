(*
  构造演算中的三元组                         s''                        s                     s'
*)

Definition Impredicativity_Type_False : Type := forall P : (Type : Type), (P           : Type).
(*高阶类型, 从左往右，第三个Type的下标为i，第四个Type下标为j，第一个Type下标为k，满足i<=k, j<=k*)
Definition Impredicativity_Prop_False : Prop := forall P : (Prop : Type), (P           : Prop).
(*Prop中的非直谓类型*)
Definition set_empty : (forall s : Set, Prop) := fun (s : Set) => False.
Definition Impredicativity_Set_False  : Prop := forall P : (Set :  Type), (set_empty P : Prop).
(*Prop中的非直谓类型*)
(*
Definition Impredicativity_Set_False  : Prop := forall P : (Set  : Type), (P : Prop <> Set).
Prop中的非直谓类型
这里是类型检查不通过的，体现了Prop和Set的不同
*)
Definition nat_to_nat                 : Set  := forall n : (nat  : Set),  (nat         : Set).


Inductive lucy_is_fucked : Prop :=
  | fucked_by_me  : lucy_is_fucked
  | fucked_by_dog : lucy_is_fucked.
Inductive lucy_is_not_virgin : Prop :=
  | she_has_made_love : lucy_is_not_virgin
  | she_is_raped      : lucy_is_not_virgin.

Definition result_of_fucked_by_different_guy (who_fuck:lucy_is_fucked) : lucy_is_not_virgin :=
match who_fuck with
  | fucked_by_me  => she_has_made_love
  | fucked_by_dog => she_is_raped
end.

Definition a_fucked_woman_is_not_virgin : Prop := (lucy_is_fucked : Prop) -> (lucy_is_not_virgin : Prop).
Definition why_a_fucked_woman_is_not_virgin : a_fucked_woman_is_not_virgin.
Proof.
  unfold a_fucked_woman_is_not_virgin.
  apply result_of_fucked_by_different_guy.
Qed.

(*A more serious example of Prop Prop Prop*)
Definition classic (p : Prop) : Prop := (~ ~ (p : Prop)) -> (p : Prop).
(*the above proposition is not proveable*)

Inductive wether : Prop :=
  | rainning : wether
  | snowing  : wether
  | fine     : wether.

Inductive what_is_lucy_doing : Prop :=
  | being_fucked
  | sleeping.

Definition lucy_be_fucked_if_it_is_not_fine (w : wether) : what_is_lucy_doing :=
match w with
  | rainning => being_fucked
  | snowing  => being_fucked
  | fine     => sleeping
end.

Inductive even : nat -> Prop :=
  | even0  : even 0
  | evenSS : forall (n:nat), even n -> even (S (S n)).
Definition all_nat_is_even            : Prop := forall n : (nat  : Set),  (even n      : Prop).