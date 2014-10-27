(** * MoreCoq: More About Coq *)

Require Export Poly.

Definition list2pair : forall {X:Type} (x:X), list X -> X*bool :=
  fun X x list =>
     match list with
     | []   => (x, false)
     | a::_ => (a, true)
     end.

Theorem inEqual : forall (x y : nat), [x] = [y] -> x = y.
Proof.
  intros.
  assert ((x, true) = (y, true)).
    apply (f_equal (@list2pair nat x) H).
  apply (f_equal fst H0).
Qed.