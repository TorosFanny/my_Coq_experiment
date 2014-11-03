Inductive Empty_set : Set :=.

(*
Result for command Check Empty_set_ind . :
Empty_set_ind
     : forall (P : Empty_set -> Prop) (e : Empty_set), P e
*)
Inductive Empty_type : Type :=.
(*
Result for command Check Empty_type_ind . :
Empty_type_ind
     : forall (P : Empty_type -> Prop) (e : Empty_type), P e
*)
Theorem empty_false : Empty_set -> False.
Proof.
  intros.
  apply (Empty_set_ind (fun _ => False) H).
Qed.