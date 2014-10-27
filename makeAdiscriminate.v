Theorem contro : 0 = S 0 -> False.
Proof.
  intros.
  Definition nat2log : nat -> Prop :=
    fun n =>
    match n with
    | 0 => False
    | _ => True
    end.
  assert (False = True) as trueIsfalse.
    apply (f_equal nat2log H).
  rewrite trueIsfalse.
  trivial.
Qed.