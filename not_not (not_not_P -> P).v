Theorem nnnnn : forall (P : Prop), ~~(~~P -> P).
Proof.
(*  unfold not.
  intros.
  apply H.
  intros. *)
 tauto.
(* intuition.*)
Qed.