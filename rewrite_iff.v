Require Export nat_neq_bool.

Theorem rewrite_iff : forall (P Q : Prop), (P <-> Q) -> (P = Q).
Proof.
  intros.
  (* rewrite <- H. --doesn't work, reports Error: Library Coq.Setoids.Setoid has to be required first.*)
Abort.

Definition map : forall (X Y : Type) (M : X -> Y) (f : X -> X), Y -> Y.
Proof.
(*It looks so easy, but actually I cannot prove it*)
Abort.

Theorem rewrite_iff : forall (P : Prop -> Prop) (x y : Prop), (x <-> y) -> (P x <-> P y).
Proof.
  intros.
  destruct H.
  unfold iff.
  split.
Abort.

(*显然存在一个函数f：nat -> bool,也存在一个函数：bool -> nat,但可以证明nat = bool，所以可证下述命题*)
Theorem not_iff_eq_Set : (forall (P Q : Set), (P -> Q) -> (Q -> P) -> P = Q) -> False.
Proof.
  intros.
  specialize (H nat bool).
  assert (nat -> bool) as nat_bool.
    intros Xnat.
    apply (fun n:nat => match n with
                        | 0 => true
                        | _ => false
                        end).
    exact Xnat.
  assert (bool -> nat) as bool_nat.
    intros Xbool.
    exact ((fun b:bool => match b with
                         | true  => 0
                         | false => 1
                         end) Xbool).
  assert (nat = bool) as nat_eq_bool.
    apply (H nat_bool bool_nat).
  apply nat_neq_bool.
  exact nat_eq_bool.
Qed.
(*对于命题，要定义一个有两个元素的真，这样*)
Inductive True2 : Prop :=
 | One : True2
 | Two : True2.

Lemma True_has_one : forall (t0 t1 : True), t0 = t1.
Proof.
  intros.
  destruct t0. destruct t1.
  reflexivity.
Qed.

Lemma not_True2_has_one : (forall (t0 t1 : True2), t0 = t1) -> False.
Proof.
  intros.
  specialize (H One Two).
  inversion H.
Abort.

Lemma True_neq_True2 : True = True2 -> False.
Proof.
Abort.

Theorem iff_eq : forall (P Q : Prop), (P -> Q) -> (Q -> P) -> P = Q.
Proof.
Abort.