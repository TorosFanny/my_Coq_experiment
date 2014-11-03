Theorem not_3_eq_4 : 3 <> 4.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Print not_3_eq_4.
(*看看上一个简单的证明展开后有多长，这说明了inversion策略的复杂性*)