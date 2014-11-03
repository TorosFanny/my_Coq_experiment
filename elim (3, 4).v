Theorem two_nat : nat.
Proof.
  elim (3, 4).
  intros.
  apply a.
Qed.

Check prod_rect.
(*傻乎乎的样子*)