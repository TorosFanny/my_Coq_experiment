Definition admit {T: Type} : T.
Admitted. (*从software fundation 的Sflib.v 里面搞得*)

Theorem The_End_Of_The_World : False.
Proof.
  apply (@admit False).
Qed.