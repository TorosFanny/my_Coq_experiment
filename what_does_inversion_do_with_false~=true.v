Definition true_not_false : true = false ->False :=
  fun H =>
    match H (*in _ = b
            return if b then True else False*)
    with
    | eq_refl => I:True
    end.