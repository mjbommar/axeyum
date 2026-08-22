import Mathlib.Data.Int.Fib.Basic

namespace Int


theorem fib_eq_fib_add_two_sub_fib_add_one_residual
    (recurrence : ∀ n : Int, fib (n + 2) = fib n + fib (n + 1))
    (cancelRight : ∀ a b : Int, a + b + -b = a) :
    ∀ n : Int, fib n = fib (n + 2) - fib (n + 1) := by
  intro n
  change fib n = fib (n + 2) + -fib (n + 1)
  exact
    ((congrArg (fun value => value + -fib (n + 1)) (recurrence n)).trans
      (cancelRight (fib n) (fib (n + 1)))).symm


end Int
