import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intFibEqAddTwoSubAddOneResidualV2
    (fibFn : Int → Int)
    (recurrence : ∀ n : Int, fibFn (n + 2) = fibFn n + fibFn (n + 1))
    (cancelRight : ∀ a b : Int, a + b + -b = a) :
    ∀ n : Int, fibFn n = fibFn (n + 2) - fibFn (n + 1) := by
  intro n
  change fibFn n = fibFn (n + 2) + -fibFn (n + 1)
  exact
    ((congrArg (fun value => value + -fibFn (n + 1)) (recurrence n)).trans
      (cancelRight (fibFn n) (fibFn (n + 1)))).symm

end Axeyum.Autogenesis
