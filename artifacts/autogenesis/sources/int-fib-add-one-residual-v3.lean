import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intFibAddOneResidualV3
    (fibFn : Int → Int)
    (recurrence : ∀ n : Int, fibFn (n + 2) = fibFn n + fibFn (n + 1))
    (addComm : ∀ a b : Int, a + b = b + a)
    (cancelRight : ∀ a b : Int, a + b + -b = a) :
    ∀ n : Int, fibFn (n + 1) = fibFn (n + 2) - fibFn n := by
  intro n
  change fibFn (n + 1) = fibFn (n + 2) + -fibFn n
  exact
    ((congrArg (fun value => value + -fibFn n) (recurrence n)).trans
      ((congrArg (fun value => value + -fibFn n)
          (addComm (fibFn n) (fibFn (n + 1)))).trans
        (cancelRight (fibFn (n + 1)) (fibFn n)))).symm

end Axeyum.Autogenesis
