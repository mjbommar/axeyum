import Mathlib.Algebra.Group.Int.Even

namespace Axeyum.Autogenesis

theorem intFibNegFunctionResidualV1
    (fib : Int → Int)
    (positiveBranch : ∀ n : Nat,
      fib (-(Int.ofNat n)) =
        if Even (Int.ofNat n) then -fib (Int.ofNat n) else fib (Int.ofNat n))
    (negativeBranch : ∀ k : Nat,
      fib (-(Int.negSucc k)) =
        if Even (Int.negSucc k) then -fib (Int.negSucc k) else fib (Int.negSucc k)) :
    ∀ z : Int, fib (-z) = if Even z then -fib z else fib z := by
  intro z
  cases z with
  | ofNat n => exact positiveBranch n
  | negSucc k => exact negativeBranch k

end Axeyum.Autogenesis
