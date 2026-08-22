import AxeyumIntFibNegativePresentationV1

namespace Axeyum.Autogenesis

theorem intFibNegOuterResidualV2
    (positiveBranch : ∀ n : Nat,
      Int.fib (-(Int.ofNat n)) =
        if Even (Int.ofNat n) then -Int.fib (Int.ofNat n) else Int.fib (Int.ofNat n))
    (negativeBranch : ∀ k : Nat,
      Int.fib (-(Int.negSucc k)) =
        if Even (Int.negSucc k) then -Int.fib (Int.negSucc k) else Int.fib (Int.negSucc k)) :
    ∀ z : Int, Int.fib (-z) = if Even z then -Int.fib z else Int.fib z := by
  intro z
  cases z with
  | ofNat n => exact positiveBranch n
  | negSucc k => exact negativeBranch k

end Axeyum.Autogenesis
