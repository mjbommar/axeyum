import AxeyumIntFibNegativePresentationV1

namespace Axeyum.Autogenesis

theorem intFibNegOuterResidualV1
    (positiveBranch : ∀ n : Nat,
      Int.fib (-(n : Int)) =
        if Even (n : Int) then -Int.fib (n : Int) else Int.fib (n : Int))
    (negativeBranch : ∀ n : Nat,
      Int.fib (-(-(n : Int))) =
        if Even (-(n : Int)) then -Int.fib (-(n : Int)) else Int.fib (-(n : Int))) :
    ∀ z : Int, Int.fib (-z) = if Even z then -Int.fib z else Int.fib z := by
  intro z
  obtain ⟨n, h | h⟩ := z.eq_nat_or_neg
  · subst z
    exact positiveBranch n
  · subst z
    exact negativeBranch n

end Axeyum.Autogenesis
