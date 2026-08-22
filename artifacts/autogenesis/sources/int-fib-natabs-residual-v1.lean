import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intFibNatAbsResidualV1
    (fibNeg : ∀ z : Int,
      Int.fib (-z) = if Even z then -Int.fib z else Int.fib z)
    (natAbsNeg : ∀ z : Int, (-z).natAbs = z.natAbs) :
    ∀ m : Int, (Int.fib m).natAbs = Nat.fib m.natAbs := by
  intro m
  cases m with
  | ofNat n => rfl
  | negSucc k =>
      change
        (Int.fib (-(Int.ofNat (k + 1)))).natAbs =
          Nat.fib (Int.natAbs (-(Int.ofNat (k + 1))))
      rw [fibNeg, natAbsNeg]
      split
      · rw [natAbsNeg]
        rfl
      · rfl

end Axeyum.Autogenesis
