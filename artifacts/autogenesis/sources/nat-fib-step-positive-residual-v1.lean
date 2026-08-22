import Init.Data.Nat.Basic

namespace Axeyum.Autogenesis

theorem natFibStepPositiveResidualV1
    (fibFn : Nat → Nat)
    (recurrence : ∀ {n}, fibFn (n + 2) = fibFn n + fibFn (n + 1))
    (addPositiveRight : ∀ {b : Nat} (a : Nat), 0 < b → 0 < a + b) :
    ∀ n, 0 < fibFn (n + 1) → 0 < fibFn (n + 2) := by
  intro n h
  rw [recurrence]
  exact addPositiveRight (fibFn n) h

end Axeyum.Autogenesis
