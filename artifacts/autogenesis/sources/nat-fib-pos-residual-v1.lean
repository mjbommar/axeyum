import Init.Data.Nat.Basic

namespace Axeyum.Autogenesis

theorem natFibPosResidualV1
    (fibFn : Nat → Nat)
    (zeroPresentation : fibFn 0 = 0)
    (onePositive : 0 < fibFn 1)
    (stepPositive : ∀ n, 0 < fibFn (n + 1) → 0 < fibFn (n + 2))
    (successorPositive : ∀ n : Nat, 0 < Nat.succ n) :
    ∀ {n}, 0 < fibFn n ↔ 0 < n := by
  intro n
  cases n with
  | zero =>
      constructor
      · intro h
        rw [zeroPresentation] at h
        nomatch h
      · intro h
        nomatch h
  | succ k =>
      constructor
      · intro _
        exact successorPositive k
      · intro _
        induction k with
        | zero => exact onePositive
        | succ k ih => exact stepPositive k (ih (successorPositive k))

end Axeyum.Autogenesis
