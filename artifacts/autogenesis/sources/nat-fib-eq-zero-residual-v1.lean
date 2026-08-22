import Init.Prelude

namespace Axeyum.Autogenesis

theorem natFibEqZeroResidualV1
    (fibFn : Nat → Nat)
    (fibZero : fibFn 0 = 0)
    (fibPos : ∀ {n}, 0 < fibFn n ↔ 0 < n)
    (succPos : ∀ n : Nat, 0 < Nat.succ n) :
    ∀ {n}, fibFn n = 0 ↔ n = 0 := by
  intro n
  cases n with
  | zero =>
      constructor
      · intro _
        rfl
      · intro _
        exact fibZero
  | succ k =>
      constructor
      · intro fibIsZero
        have positive : 0 < fibFn (Nat.succ k) := fibPos.mpr (succPos k)
        rw [fibIsZero] at positive
        nomatch positive
      · intro successorIsZero
        nomatch successorIsZero

end Axeyum.Autogenesis
