import Mathlib.Data.Int.Basic

namespace Axeyum.IntFib

theorem succOne : ∀ {n : Nat}, n % 2 = 0 → (n + 1) % 2 = 1
  | 0, _ => rfl
  | 1, h => by cases h
  | n + 2, h => by
      have step : ∀ k : Nat, (k + 2) % 2 = k % 2 := by
        intro k
        rfl
      have hn : n % 2 = 0 := (step n).symm.trans h
      exact (step (n + 1)).trans (succOne hn)

theorem succZero : ∀ {n : Nat}, n % 2 = 1 → (n + 1) % 2 = 0
  | 0, h => by cases h
  | 1, _ => rfl
  | n + 2, h => by
      have step : ∀ k : Nat, (k + 2) % 2 = k % 2 := by
        intro k
        rfl
      have hn : n % 2 = 1 := (step n).symm.trans h
      exact (step (n + 1)).trans (succZero hn)

theorem modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1
  | 0 => Or.inl rfl
  | n + 1 => by
      rcases modCases n with h | h
      · exact Or.inr (succOne h)
      · exact Or.inl (succZero h)

end Axeyum.IntFib
