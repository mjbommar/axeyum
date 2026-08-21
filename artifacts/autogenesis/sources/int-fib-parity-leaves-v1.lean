import Mathlib.Data.Int.Basic

namespace Axeyum.IntFib

theorem succOne {n : Nat} (h : n % 2 = 0) : (n + 1) % 2 = 1 := by
  calc
    (n + 1) % 2 = (n % 2 + 1 % 2) % 2 := Nat.add_mod n 1 2
    _ = (0 + 1 % 2) % 2 := congrArg (fun q => (q + 1 % 2) % 2) h
    _ = 1 := rfl

theorem succZero {n : Nat} (h : n % 2 = 1) : (n + 1) % 2 = 0 := by
  calc
    (n + 1) % 2 = (n % 2 + 1 % 2) % 2 := Nat.add_mod n 1 2
    _ = (1 + 1 % 2) % 2 := congrArg (fun q => (q + 1 % 2) % 2) h
    _ = 0 := rfl

theorem modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1
  | 0 => Or.inl rfl
  | n + 1 => by
      rcases modCases n with h | h
      · exact Or.inr (succOne h)
      · exact Or.inl (succZero h)

end Axeyum.IntFib
