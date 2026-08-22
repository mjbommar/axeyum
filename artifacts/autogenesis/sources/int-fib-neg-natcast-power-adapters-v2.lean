import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intFibPowerEvenAdapterV2
    (presentation : ∀ n : Nat,
      (-1 : Int) ^ (n + 1) = if n % 2 = 0 then -1 else 1) :
    ∀ n : Nat, n % 2 = 0 → (-1 : Int) ^ (n + 1) = -1 := by
  intro n heven
  exact (presentation n).trans (if_pos heven)

theorem intFibPowerOddAdapterV2
    (presentation : ∀ n : Nat,
      (-1 : Int) ^ (n + 1) = if n % 2 = 0 then -1 else 1) :
    ∀ n : Nat, n % 2 = 1 → (-1 : Int) ^ (n + 1) = 1 := by
  intro n hodd
  have hne : n % 2 ≠ 0 := by
    intro heven
    cases hodd.symm.trans heven
  exact (presentation n).trans (if_neg hne)

end Axeyum.Autogenesis
