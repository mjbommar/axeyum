import AxeyumIntFibNegativePresentationV1

namespace Axeyum.Autogenesis

theorem intFibNegativeEvenAdapterV1
    (presentation : ∀ n : Nat,
      Int.fib (-(n : Int)) =
        if n % 2 = 0 then -Int.ofNat (Nat.fib n) else Int.ofNat (Nat.fib n)) :
    ∀ n : Nat, n % 2 = 0 →
      Int.fib (-(n : Int)) = -Int.ofNat (Nat.fib n) := by
  intro n heven
  exact (presentation n).trans (if_pos heven)

theorem intFibNegativeOddAdapterV1
    (presentation : ∀ n : Nat,
      Int.fib (-(n : Int)) =
        if n % 2 = 0 then -Int.ofNat (Nat.fib n) else Int.ofNat (Nat.fib n)) :
    ∀ n : Nat, n % 2 = 1 →
      Int.fib (-(n : Int)) = Int.ofNat (Nat.fib n) := by
  intro n hodd
  have hne : n % 2 ≠ 0 := by
    intro heven
    cases hodd.symm.trans heven
  exact (presentation n).trans (if_neg hne)

theorem intFibPowerEvenAdapterV1
    (presentation : ∀ n : Nat,
      (-1 : Int) ^ (n + 1) = if n % 2 = 0 then -1 else 1) :
    ∀ n : Nat, n % 2 = 0 → (-1 : Int) ^ (n + 1) = -1 := by
  intro n heven
  exact (presentation n).trans (if_pos heven)

theorem intFibPowerOddAdapterV1
    (presentation : ∀ n : Nat,
      (-1 : Int) ^ (n + 1) = if n % 2 = 0 then -1 else 1) :
    ∀ n : Nat, n % 2 = 1 → (-1 : Int) ^ (n + 1) = 1 := by
  intro n hodd
  have hne : n % 2 ≠ 0 := by
    intro heven
    cases hodd.symm.trans heven
  exact (presentation n).trans (if_neg hne)

end Axeyum.Autogenesis
