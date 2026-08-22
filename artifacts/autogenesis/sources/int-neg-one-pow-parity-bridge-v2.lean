import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegOnePowParityBridgeV2
    (rawPower : ∀ k : Nat,
      (-1 : Int) ^ k = if k % 2 = 0 then 1 else -1)
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (succOne : ∀ {n : Nat}, n % 2 = 0 → (n + 1) % 2 = 1)
    (succZero : ∀ {n : Nat}, n % 2 = 1 → (n + 1) % 2 = 0) :
    ∀ n : Nat, (-1 : Int) ^ (n + 1) = if n % 2 = 0 then -1 else 1 := by
  intro n
  cases modCases n with
  | inl heven =>
      have hnext : (n + 1) % 2 = 1 := succOne heven
      have hnextNe : (n + 1) % 2 ≠ 0 := by
        intro hzero
        cases hnext.symm.trans hzero
      exact (rawPower (n + 1)).trans ((if_neg hnextNe).trans (if_pos heven).symm)
  | inr hodd =>
      have hne : n % 2 ≠ 0 := by
        intro hzero
        cases hodd.symm.trans hzero
      have hnext : (n + 1) % 2 = 0 := succZero hodd
      exact (rawPower (n + 1)).trans ((if_pos hnext).trans (if_neg hne).symm)

end Axeyum.Autogenesis
