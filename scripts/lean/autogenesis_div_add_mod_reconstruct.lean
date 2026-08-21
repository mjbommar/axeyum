import autogenesis_div_mod_go_reconstruct_v2

namespace Axeyum.Autogenesis

theorem divAddModReconstruct (m n : Nat) :
    n * (m / n) + m % n = m := by
  cases n with
  | zero =>
      rw [Nat.div_zero, Nat.mod_zero, Nat.zero_mul, Nat.zero_add]
  | succ n =>
      have hn : 0 < Nat.succ n := Nat.zero_lt_succ n
      rw [← Nat.modCore_eq_mod]
      unfold Nat.div Nat.modCore
      exact divModGoReconstruct
        (Nat.succ n) hn (Nat.succ m) m (Nat.lt_succ_self m)

end Axeyum.Autogenesis
