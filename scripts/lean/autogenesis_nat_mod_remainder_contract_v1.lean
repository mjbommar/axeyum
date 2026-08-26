import Mathlib.Data.Nat.ModEq

/-!
An empty-footprint behavior contract for the exact Lean 4.30 `Nat.mod`
implementation used by the imported `Nat.ModEq` population.

This intentionally does not call the public `Nat.mod_self`: that theorem's
Lean 4.30 proof closure contains `propext`.  Instead it follows the concrete
`Nat.mod` / `Nat.modCore.go` reduction spine and stops after the one subtraction
needed for a modulus applied to itself.
-/

namespace Axeyum.Autogenesis.Candidate.NatModRemainder

theorem modSelf (n : Nat) : n % n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    change Nat.mod (Nat.succ n) (Nat.succ n) = 0
    simp only [Nat.mod.eq_def, if_pos (Nat.le_refl _)]
    unfold Nat.modCore
    rw [dif_pos (Nat.zero_lt_succ _)]
    unfold Nat.modCore.go
    simp only [dif_pos (Nat.le_refl _), Nat.sub_self]
    unfold Nat.modCore.go
    rw [dif_neg (Nat.not_succ_le_zero _)]

end Axeyum.Autogenesis.Candidate.NatModRemainder
