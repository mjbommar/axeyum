import Mathlib.Data.Int.Basic

namespace Axeyum.NatMod

theorem modCoreEq (x y : Nat) : Nat.modCore x y =
    if 0 < y ∧ y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  split
  next hy =>
    rw [Nat.modCore.go]
    split
    next hxy =>
      rw [if_pos ⟨hy, hxy⟩]
      exact «_private.Init.Data.Nat.Div.Basic.0.Nat.modCore.go.fuel_congr»
        (x - y) y x (x - y).succ hy _ _
    next hxy =>
      exact (if_neg (fun h => hxy h.2)).symm
  next hy =>
    exact (if_neg (fun h => hy h.1)).symm

end Axeyum.NatMod
