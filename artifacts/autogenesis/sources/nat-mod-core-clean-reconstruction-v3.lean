import Mathlib.Data.Int.Basic

namespace Axeyum.NatMod

theorem fuelCongr (x y fuel1 fuel2 : Nat) (hy : 0 < y)
    (h1 : x < fuel1) (h2 : x < fuel2) :
    Nat.modCore.go y hy fuel1 x h1 = Nat.modCore.go y hy fuel2 x h2 := by
  match fuel1, fuel2 with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | Nat.succ fuel1, Nat.succ fuel2 =>
      simp only [Nat.modCore.go]
      split
      next => rw [fuelCongr]
      next => rfl
termination_by structural fuel1

theorem modCoreEq (x y : Nat) : Nat.modCore x y =
    if 0 < y ∧ y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  split
  next hy =>
    rw [Nat.modCore.go]
    split
    next hxy =>
      rw [if_pos ⟨hy, hxy⟩]
      exact fuelCongr (x - y) y x (x - y).succ hy _ _
    next hxy =>
      exact (if_neg (fun h => hxy h.2)).symm
  next hy =>
    exact (if_neg (fun h => hy h.1)).symm

end Axeyum.NatMod
