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

theorem modCoreEqMod (n m : Nat) : Nat.modCore n m = n % m := by
  change Nat.modCore n m = Nat.mod n m
  match n, m with
  | 0, _ =>
      rw [modCoreEq]
      exact if_neg fun ⟨hlt, hle⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | (_ + 1), _ =>
      rw [Nat.mod]
      dsimp
      refine iteInduction (fun _ => rfl) (fun h => ?_)
      rw [modCoreEq]
      exact if_neg fun ⟨_hlt, hle⟩ => h hle

theorem modEq (x y : Nat) : x % y =
    if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [← modCoreEqMod, ← modCoreEqMod, modCoreEq]

theorem modEqSubMod {a b : Nat} (h : a ≥ b) : a % b = (a - b) % b :=
  match Nat.eq_zero_or_pos b with
  | Or.inl hzero => hzero.symm ▸ (Nat.sub_zero a).symm ▸ rfl
  | Or.inr hpos => (modEq a b).symm ▸ if_pos ⟨hpos, h⟩

end Axeyum.NatMod
