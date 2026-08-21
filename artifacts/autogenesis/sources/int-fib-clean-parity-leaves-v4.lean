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

namespace Axeyum.IntFib

theorem modStepTwo (k : Nat) : (k + 2) % 2 = k % 2 := by
  have h := Axeyum.NatMod.modEqSubMod (a := k + 2) (b := 2) (Nat.le_add_left 2 k)
  exact h

theorem succOne : ∀ {n : Nat}, n % 2 = 0 → (n + 1) % 2 = 1
  | 0, _ => rfl
  | 1, h => by cases h
  | n + 2, h => by
      have hn : n % 2 = 0 := (modStepTwo n).symm.trans h
      exact (modStepTwo (n + 1)).trans (succOne hn)

theorem succZero : ∀ {n : Nat}, n % 2 = 1 → (n + 1) % 2 = 0
  | 0, h => by cases h
  | 1, _ => rfl
  | n + 2, h => by
      have hn : n % 2 = 1 := (modStepTwo n).symm.trans h
      exact (modStepTwo (n + 1)).trans (succZero hn)

theorem modCases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have hlt : n % 2 < 2 := @Nat.mod_lt n 2 (Nat.zero_lt_succ 1)
  cases hmod : n % 2 with
  | zero => exact Or.inl rfl
  | succ k =>
      cases k with
      | zero => exact Or.inr rfl
      | succ k =>
          have hbad : k + 2 < 2 := hmod ▸ hlt
          exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_left 2 k)) hbad)

end Axeyum.IntFib
