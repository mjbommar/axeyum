import Mathlib.Data.Nat.ModEq

/-!
An empty-footprint behavior-contract family for the exact Lean 4.30 `Nat.mod`
implementation used by the imported `Nat.ModEq` population.

The public remainder laws carry `propext` in this environment. These proofs
instead rebuild the needed fuel congruence and recurrence directly over
`Nat.mod`, `Nat.modCore`, and `Nat.modCore.go`.
-/

namespace Axeyum.Autogenesis.Candidate.NatModRemainder

theorem modCoreGoFuelCongr
    (x y fuel₁ fuel₂ : Nat)
    (hy : 0 < y)
    (h₁ : x < fuel₁)
    (h₂ : x < fuel₂) :
    Nat.modCore.go y hy fuel₁ x h₁ = Nat.modCore.go y hy fuel₂ x h₂ := by
  match fuel₁, fuel₂ with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | Nat.succ fuel₁, Nat.succ fuel₂ =>
    simp only [Nat.modCore.go]
    split
    next => rw [modCoreGoFuelCongr]
    next => rfl
termination_by structural fuel₁

theorem modCoreEq (x y : Nat) : Nat.modCore x y =
    if 0 < y ∧ y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  split
  next hy =>
    rw [Nat.modCore.go]
    split
    next hle =>
      rw [if_pos ⟨hy, hle⟩]
      apply modCoreGoFuelCongr
    next hnle =>
      rw [if_neg (fun pair => hnle pair.2)]
  next hzero =>
    rw [if_neg (fun pair => hzero pair.1)]

theorem modCoreEqMod (n m : Nat) : Nat.modCore n m = n % m := by
  change Nat.modCore n m = Nat.mod n m
  match n, m with
  | 0, _ =>
    rw [modCoreEq]
    exact if_neg fun ⟨hlt, hle⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | (_ + 1), _ =>
    rw [Nat.mod.eq_def]
    dsimp
    refine iteInduction (fun _ => rfl) (fun h => ?false)
    rw [modCoreEq]
    exact if_neg fun ⟨_hlt, hle⟩ => h hle

theorem modEq (x y : Nat) : x % y =
    if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [← modCoreEqMod x y, ← modCoreEqMod (x - y) y, modCoreEq]

theorem addSubCancelRight (n m : Nat) : n + m - m = n := by
  induction m with
  | zero => rw [Nat.add_zero, Nat.sub_zero]
  | succ m ih =>
    rw [Nat.add_succ, Nat.succ_sub_succ_eq_sub, ih]

theorem addModRight (x z : Nat) : (x + z) % z = x % z := by
  cases z with
  | zero => rw [Nat.add_zero]
  | succ z =>
    rw [modEq]
    rw [if_pos ⟨Nat.zero_lt_succ _, Nat.le_add_left _ _⟩]
    rw [addSubCancelRight]

theorem addModLeft (x z : Nat) : (x + z) % x = z % x := by
  rw [Nat.add_comm]
  exact addModRight z x

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
