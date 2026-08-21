import Mathlib.Data.Int.Basic

namespace Axeyum.IntFib

theorem evenAdd (a b : Nat) :
    -(Int.ofNat a) =
      -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
        (Int.ofNat b + Int.ofNat a) := by
  have cancel : ∀ x z : Nat,
      -(Int.ofNat x + Int.ofNat z) + Int.ofNat z = -(Int.ofNat x) := by
    intro x z
    induction z generalizing x with
    | zero => rw [Int.add_zero, Int.add_zero]
    | succ z ih =>
        cases x with
        | zero => exact ih 0
        | succ x => exact ih (x + 1)
  exact (cancel a (b + a)).symm

theorem oddAdd (a b : Nat) :
    Int.ofNat a =
      Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
        -(Int.ofNat b + Int.ofNat a) := by
  have cancel : ∀ x z : Nat,
      Int.ofNat x + Int.ofNat z + -(Int.ofNat z) = Int.ofNat x := by
    intro x z
    induction z generalizing x with
    | zero => rw [Int.add_zero, Int.add_zero]
    | succ z ih =>
        cases x with
        | zero => exact ih 0
        | succ x => exact ih (x + 1)
  exact (cancel a (b + a)).symm

end Axeyum.IntFib
