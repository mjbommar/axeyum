import Mathlib.Data.Int.Basic

namespace Axeyum.IntFib

theorem evenAdd (a b : Nat) :
    -(Int.ofNat a) =
      -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
        (Int.ofNat b + Int.ofNat a) := by
  have cancel : ∀ x z : Nat,
      -(Int.ofNat x + Int.ofNat z) + Int.ofNat z = -(Int.ofNat x) := by
    intro x z
    cases x with
    | zero =>
        change Int.subNatNat z z = Int.ofNat 0
        have hzero : z - z = 0 := Nat.sub_self z
        exact
          (Int.subNatNat_of_sub_eq_zero hzero).trans
            (congrArg Int.ofNat hzero)
    | succ x =>
        change Int.subNatNat z ((x + 1) + z) = Int.negSucc x
        have hsucc : ((x + 1) + z) - z = x + 1 := by
          rw [Nat.add_comm (x + 1) z, Nat.add_sub_cancel_left]
        exact Int.subNatNat_of_sub_eq_succ hsucc
  exact (cancel a (b + a)).symm

theorem oddAdd (a b : Nat) :
    Int.ofNat a =
      Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
        -(Int.ofNat b + Int.ofNat a) := by
  have cancel : ∀ x z : Nat,
      Int.ofNat x + Int.ofNat z + -(Int.ofNat z) = Int.ofNat x := by
    intro x z
    change Int.subNatNat (x + z) z = Int.ofNat x
    have hzero : z - (x + z) = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_add_left z x)
    have hdiff : (x + z) - z = x := by
      rw [Nat.add_comm x z, Nat.add_sub_cancel_left]
    exact
      (Int.subNatNat_of_sub_eq_zero hzero).trans
        (congrArg Int.ofNat hdiff)
  exact (cancel a (b + a)).symm

end Axeyum.IntFib
