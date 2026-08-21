import Mathlib.Data.Int.Basic

namespace Axeyum.IntFib

theorem evenAdd (a b : Nat) :
    -(Int.ofNat a) =
      -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
        (Int.ofNat b + Int.ofNat a) := by
  exact (neg_add_cancel_right (Int.ofNat a) (Int.ofNat b + Int.ofNat a)).symm

theorem oddAdd (a b : Nat) :
    Int.ofNat a =
      Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
        -(Int.ofNat b + Int.ofNat a) := by
  exact (add_neg_cancel_right (Int.ofNat a) (Int.ofNat b + Int.ofNat a)).symm

end Axeyum.IntFib
