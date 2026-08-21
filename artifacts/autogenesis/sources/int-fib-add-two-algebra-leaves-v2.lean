import Mathlib

namespace Axeyum.IntFib

theorem evenAdd (a b : Nat) :
    -(Int.ofNat a) =
      -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
        (Int.ofNat b + Int.ofNat a) := by
  let x := Int.ofNat a
  let z := Int.ofNat b + Int.ofNat a
  have hneg : -x + -z = -(x + z) :=
    (Int.add_comm (-x) (-z)).trans (neg_add_rev x z).symm
  exact
    (Int.neg_add_cancel_right (-x) z).symm.trans
      (congrArg (fun q => q + z) hneg)

theorem oddAdd (a b : Nat) :
    Int.ofNat a =
      Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
        -(Int.ofNat b + Int.ofNat a) := by
  exact
    (Int.add_neg_cancel_right
      (Int.ofNat a) (Int.ofNat b + Int.ofNat a)).symm

end Axeyum.IntFib
