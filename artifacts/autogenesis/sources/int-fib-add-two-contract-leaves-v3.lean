import Mathlib

namespace Axeyum.IntFib

theorem modCases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  omega

theorem succOne {n : Nat} (h : n % 2 = 0) : (n + 1) % 2 = 1 := by
  omega

theorem succZero {n : Nat} (h : n % 2 = 1) : (n + 1) % 2 = 0 := by
  omega

theorem castAdd (a b : Nat) :
    Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := by
  rfl

theorem evenAdd (a b : Nat) :
    -(Int.ofNat a) =
      -(Int.ofNat a + (Int.ofNat b + Int.ofNat a)) +
        (Int.ofNat b + Int.ofNat a) := by
  omega

theorem oddAdd (a b : Nat) :
    Int.ofNat a =
      Int.ofNat a + (Int.ofNat b + Int.ofNat a) +
        -(Int.ofNat b + Int.ofNat a) := by
  omega

end Axeyum.IntFib
