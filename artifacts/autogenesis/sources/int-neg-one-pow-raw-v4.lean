import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem natZeroAddV1 : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (natZeroAddV1 n)

theorem natMulOneV1 (n : Nat) : n * 1 = n :=
  natZeroAddV1 n

theorem natOnePowV1 : ∀ k : Nat, 1 ^ k = 1
  | 0 => rfl
  | k + 1 => by
      change 1 ^ k * 1 = 1
      exact (natMulOneV1 (1 ^ k)).trans (natOnePowV1 k)

theorem intNegOnePowRawV2 (k : Nat) :
    (-1 : Int) ^ k = if k % 2 = 0 then 1 else -1 := by
  change
    (if k % 2 = 0 then Int.ofNat (1 ^ k) else Int.negOfNat (1 ^ k)) =
      if k % 2 = 0 then 1 else -1
  by_cases h : k % 2 = 0
  · exact
      (if_pos h).trans
        ((congrArg Int.ofNat (natOnePowV1 k)).trans (if_pos h).symm)
  · exact
      (if_neg h).trans
        ((congrArg Int.negOfNat (natOnePowV1 k)).trans (if_neg h).symm)

end Axeyum.Autogenesis
