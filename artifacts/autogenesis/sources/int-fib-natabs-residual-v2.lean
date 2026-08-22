import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intFibNatAbsResidualV2
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (positivePresentation : ∀ n : Nat,
      fibFn (Int.ofNat n) = Int.ofNat (natFib n))
    (negativeEven : ∀ n : Nat,
      n % 2 = 0 → fibFn (-(Int.ofNat n)) = -Int.ofNat (natFib n))
    (negativeOdd : ∀ n : Nat,
      n % 2 = 1 → fibFn (-(Int.ofNat n)) = Int.ofNat (natFib n))
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (natAbsNeg : ∀ z : Int, (-z).natAbs = z.natAbs)
    (natAbsOfNat : ∀ n : Nat, (Int.ofNat n).natAbs = n) :
    ∀ m : Int, (fibFn m).natAbs = natFib m.natAbs := by
  intro m
  cases m with
  | ofNat n => rw [positivePresentation, natAbsOfNat, natAbsOfNat]
  | negSucc k =>
      let n := k + 1
      change
        (fibFn (-(Int.ofNat n))).natAbs =
          natFib (Int.natAbs (-(Int.ofNat n)))
      cases modCases n with
      | inl heven =>
          rw [negativeEven n heven, natAbsNeg, natAbsOfNat, natAbsNeg, natAbsOfNat]
      | inr hodd => rw [negativeOdd n hodd, natAbsOfNat, natAbsNeg, natAbsOfNat]

end Axeyum.Autogenesis
