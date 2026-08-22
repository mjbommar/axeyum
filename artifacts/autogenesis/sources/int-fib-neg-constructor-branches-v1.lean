import Mathlib.Algebra.Group.Int.Even

namespace Axeyum.Autogenesis

theorem intFibNegPositiveBranchResidualV1
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (positivePresentation : ∀ n : Nat,
      fibFn (Int.ofNat n) = Int.ofNat (natFib n))
    (negativeEven : ∀ n : Nat,
      n % 2 = 0 → fibFn (-(Int.ofNat n)) = -Int.ofNat (natFib n))
    (negativeOdd : ∀ n : Nat,
      n % 2 = 1 → fibFn (-(Int.ofNat n)) = Int.ofNat (natFib n))
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (evenPositive : ∀ n : Nat, Even (Int.ofNat n) ↔ n % 2 = 0) :
    ∀ n : Nat,
      fibFn (-(Int.ofNat n)) =
        if Even (Int.ofNat n) then -fibFn (Int.ofNat n) else fibFn (Int.ofNat n) := by
  intro n
  cases modCases n with
  | inl heven =>
      rw [if_pos ((evenPositive n).2 heven)]
      exact (negativeEven n heven).trans
        (congrArg (fun value : Int => -value) (positivePresentation n)).symm
  | inr hodd =>
      have hnot : ¬Even (Int.ofNat n) := by
        intro heven
        exact Nat.zero_ne_one (((evenPositive n).1 heven).symm.trans hodd)
      rw [if_neg hnot]
      exact (negativeOdd n hodd).trans (positivePresentation n).symm

theorem intFibNegNegativeBranchResidualV1
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (positivePresentation : ∀ n : Nat,
      fibFn (Int.ofNat n) = Int.ofNat (natFib n))
    (negativeEven : ∀ n : Nat,
      n % 2 = 0 → fibFn (-(Int.ofNat n)) = -Int.ofNat (natFib n))
    (negativeOdd : ∀ n : Nat,
      n % 2 = 1 → fibFn (-(Int.ofNat n)) = Int.ofNat (natFib n))
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (evenNegative : ∀ n : Nat, Even (-(Int.ofNat n)) ↔ n % 2 = 0)
    (negNeg : ∀ value : Int, -(-value) = value) :
    ∀ k : Nat,
      fibFn (-(Int.negSucc k)) =
        if Even (Int.negSucc k) then -fibFn (Int.negSucc k) else fibFn (Int.negSucc k) := by
  intro k
  let n := k + 1
  change fibFn (Int.ofNat n) =
    if Even (-(Int.ofNat n)) then -fibFn (-(Int.ofNat n)) else fibFn (-(Int.ofNat n))
  cases modCases n with
  | inl heven =>
      rw [if_pos ((evenNegative n).2 heven)]
      exact (positivePresentation n).trans
        ((negNeg (Int.ofNat (natFib n))).symm.trans
          (congrArg (fun value : Int => -value) (negativeEven n heven)).symm)
  | inr hodd =>
      have hnot : ¬Even (-(Int.ofNat n)) := by
        intro heven
        exact Nat.zero_ne_one (((evenNegative n).1 heven).symm.trans hodd)
      rw [if_neg hnot]
      exact (positivePresentation n).trans (negativeOdd n hodd).symm

end Axeyum.Autogenesis
