import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intFibNegNatCastDecisionFreeResidualV1
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (negativeEven : ∀ n : Nat,
      n % 2 = 0 → fibFn (-(n : Int)) = -Int.ofNat (natFib n))
    (negativeOdd : ∀ n : Nat,
      n % 2 = 1 → fibFn (-(n : Int)) = Int.ofNat (natFib n))
    (powerEven : ∀ n : Nat,
      n % 2 = 0 → (-1 : Int) ^ (n + 1) = -1)
    (powerOdd : ∀ n : Nat,
      n % 2 = 1 → (-1 : Int) ^ (n + 1) = 1)
    (negOneMul : ∀ x : Int, (-1 : Int) * x = -x)
    (oneMul : ∀ x : Int, (1 : Int) * x = x) :
    ∀ n : Nat,
      fibFn (-(n : Int)) = (-1 : Int) ^ (n + 1) * Int.ofNat (natFib n) := by
  intro n
  cases modCases n with
  | inl heven =>
      have hproduct :
          (-1 : Int) ^ (n + 1) * Int.ofNat (natFib n) =
            -Int.ofNat (natFib n) :=
        (congrArg (fun value : Int => value * Int.ofNat (natFib n))
          (powerEven n heven)).trans
          (negOneMul (Int.ofNat (natFib n)))
      exact (negativeEven n heven).trans hproduct.symm
  | inr hodd =>
      have hproduct :
          (-1 : Int) ^ (n + 1) * Int.ofNat (natFib n) =
            Int.ofNat (natFib n) :=
        (congrArg (fun value : Int => value * Int.ofNat (natFib n))
          (powerOdd n hodd)).trans
          (oneMul (Int.ofNat (natFib n)))
      exact (negativeOdd n hodd).trans hproduct.symm

end Axeyum.Autogenesis
