import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intFibNegNatCastResidualV2
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (parity : Nat → Prop)
    (parityDec : ∀ n, Decidable (parity n))
    (negativePresentation : ∀ n : Nat,
      fibFn (-(n : Int)) =
        if parity n then -Int.ofNat (natFib n) else Int.ofNat (natFib n))
    (powerPresentation : ∀ n : Nat,
      (-1 : Int) ^ (n + 1) = if parity n then -1 else 1)
    (negOneMul : ∀ x : Int, (-1 : Int) * x = -x)
    (oneMul : ∀ x : Int, (1 : Int) * x = x) :
    ∀ n : Nat,
      fibFn (-(n : Int)) = (-1 : Int) ^ (n + 1) * Int.ofNat (natFib n) := by
  intro n
  cases parityDec n with
  | isTrue h =>
      have hnegative : fibFn (-(n : Int)) = -Int.ofNat (natFib n) :=
        (negativePresentation n).trans (if_pos h)
      have hpower : (-1 : Int) ^ (n + 1) = -1 :=
        (powerPresentation n).trans (if_pos h)
      have hproduct :
          (-1 : Int) ^ (n + 1) * Int.ofNat (natFib n) =
            -Int.ofNat (natFib n) :=
        (congrArg (fun value : Int => value * Int.ofNat (natFib n)) hpower).trans
          (negOneMul (Int.ofNat (natFib n)))
      exact hnegative.trans hproduct.symm
  | isFalse h =>
      have hnegative : fibFn (-(n : Int)) = Int.ofNat (natFib n) :=
        (negativePresentation n).trans (if_neg h)
      have hpower : (-1 : Int) ^ (n + 1) = 1 :=
        (powerPresentation n).trans (if_neg h)
      have hproduct :
          (-1 : Int) ^ (n + 1) * Int.ofNat (natFib n) =
            Int.ofNat (natFib n) :=
        (congrArg (fun value : Int => value * Int.ofNat (natFib n)) hpower).trans
          (oneMul (Int.ofNat (natFib n)))
      exact hnegative.trans hproduct.symm

end Axeyum.Autogenesis
