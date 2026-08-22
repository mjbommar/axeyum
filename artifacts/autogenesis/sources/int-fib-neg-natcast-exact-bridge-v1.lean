import AxeyumIntFibNegNatcastResidualV2
import AxeyumIntFibNegativePresentationV1

namespace Axeyum.Autogenesis

theorem intFibNegNatCastExactBridgeV1
    (negativePresentation : ∀ n : Nat,
      Int.fib (-(n : Int)) =
        if n % 2 = 0 then -Int.ofNat (Nat.fib n) else Int.ofNat (Nat.fib n))
    (powerPresentation : ∀ n : Nat,
      (-1 : Int) ^ (n + 1) = if n % 2 = 0 then -1 else 1)
    (negOneMul : ∀ x : Int, (-1 : Int) * x = -x)
    (oneMul : ∀ x : Int, (1 : Int) * x = x) :
    ∀ n : Nat,
      Int.fib (-(n : Int)) = (-1 : Int) ^ (n + 1) * Int.ofNat (Nat.fib n) :=
  intFibNegNatCastResidualV2
    Int.fib
    Nat.fib
    (fun n => n % 2 = 0)
    (fun _ => inferInstance)
    negativePresentation
    powerPresentation
    negOneMul
    oneMul

end Axeyum.Autogenesis
