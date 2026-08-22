import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegDoubleResidualV1
    (natDoubleNeg : ∀ q : Nat,
      -((q : Int) + (q : Int)) = -(q : Int) + -(q : Int))
    (negNeg : ∀ x : Int, -(-x) = x) :
    ∀ x : Int, -(x + x) = -x + -x
  | .ofNat q => natDoubleNeg q
  | .negSucc k => by
      let q := k + 1
      change -(-(q : Int) + -(q : Int)) = (q : Int) + (q : Int)
      exact
        (congrArg (fun value : Int => -value) (natDoubleNeg q)).symm.trans
          (negNeg ((q : Int) + (q : Int)))

end Axeyum.Autogenesis
