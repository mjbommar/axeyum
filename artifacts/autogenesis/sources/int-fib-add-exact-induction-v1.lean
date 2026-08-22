import AxeyumIntFibAddInductionAdapterV1
import AxeyumIntFibAddConstructorLawsV1

namespace Axeyum.Autogenesis

theorem intSuccPredInductionV1
    (P : Int → Prop)
    (base : P 0)
    (forward : ∀ n : Int, P n → P (n + 1))
    (backward : ∀ n : Int, P n → P (n - 1)) :
    ∀ n : Int, P n :=
  intSuccPredInductionResidualV1
    P
    (fun n => n + 1)
    (fun n => n - 1)
    intConstructorSplitV1
    intOfNatZeroV1
    intOfNatSuccV1
    intNegSuccZeroV1
    intNegSuccSuccV1
    base
    forward
    backward

end Axeyum.Autogenesis
