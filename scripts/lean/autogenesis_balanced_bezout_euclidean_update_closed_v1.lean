import AxeyumAutogenesisBalancedBezoutEuclideanUpdateV2
import AxeyumAutogenesisBalancedBezoutCleanMulLeavesV1

namespace Axeyum.Autogenesis

theorem balancedBezoutEuclideanUpdateClosedV1
    (divisor dividend remainder quotient common : Nat)
    (divisionEquation : divisor * quotient + remainder = dividend)
    (recursive : BalancedBezoutUpdateV2 remainder divisor common) :
    BalancedBezoutUpdateV2 divisor dividend common :=
  balancedBezoutEuclideanUpdateV2
    balancedBezoutMulAssocLeafV1
    balancedBezoutRightDistribLeafV1
    divisor dividend remainder quotient common divisionEquation recursive

end Axeyum.Autogenesis
