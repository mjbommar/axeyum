import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intOneMulV1 (x : Int) : (1 : Int) * x = x :=
  one_mul x

theorem intNegOneMulV1 (x : Int) : (-1 : Int) * x = -x :=
  (neg_mul (1 : Int) x).trans (congrArg (fun value : Int => -value) (one_mul x))

end Axeyum.Autogenesis
