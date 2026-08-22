import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegOnePowZeroV1 : (-1 : Int) ^ 0 = 1 := rfl

theorem intNegOnePowSuccV1 (n : Nat) :
    (-1 : Int) ^ (n + 1) = (-1 : Int) ^ n * (-1) :=
  Int.pow_succ (-1 : Int) n

theorem intNegOneMulNegOneV1 : (-1 : Int) * (-1) = 1 := rfl

theorem intOneMulNegOneV1 : (1 : Int) * (-1) = -1 := rfl

end Axeyum.Autogenesis
