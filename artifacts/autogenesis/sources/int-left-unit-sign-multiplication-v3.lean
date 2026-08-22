import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intOneMulV1 (x : Int) : (1 : Int) * x = x := by
  cases x <;> rfl

theorem intNegOneMulV1 (x : Int) : (-1 : Int) * x = -x := by
  cases x <;> rfl

end Axeyum.Autogenesis
