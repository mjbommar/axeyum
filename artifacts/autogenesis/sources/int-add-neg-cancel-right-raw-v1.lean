import Mathlib.Data.Int.Basic

namespace Axeyum.IntAlgebra

theorem addNegCancelRightRaw (a b : Int) : a + b + -b = a := by
  cases a <;> cases b <;>
    dsimp only [Add.add, HAdd.hAdd, Neg.neg, Int.add, Int.neg, Int.negOfNat]

end Axeyum.IntAlgebra
