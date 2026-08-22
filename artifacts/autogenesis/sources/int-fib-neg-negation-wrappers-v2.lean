import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegAddV2 (a b : Int) : -(a + b) = -a + -b :=
  Int.neg_add

theorem intNegNegV2 (x : Int) : -(-x) = x :=
  Int.neg_neg x

end Axeyum.Autogenesis
