import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegAddV1 (a b : Int) : -(a + b) = -a + -b :=
  SubtractionMonoid.neg_add_rev a b

theorem intNegNegV1 (x : Int) : -(-x) = x :=
  neg_neg x

end Axeyum.Autogenesis
