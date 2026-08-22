import Mathlib.Algebra.Group.Int.Even

namespace Axeyum.Autogenesis

theorem intEvenToModTwoZeroResidualV2
    (doubleModZero : ∀ m : Int, (m + m) % 2 = 0) :
    ∀ n : Int, Even n → n % 2 = 0 := by
  intro n heven
  obtain ⟨m, rfl⟩ := heven
  exact doubleModZero m

theorem intModTwoZeroToEvenResidualV2
    (halfWitness : ∀ n : Int, n % 2 = 0 → ∃ m : Int, n = m + m) :
    ∀ n : Int, n % 2 = 0 → Even n := by
  intro n hzero
  exact halfWitness n hzero

end Axeyum.Autogenesis
