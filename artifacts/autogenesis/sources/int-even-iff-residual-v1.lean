import Mathlib.Algebra.Group.Int.Even

namespace Axeyum.Autogenesis

theorem intEvenIffResidualV1
    (forward : ∀ n : Int, Even n → n % 2 = 0)
    (backward : ∀ n : Int, n % 2 = 0 → Even n) :
    ∀ n : Int, Even n ↔ n % 2 = 0 := by
  intro n
  exact ⟨forward n, backward n⟩

end Axeyum.Autogenesis
