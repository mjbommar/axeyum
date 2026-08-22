import Mathlib.Algebra.Group.Int.Even

namespace Axeyum.Autogenesis

theorem intEvenNegResidualV1
    (negAdd : ∀ a b : Int, -(a + b) = -a + -b)
    (negNeg : ∀ x : Int, -(-x) = x) :
    ∀ x : Int, Even (-x) ↔ Even x := by
  intro x
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨-r, ?_⟩
    calc
      x = -(-x) := (negNeg x).symm
      _ = -(r + r) := congrArg (fun value : Int => -value) hr
      _ = -r + -r := negAdd r r
  · rintro ⟨r, hr⟩
    refine ⟨-r, ?_⟩
    calc
      -x = -(r + r) := congrArg (fun value : Int => -value) hr
      _ = -r + -r := negAdd r r

theorem intEvenOfNatModTwoResidualV1
    (evenIff : ∀ z : Int, Even z ↔ z % 2 = 0) :
    ∀ n : Nat, Even (Int.ofNat n) ↔ n % 2 = 0 := by
  intro n
  constructor
  · intro heven
    exact Int.ofNat.inj ((evenIff (Int.ofNat n)).1 heven)
  · intro hmod
    exact (evenIff (Int.ofNat n)).2 (congrArg Int.ofNat hmod)

theorem intEvenNegOfNatModTwoResidualV1
    (evenNeg : ∀ x : Int, Even (-x) ↔ Even x)
    (evenPositive : ∀ n : Nat, Even (Int.ofNat n) ↔ n % 2 = 0) :
    ∀ n : Nat, Even (-(Int.ofNat n)) ↔ n % 2 = 0 := by
  intro n
  exact (evenNeg (Int.ofNat n)).trans (evenPositive n)

end Axeyum.Autogenesis
