import Init.Prelude

namespace Axeyum.Autogenesis

theorem intNatAbsEqZeroV1 (z : Int) : z.natAbs = 0 ↔ z = 0 := by
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ n =>
          constructor
          · intro h
            nomatch h
          · intro h
            nomatch h
  | negSucc n =>
      constructor
      · intro h
        nomatch h
      · intro h
        nomatch h

theorem intFibEqZeroResidualV1
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (fibNatAbs : ∀ z : Int, (fibFn z).natAbs = natFib z.natAbs)
    (natFibZero : ∀ {n : Nat}, natFib n = 0 ↔ n = 0)
    (natAbsZero : ∀ z : Int, z.natAbs = 0 ↔ z = 0) :
    ∀ {z : Int}, fibFn z = 0 ↔ z = 0 := by
  intro z
  constructor
  · intro h
    have hfabs : (fibFn z).natAbs = 0 := (natAbsZero (fibFn z)).mpr h
    have hnatFib : natFib z.natAbs = 0 := by
      rw [← fibNatAbs z]
      exact hfabs
    have hnabs : z.natAbs = 0 := natFibZero.mp hnatFib
    exact (natAbsZero z).mp hnabs
  · intro h
    have hnabs : z.natAbs = 0 := (natAbsZero z).mpr h
    have hnatFib : natFib z.natAbs = 0 := natFibZero.mpr hnabs
    have hfabs : (fibFn z).natAbs = 0 := by
      rw [fibNatAbs z]
      exact hnatFib
    exact (natAbsZero (fibFn z)).mp hfabs

end Axeyum.Autogenesis
