import Init

/-!
Constructive target-side invariants for Lean's official `Nat.mod` implementation.

The final theorem abstracts over the divisibility predicate and the three
arithmetic lemmas it consumes. Those facts therefore remain explicit theorem
parameters when the proof is specialized inside Axeyum; they are not axioms of
this module. The proof follows the generated `Nat.modCore.go.eq_1` fuel equation
and the `Nat.mod.eq_2` successor equation directly instead of importing
`Nat.mod_add_div` or the official `Nat.dvd_mod_iff`, whose Lean 4.30 proof terms
reach `propext`.
-/

namespace Axeyum.Autogenesis

theorem modCoreGo_invariant
    (D : Nat → Prop)
    (y : Nat)
    (hy : 0 < y)
    (step : ∀ x, y ≤ x → (D (x - y) ↔ D x)) :
    ∀ fuel x (hfuel : x < fuel),
      D (Nat.modCore.go y hy fuel x hfuel) ↔ D x := by
  intro fuel
  induction fuel with
  | zero =>
      intro x hfuel
      exact False.elim (Nat.not_lt_zero x hfuel)
  | succ fuel ih =>
      intro x hfuel
      rw [Nat.modCore.go.eq_1]
      split
      next h => exact (ih _ _).trans (step x h)
      next => exact Iff.rfl

theorem modSucc_invariant
    (D : Nat → Prop)
    (d : Nat)
    (step : ∀ x, Nat.succ d ≤ x → (D (x - Nat.succ d) ↔ D x))
    (x : Nat) :
    D (Nat.mod x (Nat.succ d)) ↔ D x := by
  cases x with
  | zero => exact Iff.rfl
  | succ x =>
      rw [Nat.mod.eq_2]
      split
      next =>
        unfold Nat.modCore
        split
        next =>
          exact modCoreGo_invariant D (Nat.succ d) (Nat.zero_lt_succ d) step _ _ _
        next h => exact False.elim (h (Nat.zero_lt_succ d))
      next => exact Iff.rfl

theorem modSucc_dvd_iff
    (dvd : Nat → Nat → Prop)
    (dvd_add_iff_right :
      ∀ k m n, dvd k m → (dvd k n ↔ dvd k (Nat.add m n)))
    (sub_add_cancel :
      ∀ m n, Nat.le m n → Nat.add (Nat.sub n m) m = n)
    (add_comm : ∀ m n, Nat.add m n = Nat.add n m) :
    ∀ k d x, dvd k (Nat.succ d) →
      (dvd k (Nat.mod x (Nat.succ d)) ↔ dvd k x) := by
  intro k d x dividesDivisor
  apply modSucc_invariant (dvd k) d
  intro value divisorLeValue
  have addIff :=
    dvd_add_iff_right k (Nat.succ d) (Nat.sub value (Nat.succ d)) dividesDivisor
  have restore :
      Nat.add (Nat.succ d) (Nat.sub value (Nat.succ d)) = value :=
    (add_comm (Nat.succ d) (Nat.sub value (Nat.succ d))).trans
      (sub_add_cancel (Nat.succ d) value divisorLeValue)
  constructor
  · intro dividesDifference
    exact restore ▸ addIff.mp dividesDifference
  · intro dividesValue
    exact addIff.mpr (restore.symm ▸ dividesValue)

end Axeyum.Autogenesis
