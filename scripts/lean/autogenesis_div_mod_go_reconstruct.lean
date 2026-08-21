import Init.Data.Nat.Div.Basic

namespace Axeyum.Autogenesis

theorem divModGoReconstruct
    (y : Nat) (hy : 0 < y) (fuel : Nat) :
    ∀ (x : Nat) (hfuel : x < fuel),
      y * Nat.div.go y hy fuel x hfuel +
          Nat.modCore.go y hy fuel x hfuel =
        x := by
  induction fuel with
  | zero =>
      intro x hfuel
      exact (Nat.not_lt_zero x hfuel).elim
  | succ fuel ih =>
      intro x hfuel
      rw [Nat.div.go.eq_1, Nat.modCore.go.eq_1]
      split
      next h =>
        let hsub : x - y < fuel := Nat.div_rec_fuel_lemma hy h hfuel
        calc
          y * (Nat.div.go y hy fuel (x - y) hsub + 1) +
                Nat.modCore.go y hy fuel (x - y) hsub =
              (y * Nat.div.go y hy fuel (x - y) hsub +
                  Nat.modCore.go y hy fuel (x - y) hsub) + y := by
                    rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
                      Nat.add_comm y (Nat.modCore.go y hy fuel (x - y) hsub),
                      ← Nat.add_assoc]
          _ = (x - y) + y := by
                rw [ih (x - y) hsub]
          _ = x := Nat.sub_add_cancel h
      next _ =>
        have hmulzero : ∀ n : Nat, n * 0 = 0 := by
          intro n
          induction n with
          | zero => rfl
          | succ n ihzero => exact ihzero
        have haddzero : ∀ n : Nat, n + 0 = n := by
          intro n
          induction n with
          | zero => rfl
          | succ n ihzero => exact congrArg Nat.succ ihzero
        calc
          y * 0 + x = 0 + x := congrArg (fun n => n + x) (hmulzero y)
          _ = x + 0 := Nat.add_comm 0 x
          _ = x := haddzero x

end Axeyum.Autogenesis
