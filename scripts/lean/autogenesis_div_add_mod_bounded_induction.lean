import Init.Data.Nat.Div.Basic

namespace Axeyum.Autogenesis

theorem divAddModBoundedInduction (m n : Nat) :
    n * (m / n) + m % n = m := by
  have haddzero : ∀ x : Nat, x + 0 = x := by
    intro x
    induction x with
    | zero => rfl
    | succ x ih => exact congrArg Nat.succ ih
  have hmulzero : ∀ x : Nat, x * 0 = 0 := by
    intro x
    induction x with
    | zero => rfl
    | succ x ih => exact ih
  have hrestore : ∀ x y : Nat, y ≤ x → x - y + y = x := by
    intro x
    induction x with
    | zero =>
        intro y h
        cases y with
        | zero => rfl
        | succ y => exact (Nat.not_succ_le_zero y h).elim
    | succ x ih =>
        intro y h
        cases y with
        | zero => exact haddzero (Nat.succ x)
        | succ y =>
            rw [Nat.succ_sub_succ_eq_sub, ← Nat.add_assoc,
              ih y (Nat.le_of_succ_le_succ h)]
  have hall : ∀ bound k : Nat, k ≤ bound → ∀ divisor : Nat,
      divisor * (k / divisor) + k % divisor = k := by
    intro bound
    induction bound with
    | zero =>
        intro k hk divisor
        cases k with
        | zero =>
            rw [Nat.div_eq, Nat.mod_eq]
            split
            next h =>
              cases divisor with
              | zero => exact (Nat.not_succ_le_zero 0 h.1).elim
              | succ divisor =>
                  exact (Nat.not_succ_le_zero divisor h.2).elim
            next _ =>
              exact congrArg (fun x => x + 0) (hmulzero divisor)
        | succ k => exact (Nat.not_succ_le_zero k hk).elim
    | succ bound ih =>
        intro k hk divisor
        cases Nat.le_or_eq_of_le_succ hk with
        | inl hprevious => exact ih k hprevious divisor
        | inr hcurrent =>
            subst k
            rw [Nat.div_eq, Nat.mod_eq]
            split
            next h =>
              have hdecrease : Nat.succ bound - divisor < Nat.succ bound :=
                Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
              have hprevious : Nat.succ bound - divisor ≤ bound :=
                Nat.le_of_lt_succ hdecrease
              calc
                divisor * ((Nat.succ bound - divisor) / divisor + 1) +
                      (Nat.succ bound - divisor) % divisor =
                    (divisor * ((Nat.succ bound - divisor) / divisor) +
                      (Nat.succ bound - divisor) % divisor) + divisor := by
                        rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
                          Nat.add_comm divisor
                            ((Nat.succ bound - divisor) % divisor),
                          ← Nat.add_assoc]
                _ = (Nat.succ bound - divisor) + divisor := by
                      rw [ih (Nat.succ bound - divisor) hprevious divisor]
                _ = Nat.succ bound := hrestore (Nat.succ bound) divisor h.2
            next _ =>
              calc
                divisor * 0 + Nat.succ bound = 0 + Nat.succ bound :=
                  congrArg (fun x => x + Nat.succ bound) (hmulzero divisor)
                _ = Nat.succ bound + 0 := Nat.add_comm 0 (Nat.succ bound)
                _ = Nat.succ bound := haddzero (Nat.succ bound)
  exact hall m m (Nat.le_refl m) n

end Axeyum.Autogenesis
