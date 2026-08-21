import Init.Data.Nat.Div.Basic

namespace Axeyum.Autogenesis

theorem divAddModPublicRecursion (m n : Nat) :
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
  rw [Nat.div_eq, Nat.mod_eq]
  split
  next h =>
    have hdecrease : m - n < m :=
      Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    calc
      n * ((m - n) / n + 1) + (m - n) % n =
          (n * ((m - n) / n) + (m - n) % n) + n := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
              Nat.add_comm n ((m - n) % n), ← Nat.add_assoc]
      _ = (m - n) + n := by
            rw [divAddModPublicRecursion (m - n) n]
      _ = m := hrestore m n h.2
  next _ =>
    calc
      n * 0 + m = 0 + m := congrArg (fun x => x + m) (hmulzero n)
      _ = m + 0 := Nat.add_comm 0 m
      _ = m := haddzero m
termination_by m
decreasing_by
  assumption

end Axeyum.Autogenesis
