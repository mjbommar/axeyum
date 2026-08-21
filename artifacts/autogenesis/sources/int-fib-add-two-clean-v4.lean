import Mathlib.Data.Nat.Fib.Basic

namespace Int

@[pp_nodot]
def fib : Int → Int
  | ofNat n => ofNat (Nat.fib n)
  | negSucc k =>
      let n := k + 1
      if n % 2 = 0 then -ofNat (Nat.fib n) else ofNat (Nat.fib n)

@[simp]
theorem fib_natCast (n : Nat) : fib (n : Int) = (Nat.fib n : Int) := by
  rfl

theorem fib_add_two : ∀ n : Int, fib (n + 2) = fib n + fib (n + 1)
  | ofNat n => by
      simpa [fib] using congrArg Int.ofNat (Nat.fib_add_two (n := n))
  | negSucc k => by
      cases k with
      | zero => rfl
      | succ k =>
          cases k with
          | zero => rfl
          | succ k =>
              change
                fib (negSucc k) =
                  fib (negSucc (k + 2)) + fib (negSucc (k + 1))
              rcases Nat.mod_two_eq_zero_or_one (k + 1) with h | h
              · have h₁ : (k + 2) % 2 = 1 := by
                  simpa [Nat.add_assoc] using
                    Nat.succ_mod_two_eq_one_iff.mpr h
                have h₂ : (k + 3) % 2 = 0 := by
                  simpa [Nat.add_assoc] using
                    Nat.succ_mod_two_eq_zero_iff.mpr h₁
                simp [fib, h, h₁, h₂, Nat.fib_add_two] <;> abel
              · have h₁ : (k + 2) % 2 = 0 := by
                  simpa [Nat.add_assoc] using
                    Nat.succ_mod_two_eq_zero_iff.mpr h
                have h₂ : (k + 3) % 2 = 1 := by
                  simpa [Nat.add_assoc] using
                    Nat.succ_mod_two_eq_one_iff.mpr h₁
                simp [fib, h, h₁, h₂, Nat.fib_add_two] <;> abel

end Int
