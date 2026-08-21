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
              rcases Nat.mod_two_eq_zero_or_one (k + 1) with h | h <;>
                simp [fib, Nat.fib_add_two, Nat.add_mod, h, Nat.succ_eq_add_one]

end Int
