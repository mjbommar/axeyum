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

end Int
