import Mathlib.Data.Nat.Fib.Basic

namespace Int

@[pp_nodot]
def fib : Int → Int
  | ofNat n => ofNat (Nat.fib n)
  | negSucc k =>
      let n := k + 1
      if n % 2 = 0 then -ofNat (Nat.fib n) else ofNat (Nat.fib n)

theorem fib_neg_natCast_presentation : ∀ n : Nat,
    fib (-(n : Int)) =
      if n % 2 = 0 then -ofNat (Nat.fib n) else ofNat (Nat.fib n)
  | 0 => rfl
  | _ + 1 => rfl

end Int
