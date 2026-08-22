import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intFibOfNonnegResidualV1
    (fibFn : Int → Int)
    (natFib : Nat → Nat)
    (positivePresentation : ∀ n : Nat,
      fibFn (Int.ofNat n) = Int.ofNat (natFib n)) :
    ∀ {n : Int}, 0 ≤ n → fibFn n = Int.ofNat (natFib n.toNat) := by
  intro n hn
  cases n with
  | ofNat k => exact positivePresentation k
  | negSucc k => nomatch hn

end Axeyum.Autogenesis
