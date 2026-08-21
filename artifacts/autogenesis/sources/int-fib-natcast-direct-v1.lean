import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intFibNatCastDirectV1 (n : Nat) :
    Int.fib (n : Int) = (Nat.fib n : Int) := by
  rfl

end Axeyum.Autogenesis
