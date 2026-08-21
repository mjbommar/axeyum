import Init.Data.Nat.Gcd

namespace Axeyum.Autogenesis

-- Deliberately use only constructor case analysis and definitional reduction.
-- The preregistered boundary forbids every public/private gcd equation theorem,
-- WellFounded.Nat.fix_eq, simplification, and proof search.
theorem gcdDefDirect (x y : Nat) :
    x.gcd y = if x = 0 then y else (y % x).gcd x := by
  cases x with
  | zero => rfl
  | succ predecessor => rfl

end Axeyum.Autogenesis
