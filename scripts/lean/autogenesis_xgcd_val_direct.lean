import Mathlib.Data.Int.GCD

namespace Axeyum.Autogenesis

-- Deliberately use only definitional equality. The preregistered boundary
-- forbids both official projection theorems, simplification, and proof search.
theorem xgcdValDirect (x y : Nat) :
    x.xgcd y = (x.gcdA y, x.gcdB y) := by
  rfl

end Axeyum.Autogenesis
