import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intNegOnePowRawV1 (k : Nat) :
    (-1 : Int) ^ k = if k % 2 = 0 then 1 else -1 := rfl

end Axeyum.Autogenesis
