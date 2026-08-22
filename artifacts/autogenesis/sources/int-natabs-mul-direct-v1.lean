import Init.Data.Int.DivMod.Lemmas

namespace Axeyum.Autogenesis

theorem intNatAbsMulDirectV1 (a b : Int) :
    (a * b).natAbs = a.natAbs * b.natAbs := by
  cases a <;> cases b <;> rfl

end Axeyum.Autogenesis
