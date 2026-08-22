import Init.Data.Int.DivMod.Lemmas

namespace Axeyum.Autogenesis

private theorem intNatAbsNegOfNatDirectV1 (n : Nat) :
    Int.natAbs (Int.negOfNat n) = n := by
  cases n <;> rfl

theorem intNatAbsMulDirectV1 (a b : Int) :
    (a * b).natAbs = a.natAbs * b.natAbs := by
  cases a <;> cases b
  · rfl
  · exact intNatAbsNegOfNatDirectV1 _
  · exact intNatAbsNegOfNatDirectV1 _
  · rfl

end Axeyum.Autogenesis
