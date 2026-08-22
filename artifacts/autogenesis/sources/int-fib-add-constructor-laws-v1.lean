import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intConstructorSplitV1 (z : Int) :
    (∃ n : Nat, z = Int.ofNat n) ∨ ∃ n : Nat, z = Int.negSucc n := by
  cases z with
  | ofNat n => exact Or.inl ⟨n, rfl⟩
  | negSucc n => exact Or.inr ⟨n, rfl⟩

theorem intOfNatZeroV1 : Int.ofNat 0 = 0 := rfl

theorem intOfNatSuccV1 (n : Nat) : Int.ofNat (n + 1) = Int.ofNat n + 1 := rfl

theorem intNegSuccZeroV1 : Int.negSucc 0 = 0 - 1 := rfl

theorem intNegSuccSuccV1 (n : Nat) : Int.negSucc (n + 1) = Int.negSucc n - 1 := rfl

end Axeyum.Autogenesis
