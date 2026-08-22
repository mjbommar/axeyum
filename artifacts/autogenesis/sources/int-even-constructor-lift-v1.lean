import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem intDoubleModTwoZeroLiftV1
    (natDouble : ∀ n : Nat, (n + n) % 2 = 0)
    (succOne : ∀ {n : Nat}, n % 2 = 0 → (n + 1) % 2 = 1) :
    ∀ m : Int, (m + m) % 2 = 0
  | .ofNat n => congrArg Int.ofNat (natDouble n)
  | .negSucc n => by
      change Int.subNatNat 2 (Nat.succ (Nat.succ (n + n) % 2)) = 0
      rw [succOne (natDouble n)]
      rfl

theorem intNegNatDoubleV2 : ∀ q : Nat,
    -((q : Int) + (q : Int)) = -(q : Int) + -(q : Int)
  | 0 => rfl
  | q + 1 => by
      change Int.negSucc (Nat.succ q + q) = Int.negSucc (Nat.succ (q + q))
      exact congrArg Int.negSucc (Nat.succ_add q q)

theorem intHalfWitnessOfModTwoZeroLiftV1
    (natHalf : ∀ n : Nat, n % 2 = 0 → ∃ q : Nat, n = q + q)
    (modCases : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1)
    (succZero : ∀ {n : Nat}, n % 2 = 1 → (n + 1) % 2 = 0) :
    ∀ z : Int, z % 2 = 0 → ∃ m : Int, z = m + m
  | .ofNat n, h => by
      have hn : n % 2 = 0 := Int.ofNat.inj h
      obtain ⟨q, hq⟩ := natHalf n hn
      exact ⟨Int.ofNat q, congrArg Int.ofNat hq⟩
  | .negSucc n, h => by
      change Int.subNatNat 2 (Nat.succ (n % 2)) = 0 at h
      have hn : n % 2 = 1 := by
        cases modCases n with
        | inl hz =>
            rw [hz] at h
            cases h
        | inr ho => exact ho
      obtain ⟨q, hq⟩ := natHalf (n + 1) (succZero hn)
      refine ⟨-(q : Int), ?_⟩
      calc
        Int.negSucc n = -((n + 1 : Nat) : Int) := rfl
        _ = -((q + q : Nat) : Int) :=
          congrArg (fun x : Nat => -(x : Int)) hq
        _ = -((q : Int) + (q : Int)) :=
          congrArg (fun x : Int => -x) (Int.natCast_add q q)
        _ = -(q : Int) + -(q : Int) := intNegNatDoubleV2 q

end Axeyum.Autogenesis
