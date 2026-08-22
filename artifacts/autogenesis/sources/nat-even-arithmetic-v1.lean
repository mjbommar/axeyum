import Mathlib.Data.Int.Basic

namespace Axeyum.Autogenesis

theorem natDoubleSuccShape (q : Nat) :
    (q + 1) + (q + 1) = (q + q) + 2 := by
  calc
    (q + 1) + (q + 1) = ((q + 1) + q) + 1 := rfl
    _ = ((q + q) + 1) + 1 :=
      congrArg (fun x => x + 1) (Nat.succ_add q q)
    _ = (q + q) + 2 := rfl

theorem natDoubleModTwoZeroV1
    (modStepTwo : ∀ k : Nat, (k + 2) % 2 = k % 2) :
    ∀ q : Nat, (q + q) % 2 = 0
  | 0 => rfl
  | q + 1 => by
      calc
        ((q + 1) + (q + 1)) % 2 = ((q + q) + 2) % 2 :=
          congrArg (fun x => x % 2) (natDoubleSuccShape q)
        _ = (q + q) % 2 := modStepTwo (q + q)
        _ = 0 := natDoubleModTwoZeroV1 modStepTwo q

theorem natHalfWitnessOfModTwoZeroV1
    (modStepTwo : ∀ k : Nat, (k + 2) % 2 = k % 2) :
    ∀ n : Nat, n % 2 = 0 → ∃ q : Nat, n = q + q
  | 0, _ => ⟨0, rfl⟩
  | 1, h => by cases h
  | n + 2, h => by
      have hn : n % 2 = 0 := (modStepTwo n).symm.trans h
      obtain ⟨q, hq⟩ := natHalfWitnessOfModTwoZeroV1 modStepTwo n hn
      refine ⟨q + 1, ?_⟩
      exact (congrArg (fun x => x + 2) hq).trans (natDoubleSuccShape q).symm

end Axeyum.Autogenesis
