import Mathlib.Data.Int.GCD

namespace Axeyum.Autogenesis

theorem dvdAddCancelAllNatAdapterV1
    (positiveCancel : ∀ d excess b : Nat,
      1 ≤ d → d ∣ excess → d ∣ excess + b → d ∣ b)
    (d excess b : Nat)
    (dividesExcess : d ∣ excess)
    (dividesSum : d ∣ excess + b) :
    d ∣ b := by
  cases d with
  | zero =>
      rcases dividesExcess with ⟨leftFactor, leftEquation⟩
      rcases dividesSum with ⟨sumFactor, sumEquation⟩
      have excessZero : excess = 0 :=
        leftEquation.trans (Nat.zero_mul leftFactor)
      have sumZero : excess + b = 0 :=
        sumEquation.trans (Nat.zero_mul sumFactor)
      have bZero : b = 0 := by
        calc
          b = 0 + b := (Nat.zero_add b).symm
          _ = excess + b :=
            congrArg (fun value => value + b) excessZero.symm
          _ = 0 := sumZero
      have zeroDividesZero : 0 ∣ 0 := ⟨0, rfl⟩
      exact
        Eq.mp
          (congrArg (fun value => 0 ∣ value) bZero).symm
          zeroDividesZero
  | succ predecessor =>
      have positive : 1 ≤ Nat.succ predecessor :=
        Nat.succ_le_succ (Nat.zero_le predecessor)
      exact
        positiveCancel (Nat.succ predecessor) excess b positive
          dividesExcess dividesSum

end Axeyum.Autogenesis
