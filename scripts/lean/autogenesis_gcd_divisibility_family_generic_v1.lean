import Mathlib.Data.Int.GCD

namespace Axeyum.Autogenesis

/-- A dependency-explicit GCD divisibility family.  Division, cancellation,
and both public GCD equations are parameters so the exported proof can be
closed only with independently checked target-kernel leaves. -/
theorem gcdDivisibilityFamilyGenericV1
    (gcdZeroLeft : ∀ n : Nat, Nat.gcd 0 n = n)
    (gcdSucc : ∀ m n : Nat,
      Nat.gcd (Nat.succ m) n = Nat.gcd (Nat.mod n (Nat.succ m)) (Nat.succ m))
    (modQuotientWitness : ∀ m n : Nat, 0 < m →
      ∃ q : Nat, m * q + Nat.mod n m = n)
    (dvdRefl : ∀ n : Nat, n ∣ n)
    (dvdMulRight : ∀ d a b : Nat, d ∣ a → d ∣ a * b)
    (dvdAdd : ∀ d a b : Nat, d ∣ a → d ∣ b → d ∣ a + b)
    (dvdAddCancel : ∀ d a b : Nat, d ∣ a → d ∣ a + b → d ∣ b) :
    (∀ m n : Nat, Nat.gcd m n ∣ m ∧ Nat.gcd m n ∣ n) ∧
    (∀ d m n : Nat, d ∣ m → d ∣ n → d ∣ Nat.gcd m n) := by
  have gcdDividesPair : ∀ m n : Nat, Nat.gcd m n ∣ m ∧ Nat.gcd m n ∣ n := by
    intro m n
    refine Nat.gcd.induction m n ?_ ?_
    · intro n
      have atN : n ∣ 0 ∧ n ∣ n := ⟨⟨0, (Nat.mul_zero n).symm⟩, dvdRefl n⟩
      exact Eq.mp
        (congrArg (fun value => value ∣ 0 ∧ value ∣ n) (gcdZeroLeft n)).symm
        atN
    · intro m n hm ih
      cases m with
      | zero => exact (Nat.not_lt_zero 0 hm).elim
      | succ predecessor =>
          let divisor := Nat.succ predecessor
          let remainder := Nat.mod n divisor
          let common := Nat.gcd remainder divisor
          rcases modQuotientWitness divisor n hm with ⟨q, hq⟩
          have dividesProduct : common ∣ divisor * q :=
            dvdMulRight common divisor q ih.2
          have dividesSum : common ∣ divisor * q + remainder :=
            dvdAdd common (divisor * q) remainder dividesProduct ih.1
          have dividesN : common ∣ n :=
            Eq.mp (congrArg (fun value => common ∣ value) hq) dividesSum
          have atCommon : common ∣ divisor ∧ common ∣ n := ⟨ih.2, dividesN⟩
          exact Eq.mp
            (congrArg
              (fun value => value ∣ divisor ∧ value ∣ n)
              (gcdSucc predecessor n)).symm
            atCommon
  have dividesGcd : ∀ d m n : Nat, d ∣ m → d ∣ n → d ∣ Nat.gcd m n := by
    intro d m n
    refine Nat.gcd.induction m n ?_ ?_
    · intro n _ dividesN
      exact Eq.mp
        (congrArg (fun value => d ∣ value) (gcdZeroLeft n)).symm
        dividesN
    · intro m n hm ih dividesM dividesN
      cases m with
      | zero => exact (Nat.not_lt_zero 0 hm).elim
      | succ predecessor =>
          let divisor := Nat.succ predecessor
          let remainder := Nat.mod n divisor
          rcases modQuotientWitness divisor n hm with ⟨q, hq⟩
          have dividesProduct : d ∣ divisor * q :=
            dvdMulRight d divisor q dividesM
          have dividesSum : d ∣ divisor * q + remainder :=
            Eq.mp (congrArg (fun value => d ∣ value) hq).symm dividesN
          have dividesRemainder : d ∣ remainder :=
            dvdAddCancel d (divisor * q) remainder dividesProduct dividesSum
          have atRecursiveGcd : d ∣ Nat.gcd remainder divisor :=
            ih dividesRemainder dividesM
          exact Eq.mp
            (congrArg (fun value => d ∣ value) (gcdSucc predecessor n)).symm
            atRecursiveGcd
  exact ⟨gcdDividesPair, dividesGcd⟩

end Axeyum.Autogenesis
