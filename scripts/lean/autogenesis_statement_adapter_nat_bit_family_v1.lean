import Mathlib

namespace Axeyum.Autogenesis.Statement.NatBitFamily

def bitDivTwo : Prop :=
  ∀ (b : Bool) (n : ℕ), Nat.bit b n / 2 = n

def bitEqZeroIff : Prop :=
  ∀ {n : ℕ} {b : Bool}, Nat.bit b n = 0 ↔ n = 0 ∧ b = false

def bitFalse : Prop :=
  Nat.bit false = fun x => 2 * x

def bitFalseApply : Prop :=
  ∀ (n : ℕ), Nat.bit false n = 2 * n

def bitModTwoEqOneIff : Prop :=
  ∀ (a : Bool) (x : ℕ), Nat.bit a x % 2 = 1 ↔ a = true

def bitModTwoEqZeroIff : Prop :=
  ∀ (a : Bool) (x : ℕ), Nat.bit a x % 2 = 0 ↔ (!a) = true

def bitNeZeroIff : Prop :=
  ∀ {n : ℕ} {b : Bool}, Nat.bit b n ≠ 0 ↔ n = 0 → b = true

def bitTrue : Prop :=
  Nat.bit true = fun x => 2 * x + 1

def bitTrueApply : Prop :=
  ∀ (n : ℕ), Nat.bit true n = 2 * n + 1

def bitwiseZero : Prop :=
  ∀ {f : Bool → Bool → Bool}, Nat.bitwise f 0 0 = 0

end Axeyum.Autogenesis.Statement.NatBitFamily
