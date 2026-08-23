import Mathlib.Data.Nat.ModEq

/-!
Proof-free statement adapters for the blind development-set generalization
probe of the `int_modeq_support` producer
(`crates/axeyum-lean-import/examples/int_modeq_support/mod.rs`), tuned only
against `integer-modular-equivalence` (train). This file adapts the four
sibling propositions in `natural-modular-equivalence` (development):
`Nat.ModEq.refl`, `Nat.ModEq.symm`, `Nat.ModEq.trans`, `Nat.ModEq.comm`.

`Nat.ModEq n a b` is a transparent, non-recursive `def` unfolding to
`a % n = b % n` (`Mathlib/Data/Nat/ModEq.lean`), the same shape as
`Int.ModEq`.

Each proposition below is the value of a transparent `Prop` definition. This
file contains no axiom, theorem, opaque declaration, or proof value.
-/

namespace Axeyum.Autogenesis.Statement.NatModEqFamily

def natModEqRefl : Prop :=
  ∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]

def natModEqSymm : Prop :=
  ∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]

def natModEqTrans : Prop :=
  ∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n]

def natModEqComm : Prop :=
  ∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]

end Axeyum.Autogenesis.Statement.NatModEqFamily
