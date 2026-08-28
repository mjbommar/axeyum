import Mathlib.Data.Nat.ModEq

/-!
Proof-free statement adapters for the ten still-`open`
`natural-modular-equivalence` propositions this lane targets.

`Nat.ModEq n a b` is a transparent, non-recursive `def` unfolding to
`a % n = b % n` (`Mathlib/Data/Nat/ModEq.lean`), so each definition below is
exactly the corresponding Mathlib statement with no proof value attached.

Each proposition is the value of a transparent `Prop` definition. This file
contains no axiom, theorem, opaque declaration, or proof value. The candidate
proofs live in
`scripts/lean/autogenesis_nat_modeq_congruence_contract_v1.lean` and are
transported into an independently proof-isolated import of these statements
by `crates/axeyum-lean-import/examples/imported_candidate_transport_probe.rs`.

The eleventh open sibling, `Nat.ModEq.gcd_eq`, is deliberately absent: see
the lane status note — `Nat.gcd.eq_def` carries `Quot.sound` in this
environment, so no candidate for it can meet the empty-axiom-footprint bar
this route requires.
-/

namespace Axeyum.Autogenesis.Statement.NatModEqCongruence

def modModEq : Prop :=
  ∀ (a n : ℕ), a % n ≡ a [MOD n]

def modEqOne : Prop :=
  ∀ {a b : ℕ}, a ≡ b [MOD 1]

def addLeft : Prop :=
  ∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c + a ≡ c + b [MOD n]

def addRight : Prop :=
  ∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a + c ≡ b + c [MOD n]

def addLeftCancel : Prop :=
  ∀ {n a b : ℕ} (c : ℕ), c + a ≡ c + b [MOD n] → a ≡ b [MOD n]

def addRightCancel : Prop :=
  ∀ {n a b : ℕ} (c : ℕ), a + c ≡ b + c [MOD n] → a ≡ b [MOD n]

def ofDvd : Prop :=
  ∀ {m n a b : ℕ}, m ∣ n → a ≡ b [MOD n] → a ≡ b [MOD m]

def ofMulLeft : Prop :=
  ∀ {n a b : ℕ} (m : ℕ), a ≡ b [MOD m * n] → a ≡ b [MOD n]

def ofMulRight : Prop :=
  ∀ {n a b : ℕ} (m : ℕ), a ≡ b [MOD n * m] → a ≡ b [MOD n]

def dvdIff : Prop :=
  ∀ {m a b d : ℕ}, a ≡ b [MOD m] → d ∣ m → (d ∣ a ↔ d ∣ b)

end Axeyum.Autogenesis.Statement.NatModEqCongruence
