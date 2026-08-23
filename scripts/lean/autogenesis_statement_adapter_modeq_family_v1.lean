import Mathlib.Data.Int.ModEq

/-!
Proof-free statement adapters for four members of the `integer-modular-
equivalence` family (`artifacts/facts/F-ml430-int-modeq-{refl,symm,trans}-*`
and `F-ml430-int-modeq-comm-1e4bcc07.json`), used to build fresh,
proof-isolated kernel goals for the `int_modeq_support` producer
(`crates/axeyum-lean-import/examples/int_modeq_support/mod.rs`).

`Int.ModEq n a b` is a transparent, non-recursive `def` unfolding to
`a % n = b % n` (`Mathlib/Data/Int/ModEq.lean`). The four propositions below
are exactly the equivalence-relation laws over that definition:
`Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans`, and `Int.modEq_comm`.

Each proposition below is the value of a transparent `Prop` definition. This
file contains no axiom, theorem, opaque declaration, or proof value.
-/

namespace Axeyum.Autogenesis.Statement.IntModEqFamily

def intModEqRefl : Prop :=
  ∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]

def intModEqSymm : Prop :=
  ∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]

def intModEqTrans : Prop :=
  ∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n]

def intModEqComm : Prop :=
  ∀ {n a b : ℤ}, a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]

end Axeyum.Autogenesis.Statement.IntModEqFamily
