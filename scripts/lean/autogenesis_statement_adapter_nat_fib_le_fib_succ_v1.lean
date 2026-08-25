import Mathlib.Data.Nat.Fib.Basic

/-!
A proof-free adapter probe for the frozen train fact
`F:ml430-nat-fib-le-fib-succ-d1ef4a3d`.

The proposition is the value of a transparent `Prop` definition. It is not an
axiom, theorem, or opaque declaration, so exporting this declaration cannot
make the proposition available as a proof assumption.

Built to test whether `Nat.fib_add_two` -- already a PROVED ledger fact,
`F:ml430-nat-fib-add-two-b86e0c82`, and also checked axiom-free in this
kernel's own `nat_prelude` -- can be composed via
`axeyum_lean_import::compose_checked_theorem_slice` (ADR-0523) into the
isolated kernel this adapter's own export produces, as a premise for an
order-shaped sibling goal `bounded_induction.rs`'s `close_order_terminal`
cannot reach alone. It cannot, for a different reason than the factorial
probe: `Kernel::add_declaration` rejects the reconstructed `Nat.fib_add_two`
with `DeclarationValueMismatch` because `nat_prelude`'s own `Nat.fib` is
built over its internal `AxNat.fibAux` accumulator helper, which has no
Mathlib-imported counterpart to reuse against Mathlib's `Nat.iterate`-based
`Nat.fib` -- a representational mismatch, not the `brecOn` opacity the
factorial probe hit. See
`docs/autogenesis/262-curriculum-directed-frontier-selection.md`'s fifth
amendment for the full measurement.
-/

namespace Axeyum.Autogenesis.Statement

def natFibLeFibSucc : Prop :=
  ∀ {n : ℕ}, Nat.fib n ≤ Nat.fib (n + 1)

end Axeyum.Autogenesis.Statement
