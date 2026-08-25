import Mathlib.Data.Nat.Factorial.Basic

/-!
A proof-free adapter probe for the frozen train fact
`F:ml430-nat-factorial-pos-f1dd2405`.

The proposition is the value of a transparent `Prop` definition. It is not an
axiom, theorem, or opaque declaration, so exporting this declaration cannot
make the proposition available as a proof assumption.

Built to test whether `Nat.factorial_succ` (checked axiom-free in this
kernel's own `nat_prelude`) can be composed via `axeyum_lean_import::
compose_checked_theorem_slice` (ADR-0523) into the isolated kernel this
adapter's own export produces, as a premise for `bounded_induction.rs`'s
stuck goals. It cannot: `Kernel::add_declaration` rejects the reconstructed
`Nat.factorial_succ` with `DeclarationValueMismatch` because
`AxNat.factorial (AxNat.succ x0)` does not WHNF-reduce, in THIS kernel against
Mathlib's `brecOn`-compiled `Nat.factorial`, to `AxNat.mul (AxNat.factorial
x0) (AxNat.succ x0)` -- the same course-of-values opacity
`docs/autogenesis/262-curriculum-directed-frontier-selection.md`'s fourth
amendment diagnosed for `bounded_induction.rs`'s own WHNF-then-app-spine
search, now confirmed via an independent code path. See that document's fifth
amendment for the full measurement.
-/

namespace Axeyum.Autogenesis.Statement

def natFactorialPos : Prop :=
  ∀ (n : ℕ), 0 < n.factorial

end Axeyum.Autogenesis.Statement
