import Mathlib.Data.Nat.Factorial.Basic

/-!
Proof-free statement adapter for the one member of the bounded-induction
family that a prior adapter run does not already cover.

`bounded_induction_support` (`crates/axeyum-lean-import/examples/
bounded_induction_support/mod.rs`) is target-agnostic: `Eq.refl`, and where
that is stuck, a bounded structural induction over a discovered zero/succ
binder plus one congruence rewrite driven by the induction hypothesis.
Measured over the frozen `natural-factorial` train rows, it independently
kernel-checks (`axioms = 0`) three statements: this one (`descFactorial n 1 =
n`, which bare reflexivity cannot close), and two the reflexivity-only
producer had already closed (`ascFactorial n 0 = 1`, `descFactorial n 0 =
1`), whose adapters already exist as tracked, checked artifacts
(`scripts/lean/autogenesis_statement_adapter_factorial.lean` and
`scripts/lean/autogenesis_statement_adapter_factorial_zero_family.lean`).

This file contains no axiom, theorem, opaque declaration, or proof value.
-/

namespace Axeyum.Autogenesis.Statement.BoundedInductionFamily

def natDescFactorialOne : Prop :=
  ∀ (n : ℕ), n.descFactorial 1 = n

end Axeyum.Autogenesis.Statement.BoundedInductionFamily
