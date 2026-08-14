# ADR-0393: Checked geometric-sum reindexing

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1.

## Context

The proof of `thm:sharp` in `../axeyum-rado-paper` factors

`u = a * [1 + 2 * (a + ... + a^(k-3)) + a^(k-2)]`.

The inner shifted power sum is empty at `k = 3`. ADR-0391 supplied a generic
half-open `Nat.sumRange` with that empty semantics, but did not prove the
reindexing that turns multiplication of powers indexed from zero into powers
indexed from one. The older `rado_shell_arithmetic` test has a test-local
`geo_shift` theorem over specialized recurrences; it is evidence of feasibility,
not reusable library surface.

## Decision

Add the zero-axiom checked theorem

`Nat.mul_sumRange_pow : forall a n,
  a * sumRange (fun i => a^i) n =
  sumRange (fun i => a^(succ i)) n`.

Prove it by induction on `n`. The base is the empty sum. The successor step
uses `left_distrib`, the induction hypothesis, `mul_comm`, and `pow_succ`.
Keep the theorem generic in both the base and range length; do not encode the
paper's `k-3` expression or its surrounding factorization in the prelude.

## Evidence

The focused Nat suite checks the theorem's admitted declaration, applies it at
the empty range used by `k = 3`, and applies it at `a = 3, n = 4`. A mutation
control feeds the valid proof for range two to the inferred proposition for
range three and requires trusted-gate rejection without insertion. Package
determinism and the zero-axiom environment walk remain enforced.

## Alternatives

Promoting the test-local `geo`/`geo1` recurrences was rejected because it would
make general finite-sum algebra depend on Rado-specific duplicate definitions.
A paper-shaped theorem over `k-3` was rejected because subtraction is not yet
available and would hide the empty-range obligation behind unrelated machinery.

## Consequences

The geometric reindexing dependency named by R7.1 is now a reusable checked
library theorem. Completing `thm:sharp` still needs finite-sum congruence and
scalar/additive algebra for the full factorization, truncated subtraction for
its witness, order/range arguments, and the explicitly bounded colour proof.
No paper theorem is credited by this increment.
