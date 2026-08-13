# Lean Nat finite-range sum R4.6 result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.6;
[ADR-0391](../research/09-decisions/adr-0391-generic-nat-finite-range-sums.md).

## Result

`Nat.sumRange` is a shared zero-axiom definition for the half-open finite range
`[0,n)`. Its empty and successor equations are kernel-checked theorems backed
by definitional reduction. The empty `k=3` inner sum in `thm:sharp` can now be
represented as `sumRange f 0`, which computes to zero without a side condition.

The focused Nat suite checks six definitions and 27 theorems, evaluates the
empty range and `sumRange identity 4 = 6`, rejects a false value, and includes
an eleventh declaration-level mutation control for a wrong successor-equation
target. The exact package remains deterministic and axiom-free.

Local validation passed all 207 kernel library tests, every kernel integration
suite and doctest, strict Clippy/rustdoc, the 65-row classified axiom ledger and
its eight controls, plan/link/parity checks, formatting, and diff integrity.
Publication and hosted CI remain separate state.

## Boundary

This is the finite-sum foundation, not completion of R4.6 or theorem credit.
Range reindexing/splitting, sum algebra, and the paper's geometric factorization
remain open and must receive separate checked proofs and negative controls.
