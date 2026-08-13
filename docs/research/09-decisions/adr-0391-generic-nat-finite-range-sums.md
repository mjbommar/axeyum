# ADR-0391: Generic Nat finite-range sums

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1.

## Context

The Rado capability test has specialized `geo` and `geo1` recurrences, but
they are not shared library surface and do not name the empty-range semantics
needed when `k = 3` in `thm:sharp`. A reusable mathematical foundation should
represent finite sums independently of this one paper before proving its
geometric reindexing identity.

## Decision

Add the zero-axiom definition
`Nat.sumRange f n = f 0 + ... + f (n-1)`, by `Nat.rec` on `n`, together with
checked definitional-equation theorems:

- `sumRange_zero : forall f, sumRange f 0 = 0`;
- `sumRange_succ : forall f n, sumRange f (succ n) = sumRange f n + f n`.

The function and theorem handles join the exact transactional Nat package.
Reindexing, splitting ranges, distributivity over sums, and the geometric
closed form are later theorem increments; this ADR does not imply them.

## Evidence

The focused suite checks that the empty sum reduces to zero and that summing
the identity function over four terms reduces to `0+1+2+3=6`, with a false
value control. A valid successor-equation proof relabelled as an equality to
zero must be rejected without environment insertion. Package determinism and
the zero-axiom walk remain enforced.

## Consequences

R4.6 remains **WIP**, but the empty-range semantic corner and generic recursive
surface now exist. The next Rado-specific step is a checked reindexing theorem
connecting `sumRange (fun i => a^(succ i)) n` to multiplication by `a`, after
which the exact `thm:sharp` factorization can be expressed without test-local
sum definitions.
