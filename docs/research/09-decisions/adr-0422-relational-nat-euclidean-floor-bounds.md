# ADR-0422: Relational Nat Euclidean floor bounds

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

Constructive existence and uniqueness make `divMod` well-defined, but clients
should not have to reopen its conjunction to recover the defining floor
interval. Rounding proofs, bounded iteration, and chunking algorithms all need
the same two inequalities.

The Rado shell-gap proof exposed this boundary: its problem-specific algebra
starts only after converting an integral multiplicative bound into an order on
the quotient. The reusable library should provide that conversion without
mentioning the shell construction.

## Decision

Add the zero-axiom theorem

```text
div_mod_bounds : divMod d n q r -> d*q <= n and n < d*(succ q)
```

Derive the lower bound from `d*q <= d*q+r` and the relation equation. Derive
the strict upper bound from `r<d`, strict additive monotonicity, and the
definitional equality `d*q+d = d*(succ q)`.

Keep division relational. Do not add executable `/`, `%`, host arithmetic, or
a Rado-specific rounded expression.

## Evidence

The concrete decomposition `5 = 2*2+1` exercises both bounds. NC41 changes
only the strict upper endpoint and the trusted declaration gate rejects it
without insertion. All 19 focused Nat tests pass, the deterministic census is
79 definitions/theorems, and the prelude declares zero axioms.

## Consequences

Every checked decomposition now carries the canonical half-open floor
interval. The next reusable layer is the positive-divisor equivalence between
`d*s <= n` and `s <= q`; that is the direct integrality/rounding bridge and is
also useful outside the motivating paper.
