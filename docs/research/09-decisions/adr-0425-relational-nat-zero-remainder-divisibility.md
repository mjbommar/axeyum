# ADR-0425: Relational Nat zero remainder characterizes divisibility

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.3 / R4.7.

## Context

The Nat prelude had independent relational interfaces for Euclidean division
and divisibility. Exact-division consumers need a checked bridge between them;
otherwise each proof must manually reconcile a quotient/remainder witness with
an existential factorization.

The Rado development repeatedly benefited from keeping divisibility
relational, especially for valuation proofs. The same design should extend to
division instead of adding executable `%` tests or host arithmetic.

## Decision

Add the zero-axiom theorem

```text
div_mod_remainder_eq_zero_iff_dvd :
  divMod d n q r -> (r=0 iff dvd d n)
```

For `r=0`, rewrite the reconstruction equation and introduce `q` as the
divisibility witness. Conversely, eliminate an arbitrary divisibility witness,
build its zero-remainder decomposition, and use `div_mod_unique` to identify
the supplied remainder with zero.

A separate positivity premise is unnecessary. The supplied decomposition's
`r<d` bound constructively yields `0<d`, which validates the zero-remainder
decomposition.

## Evidence

The exact decomposition `6 = 2*3+0` exercises the bridge. NC44 changes only
the divisor in the resulting `dvd` proposition and the trusted declaration
gate rejects it without insertion. All 19 focused Nat tests pass, the
deterministic census is 82 definitions/theorems, and the prelude declares zero
axioms.

## Consequences

Exact division is now expressed consistently across quotient/remainder and
divisibility APIs. A direct existence corollary can next turn `d ∣ n` into a
zero-remainder decomposition for algorithm and number-theory clients that do
not already carry a `divMod` witness.
