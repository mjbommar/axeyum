# ADR-0445: Reducible Nat strict-order well-foundedness

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.8 and Q2.

## Context

ADR-0441--0444 provide native accessibility, a generic checked fixpoint and
its equation, and generic predecessor elimination. Number-theoretic algorithms
still need a concrete decreasing relation. Pinned Lean 4.30 proves that Nat
strict order is well-founded by ordinary Nat induction and uses generic
`Acc.inv` for strict predecessors.

An opaque proof would establish the proposition but leave a closed
`WellFounded.fix` application stuck at that proof. This matters for algorithms,
not just proof presentation: a checked Euclidean program must compute through
the supplied well-foundedness witness. The Rado route-C experience likewise
argues for a reusable order boundary rather than algorithm-local termination
machinery.

## Decision

Add

```text
Nat.lt_well_founded : WellFounded Nat.lt
```

as a checked reducible definition with no axioms. Ordinary Nat induction builds
`Acc Nat.lt n`. The zero case eliminates the impossible `m < 0`. In the
successor case, `m < succ n` implies `m <= n`; `lt_or_eq_of_le` then separates:

- `m < n`, discharged by the generic `Acc.inv` applied to the induction
  hypothesis;
- `m = n`, discharged by symmetry and equality transport of the induction
  hypothesis.

Keep the definition reducible so the generic fixpoint can expose accessibility
constructors during kernel reduction. This follows the computational boundary
of pinned Lean's reducible Nat well-foundedness definition without importing
Lean's implementation as an axiom or trusted primitive.

## Evidence

The end-to-end control defines a closed countdown identity with generic
`WellFounded.fix`. Its successor branch calls the recursive function at the
immediate predecessor, so the test cannot pass by ignoring recursion. Applied
at two, the kernel infers Nat and definitionally reduces the result to two.
A mutation claiming that same expression equals one by reflexivity is rejected
with `DeclarationValueMismatch`.

The definition joins promised-name, deterministic-render, zero-axiom, strict
Clippy, and pinned Lean 4.30 replay gates. Its proof uses the already checked Nat
order spine and the general accessibility API rather than a private recursor.

## Consequences

The generic well-founded recursion stack now computes end to end over Nat
strict order. This settles the core termination route in Q2, but does not yet
provide executable quotient/remainder, gcd, Bezout, or Gauss results. The next
design boundary is a checked executable Euclidean-remainder operation whose
totality and equations reuse the existing relational division theory; gcd
should be built only after that boundary is explicit.
