# ADR-0531: Admit Capell cubic towers as partial Lemire families

Status: accepted
Date: 2026-08-20

## Context

Odd monomial substitution preserves Lemire's half-degree coefficient window.
Capell's theorem can also preserve irreducibility, so the construction must be
audited against the committed degree-1-through-400 witnesses before it is
either promoted as an all-degree route or discarded with the generic
Q-transform recurrence.

## Decision

Expose a bounded `monomial_compose` operation and a theorem-specific
`cubic_composition_criterion`.  Admit every criterion-positive checked seed as
an infinite family `d*3^k`, while explicitly rejecting the union of these
families as a proof for arbitrary degree.

For an irreducible source `f` of even degree `d`, the criterion computes in
`GF(2)[x]/(f)` whether

```text
x^((2^d-1)/3) != 1.
```

This is exactly the noncube condition for a root of `f`; Capell's theorem then
proves `f(x^3)` irreducible.  Odd source degrees are rejected structurally
because cubing permutes `GF(2^d)`.

## Evidence

Focused tests cover a positive cyclotomic tower, a second unrelated positive
seed, a cube obstruction, and the odd-degree permutation obstruction.  Every
positive output is independently Rabin-certified.

The standalone `axeyum-gf2-capell-audit` replays both checkers on all 400
committed sources.  For every positive criterion it produces a fresh
composition certificate and checks it with both the bit-packed and independent
dense implementations.  The exact result is 138 positive seeds, 200 odd
sources, and 62 cube sources.  The positives occupy 95 3-free rays, of which
83 begin at the 3-free base and 12 begin at a later power of three.

The infinite iteration is algebraic.  If `beta^3=alpha`, its order gains one
factor of three; LTE gives the same one-factor increase from `2^d-1` to
`2^(3d)-1`.  Hence the noncube criterion renews at every step, while exponent
scaling preserves the half-degree window.

## Alternatives

Treating a successful first composition as evidence for all iterations was
rejected; the 3-primary order argument is required.  Treating the 138 seeds as
all-degree coverage was rejected because all odd degrees and infinitely many
even 3-free bases remain outside their union.

## Consequences

Axeyum now carries theorem-backed infinite Lemire families rather than only a
finite witness table.  They are useful constructive results and regression
controls, but they do not weaken or replace the connected Hayes/Carlitz
endpoint obligation needed for a complete proof.
