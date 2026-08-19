# ADR-0491: Keep inverse-additive interval energy as a bounded CAS diagnostic

Status: accepted
Date: 2026-08-19
Index-summary: Add exact additive energy and Walsh fourth moments for inverted binary principal-unit intervals, distinct from multiplicative product energy

## Context

The exact Fourier bridge in ADR-0490 converts each endpoint convolution term
to Möbius-weighted inverse-additive phases.  The characteristic-free Hölder
core of bilinear Kloosterman arguments is controlled by the additive energy of
the inverse set.  Axeyum's existing principal-unit energy operations count
multiplicative collisions `ab=cd`; that is a different invariant and cannot be
substituted.

For the binary modulus `x^(ell+1)`, the invertible polynomials of degree less
than `d+1` are exactly

```text
V_d={1+a_1 x+...+a_d x^d}.
```

Thus the relevant energy counts additive quadruples in `V_d^(-1)`.

## Decision

Add `principal_unit_inverse_additive_energy` to
`axeyum-cas::gf2_hayes`.  Embed each inverse unit in the additive coefficient
group by dropping its constant coefficient, apply the checked integral Walsh
transform, and return

- the exact additive quadruple count;
- the unnormalized Walsh fourth moment;
- the maximum Walsh amplitude; and
- the exact correspondence `polynomial_degree_cutoff=d+1`.

Require the fourth moment to be divisible by `2^ell` and define the energy by
the exact Parseval quotient.  Keep the operation resource-bounded and
CAS-local.  Do not expose an SMT predicate or grant a universal energy bound.

## Evidence

A separate direct oracle enumerates all ordered inverse pairs, buckets their
additive sums, and squares the multiplicities.  It agrees with the Walsh route
for every `2<=ell<=9` and every `1<=d<ell`.  The complete level-eight row is

```text
[8, 40, 176, 928, 7424, 77824, 1114112].
```

A mutation control distinguishes the inverse-additive energy from the
existing multiplicative product energy.  Invalid degrees and group-order
resource exhaustion decline explicitly.

Distributed finite probes on `s1`, `s4`, `s5`, `s6`, and `s7` covered levels
17 through 21.  They suggest a stable no-wrap regime for fixed `d` once the
modulus is sufficiently deep.  ADR-0493 subsequently proves exact
stabilization for `ell>=3d`, supplies an independent rational-function CAS
route, and derives an explicit `2^(2d+o(d))` bound.  The finite observations
in this ADR remain only the evidence that selected that theorem.

## Alternatives

- Reuse multiplicative product energy: rejected because additive equality of
  inverses and multiplicative product equality are different relations and
  already produce different values at `(ell,d)=(8,4)`.
- Cite Bagshaw's 2024 energy lemma directly at `q=2`: rejected because that
  paper globally fixes odd `q`; any characteristic-two use must reprove the
  relevant dependency chain.
- Promote the fleet pattern without a proof: rejected.  The later promotion in
  ADR-0493 rests instead on clearing denominators, a degree bound, and a
  rational-collision classification.

## Consequences

- The exponent audit can use the exact special-modulus energy rather than a
  mismatched product statistic.
- Characteristic-free Hölder identities and characteristic-dependent complete
  sums remain visibly separate.
- The operation can falsify proposed piecewise energy formulae before they are
  used in the Lemire proof, while contributing no universal theorem credit.
- ADR-0493 refines this boundary: the Walsh table remains bounded, while the
  no-wrap stabilization and divisor envelope are uniform source-level lemmas.
