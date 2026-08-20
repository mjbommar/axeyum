# ADR-0522: Certify the dyadic auxiliary-unit quadratic projector

Status: accepted
Date: 2026-08-19
Index-summary: Make the modulo-eight auxiliary-unit Gauss projector a checked CAS primitive and require any joined Witt law to preserve its polarization contract

## Context

The binary Möbius weight is the Kronecker character of the integral
discriminant modulo eight.  Its four-phase expansion is exact, but estimating
the phases separately loses the indefinite cancellation.  The bridge note
proposes keeping them inside one quadratic Gauss sum over
`A=(Z/8Z)^x=<3,5>` before constructing any larger fibre/valuation/Witt group.

## Decision

Add `dyadic_auxiliary_quadratic_projector_report` as the native prerequisite
for a joined group law.

Write

```text
a=3^u 5^v=1+2u+4v (mod 8),
chi_8(a)=(-1)^(u+v),
Q_D(u,v)=chi_8(a) zeta_8^((a-1)D).
```

The operation checks for every `D mod 8` that

```text
sum_(a in A) chi_8(a) zeta_8^(aD)
  = 2(zeta_8-zeta_8^3) chi_8(D),
```

that the polarization of `Q_D` is `(-1)^(D u u')`, and that the radical and
phase restriction have the claimed sizes.  All cyclotomic sums use the exact
integral basis `1,zeta_8,zeta_8^2,zeta_8^3` with `zeta_8^4=-1`.

## Evidence

For odd `D`, the radical is exactly `{u=0}`, of size two, and the phase is
trivial on it.  For example, at `D=1` the normalized sum is
`2-2 zeta_8^2`, of squared complex magnitude eight.  For even `D`, the
polarization is trivial but the phase is a nontrivial character, and the sum
is exactly zero.  The ordinary test checks all eight residues and both the
projector and radical classifications.

## Alternatives

- Four separate triangle bounds were rejected because they erase the Gauss
  cancellation that creates the Möbius zero/sign projector.
- Treating the existing nonquadratic affine fibre as the auxiliary group was
  rejected: restriction to its `a=1` slice would still have to be quadratic,
  while the pinned support-degree-seven witness is not.

## Consequences

- A proposed joined fibre/valuation/Witt law now has a precise fail-fast
  contract: its discriminant difference modulo four must be additive before
  polarization or Heisenberg rank is computed.
- This projector is a proved finite algebraic identity, but no joined law or
  bounded radical for the endpoint sum has yet been found.  It grants no
  credit toward (CRT) by itself.
