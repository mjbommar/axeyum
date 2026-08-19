# ADR-0513: Test local Witt-cylinder concentration

Status: accepted
Date: 2026-08-19
Index-summary: Measure exact local fourth-over-second concentration on every conductor cylinder before proposing a Carleson bound

## Context

ADR-0512 rejects a direct magic-square parametrization of the connected
remainder. The conductor filtration still represents the whole fourth moment.
For `f_e=D_e^2` and a level-`j` Witt cylinder `b`, define

```text
R_j(b)=2^(ell-j) sum_(e below b) f_e^2
       / (sum_(e below b) f_e)^2.
```

Its excess over one is the normalized Haar square energy below the cylinder.
At the root, `R_0=2^ell M_4/M_2^2` is the kurtosis ratio needed to turn the
proved second-moment bound into a polynomial-times-`2^(3ell)` fourth moment.

## Decision

Compute every `R_j(b)` exactly as a rational pair, retain the worst cylinder
at each level, and check the root against the independently computed `M_2`
and `M_4`. Treat a small uniform ceiling as a conjectural Carleson target, not
as theorem evidence.

## Evidence

At `(ell,n)=(9,19)`, the root ratio is about `2.813`. The largest local ratio
occurs at level six and is

```text
7244949696 / 1224440064 < 5.92.
```

The final singleton level has ratio one. The native test checks the root
identity, singleton boundary, and a preallocation resource decline.

## Consequences

- The provisional target `R_j(b)<=8` is concrete and directly testable on the
  fleet.
- A uniform proof, combined with the existing exact-conductor Weil
  second-moment envelope, would give a polynomial-times-`2^(3ell)` fourth
  moment and hence close all sufficiently large endpoints.
- Finite satisfaction of the ceiling grants no theorem credit.
