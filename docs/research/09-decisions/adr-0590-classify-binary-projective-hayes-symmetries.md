# ADR-0590: Classify binary projective Hayes symmetries

Status: accepted
Date: 2026-08-21
Index-summary: Prove translation is the only nonidentity binary projective transformation acting on the fixed-degree Hayes quotient

## Context

ADR-0587 obtains exact spectral cancellation from `x -> x+1`.  A second
independent involution could enlarge the symmetry orbits and potentially
remove a positive fraction of the residual characters.  The remaining four
elements of `PGL_2(GF(2))` involve inversion, so their action on the monic
fixed-degree family and its reciprocal high-coefficient quotient must be
decided before such an argument receives credit.

## Decision

Add `binary_hayes_projective_symmetry_classification`, enumerating all six
binary determinant-one matrices.  For

```text
g=(a,b;c,d),
g.F(x)=(c*x+d)^n F((a*x+b)/(c*x+d)).
```

The transformation preserves every monic polynomial of degree `n` only if it
fixes infinity, equivalently `c=0`.  Determinant one over `GF(2)` then forces
`a=d=1`, leaving exactly

```text
x -> x,             x -> x+1.
```

If `c=1`, the transformed leading coefficient is `F(a)`.  The monic
polynomial `(x+a)^n` is therefore an explicit degree-drop witness.  Reciprocal
and conjugate transformations may preserve selected constant-one polynomials,
but their resulting reciprocal class depends on low coefficients not present
in the Hayes quotient; they do not define a second action on that quotient.

## Evidence

The focused test enumerates the six matrices for every `1<=n<=64`, requires
exactly two quotient actions, identifies their matrices as identity and
translation, checks all four degree-drop witness roots, and exercises the
degree-zero refusal.  All-feature CAS `lib`/`bins`/`tests` Clippy passes.

## Consequences

- Translation is the complete nontrivial `PGL_2(GF(2))` symmetry available on
  the existing high-coefficient Hayes quotient.
- Inversion cannot be composed with ADR-0587 to create larger character
  orbits without enlarging the state space to include low coefficients.  Such
  an enlargement is the two-sided functional-equation problem already known
  not to bound the endpoint trace by itself.
- The residual `(WITT-LOW)` theorem must use signed trace structure rather than
  another binary projective symmetry.  No `(REL)` proof credit is gained.
