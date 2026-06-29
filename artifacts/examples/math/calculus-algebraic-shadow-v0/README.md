# Calculus Algebraic Shadow

Audience: learners and solver/proof contributors who need a precise,
checkable slice of calculus without overstating analytic coverage.

This pack checks polynomial derivative algebra: coefficient differentiation,
the product rule for fixed polynomial instances, tangent-line replay, a convex
quadratic critical point, and rejection of a false derivative value. It keeps
epsilon-delta differentiability, integration, and the fundamental theorem of
calculus under Lean horizon.

## Concept Rows

- `curriculum_calculus`
- `curriculum_polynomials`
- `curriculum_reals`
- `curriculum_sequences_and_limits`
- `field_real_analysis`
- `field_differential_equations_and_dynamical_systems`
- `field_numerical_analysis`

## Claims

- A polynomial derivative coefficient list can be recomputed exactly.
- The product rule can be checked as a polynomial identity for fixed factors.
- A tangent-line value can be replayed from a polynomial and its derivative.
- A convex quadratic critical point can be checked algebraically.
- A false derivative value at a point is rejected.
- General calculus theorems remain proof-assistant work.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
```

The validator differentiates coefficient lists, multiplies and adds
polynomials, evaluates tangent lines, checks a fixed convex critical point, and
keeps analytic theorem rows marked `lean-horizon`.

## Limitations

This pack validates the algebraic shadow of calculus. It does not prove the
power rule from a limit definition, continuity, differentiability, the mean
value theorem, integration, or convergence of series. Those claims need a
kernel-checked proof route before graduation.
