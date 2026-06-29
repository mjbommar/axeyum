# Rational And Real Algebra

Concept rows:

- `curriculum_rationals`, `curriculum_reals`, and `curriculum_polynomials` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis`, `field_optimization_and_convexity`, and
  `field_geometry` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [rationals-lra-v0](../../../artifacts/examples/math/rationals-lra-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [coordinate-geometry-v0](../../../artifacts/examples/math/coordinate-geometry-v0/)

## What Axeyum Checks

The real-algebra path is currently exact rational arithmetic plus algebraic
shadows of real reasoning. It checks density witnesses, additive inverses,
fixed order facts, LP feasibility and infeasibility certificates, midpoints,
collinearity determinants, and squared distances.

This is where Axeyum can teach that many "real" examples have a small rational
core that is directly replayable.

## Encode / Check Walkthrough

For a rational order check, encode:

```text
a = 1/3
b = 2/3
midpoint = 1/2
```

The validator checks both the ordering and the exact arithmetic identity. For a
coordinate-geometry check, encode two endpoints and the proposed midpoint:

```text
A = (0, 0)
B = (4, 2)
M = (2, 1)
```

The checker recomputes both midpoint coordinates. For optimization, encode
linear constraints and a candidate assignment; the checker evaluates each
constraint exactly.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
```

## Horizon

Completeness, arbitrary limits, continuity, compactness, integration, and
general real-analysis theorems remain Lean-horizon. Nonlinear real arithmetic
and SOS/RCF certificates are future proof-route work, not assumed coverage.
