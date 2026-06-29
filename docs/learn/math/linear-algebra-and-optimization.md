# Linear Algebra And Optimization

Concept rows:

- `curriculum_linear_algebra`, `field_linear_algebra`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `field_functional_analysis_and_operator_theory` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [linear-algebra-rational-v0](../../../artifacts/examples/math/linear-algebra-rational-v0/)
- [linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
- [finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/)

## What Axeyum Checks

The linear path uses exact rational matrices. It replays `A*x = b`, checks
`L*U = A`, validates a row-scaling inconsistency certificate, checks LP
feasibility witnesses, checks a tiny Farkas infeasibility certificate, and
replays finite-dimensional norm/operator examples.

This is a strong resource path because the trusted checker can be small: matrix
multiplication, vector norms, linear inequalities, and certificate arithmetic.

## Horizon

Rank theorems, spectral theorems, conditioning, numerical stability, SDP,
general convex analysis, and algorithm convergence need proof routes or
carefully bounded numerical-experiment metadata.
