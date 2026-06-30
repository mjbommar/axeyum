# Exact Finite Simplicial Cohomology Checks

Audience: learners, educators, topology contributors, algebraic-topology
contributors, and solver contributors who need a tiny cochain-complex resource.

This pack checks finite simplicial cohomology over `F2`. It starts with a
finite simplicial complex, lists cochain values on simplices, and replays the
coboundary:

```text
delta phi(sigma) = phi(boundary sigma) mod 2
```

The checked slice is finite replay plus one source-linked QF_UF/Alethe
contradiction for a malformed coboundary value.

## Rows

- `coboundary-replay`: recompute the F2 coboundary of one vertex potential.
- `coboundary-squared-zero`: check `delta(delta f) = 0` on a filled triangle.
- `cohomology-rank-replay`: recompute F2 cohomology dimensions for a three-edge
  circle and check one non-coboundary cocycle.
- `bad-coboundary-rejected`: reject a false coboundary value by finite replay.
- `qf-uf-bad-coboundary-value`: check the final value mismatch through
  QF_UF/Alethe evidence.
- `general-cohomology-lean-horizon`: keep general cohomology theory under Lean
  horizon.

## Trust Boundary

The finite validator recomputes simplex closure, F2 coboundary values,
`delta^2 = 0`, F2 matrix ranks, and the non-coboundary status of the listed
cocycle. The promoted bad row is accepted only because the fixed value conflict
has a checked Alethe proof. This pack does not prove cup-product laws,
universal-coefficient theorems, de Rham comparison, sheaf cohomology, or
cohomology invariance.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cohomology-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_simplicial_cohomology_bad_coboundary_value_emits_checked_alethe
```
