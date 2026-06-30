# Exact Finite Simplicial Cup Product Checks

Audience: learners, educators, topology contributors, algebraic-topology
contributors, and solver contributors who need a tiny cochain-operation
resource.

This pack checks finite simplicial cup products over `F2`. It starts with a
finite ordered simplicial complex, lists cochain values on simplices, and
replays the Alexander-Whitney split convention:

```text
(alpha cup beta)([v0,...,v(p+q)])
  = alpha([v0,...,vp]) * beta([vp,...,v(p+q)]) mod 2
```

The checked slice is finite replay plus one source-linked QF_BV/DRAT
contradiction for a malformed cup-product value.

## Rows

- `cup-product-replay`: recompute `alpha cup beta` and `beta cup alpha` on one
  filled triangle.
- `cup-coboundary-leibniz-replay`: check one finite
  `delta(f cup g) = delta(f) cup g + f cup delta(g)` row over `F2`.
- `bad-cup-product-rejected`: reject a false cup-product value by finite replay.
- `qf-bv-bad-cup-product`: check the final one-bit value mismatch through
  QF_BV bit-blast and DRAT evidence.
- `general-cup-product-lean-horizon`: keep cohomology-ring theory under Lean
  horizon.

## Trust Boundary

The finite validator recomputes simplex closure, F2 cup products, F2
coboundaries, and the listed finite Leibniz row. The promoted bad row is
accepted only because the fixed one-bit value conflict has a checked DRAT
proof after bit-blast. This pack does not prove associativity, graded
commutativity, naturality, cohomology-ring quotienting, or topological
invariance.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cup-products-v0
cargo test -p axeyum-solver --test math_resource_bv_routes finite_simplicial_cup_product_bad_value_emits_checked_bv_drat
```
