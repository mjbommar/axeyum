# Finite Network Flow And Cut Certificates

This pack checks one exact directed network-flow example and its cut certificate.
It is a finite replay resource, not a proof of the general max-flow/min-cut
theorem.

## Audience

- Learners connecting graph cuts, capacities, and linear constraints.
- Proof contributors looking for the future theorem boundary.
- Solver contributors looking for a source-linked exact-rational flow/cut
  regression seed.

## Concept Links

- `field_graph_theory`
- `field_discrete_math`
- `field_optimization_and_convexity`
- `field_linear_algebra`
- `bridge_finite_graph_replay_obstruction`

## Checks

- `feasible-flow-witness`: checks nonnegative capacities/flows, capacity
  bounds, conservation, and value 3.
- `flow-cut-optimality-witness`: checks that the source-side cut `{s}` has
  capacity 3 and is saturated by the feasible flow.
- `bad-capacity-bound-rejected`: rejects a malformed edge flow `3 > 2`.
- `bad-flow-value-rejected`: rejects a claimed flow value 4 using the finite
  cut-capacity upper bound 3.
- `qf-lra-bad-flow-value-cut-bound`: checks the final scalar contradiction
  `4 <= 3` through a committed SMT-LIB artifact and `UnsatFarkas` evidence.
- `max-flow-min-cut-theorem-lean-horizon`: records the general theorem boundary.

## Trust Boundary

The checker recomputes every arithmetic fact over exact rationals from the
listed network. Search may propose the flow or cut; trusted checking is only
capacity, conservation, cut-capacity, equality/inequality replay, and the
source-linked Farkas certificate for the promoted cut-bound conflict.

## Run

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-flow-cut-v0
```
