# Checks

## `feasible-flow-witness`

Expected: `sat`.

Validation: `finite_network_flow_replay`.

The validator checks:

- every listed endpoint is in the vertex set;
- capacities and flows are nonnegative exact rationals;
- each edge flow is at most its capacity;
- internal vertices have zero net outflow;
- source net outflow and sink net inflow both equal `3`.

## `flow-cut-optimality-witness`

Expected: `sat`.

Validation: `finite_flow_cut_certificate_replay`.

The validator checks the same feasibility obligations, then recomputes the
directed cut from `source_side = {s}` to `target_side = {a,b,t}`. The crossing
capacity is `3`, and the net flow through the cut is also `3`.

## `bad-capacity-bound-rejected`

Expected: `unsat`.

Validation: `finite_bad_flow_capacity_refutation`.

The validator allows the malformed flow to parse, locates the listed
violating edge `s -> a`, and confirms that the row is false because
`claimed_flow = 3` exceeds `capacity = 2`.

## `bad-flow-value-rejected`

Expected: `unsat`.

Validation: `finite_bad_flow_value_cut_bound_refutation`.

The validator recomputes the source-side cut capacity as `3`. A claimed
feasible flow value `4` is therefore rejected by this finite cut upper bound.

## `max-flow-min-cut-theorem-lean-horizon`

Expected: `not-run`.

Validation: `lean_horizon_metadata`.

The finite rows are useful shadows. The general theorem and algorithmic
correctness route remain future Lean/proof work.
