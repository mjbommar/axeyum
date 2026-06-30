# Checks

## `chain-active-without-conditioning`

Expected result: `sat`.

The validator checks that the path:

```text
a, b, c
```

is valid in the skeleton of `a -> b -> c`, and that `b` is an unconditioned
non-collider.

## `chain-conditioned-blocks`

Expected result: `unsat`.

The same chain is blocked by conditioning on `b`. The validator enumerates the
only simple skeleton path and confirms the middle non-collider blocks it.

The promoted solver artifact is:

```text
artifacts/examples/math/graph-d-separation-v0/cnf/chain-conditioned-blocks.cnf
```

It asserts that the path `a-b-c` exists, that `b` is the middle non-collider,
that `b` is conditioned, and that the path is active. The final clause encodes
the d-separation rule that a conditioned non-collider blocks an active path, so
the fixed claim is unsatisfiable.

The shared Boolean regression:

```text
crates/axeyum-cnf/tests/math_resource_boolean_routes.rs::graph_d_separation_chain_conditioned_blocks_emits_checked_drat_and_lrat
```

parses the DIMACS artifact, emits a DRAT refutation, elaborates it to LRAT, and
checks both proof objects independently.

## `fork-conditioned-blocks`

Expected result: `unsat`.

For `a <- b -> c`, conditioning on `b` blocks the only simple path between `a`
and `c`.

## `collider-unconditioned-blocks`

Expected result: `unsat`.

For `a -> b <- c`, the only simple path is blocked because `b` is an
unconditioned collider and has no conditioned descendant.

## `collider-descendant-opens`

Expected result: `sat`.

For:

```text
a -> b <- c
b -> d
```

conditioning on `d` opens the collider at `b`. The validator computes
descendants from the DAG and checks the active path.
