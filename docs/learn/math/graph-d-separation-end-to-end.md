# End To End: DAG D-Separation Checks

This lesson follows one finite DAG resource from directed edges to active-path
witness replay, blocked-path refutation, source-linked CNF evidence, and
descendant-opened collider replay.
It uses
[graph-d-separation-v0](../../../artifacts/examples/math/graph-d-separation-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_graph_theory`, `field_probability_theory`, and
  `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `chain-active-without-conditioning` | `sat` | checked |
| `chain-conditioned-blocks` | `unsat` | checked CNF/DRAT/LRAT |
| `fork-conditioned-blocks` | `unsat` | checked |
| `collider-unconditioned-blocks` | `unsat` | checked CNF/DRAT/LRAT |
| `collider-descendant-opens` | `sat` | checked |

Every row is a finite graph-theoretic d-separation check. The pack does not
prove causal identification, do-calculus, probabilistic graphical-model
semantics, adjustment-set correctness, or statistical consistency.

## The Finite Rule

D-separation is checked on paths in the undirected skeleton of a finite DAG.
For each interior node on a path:

- a non-collider blocks the path when it is in the conditioning set;
- a collider blocks the path unless it or one of its descendants is in the
  conditioning set.

The validator enumerates finite skeleton paths and computes the finite
descendant relation directly from the DAG.

## Replay An Active Chain

The active chain row uses:

```text
a -> b -> c
conditioning_set = {}
path = a, b, c
```

The middle node `b` is a non-collider, and it is not conditioned on. The path is
therefore active, so the d-connected claim is checked as `sat`.

## Refute A Conditioned Chain

The next row uses the same chain but conditions on `b`:

```text
a -> b -> c
conditioning_set = {b}
```

Now `b` is a conditioned non-collider. The validator enumerates the only simple
skeleton path from `a` to `c` and confirms that it is blocked, so the
d-connected claim is rejected.

The source-linked CNF artifact for this row asserts the selected path, the
conditioned non-collider, and the bad active-path claim. Axeyum emits a DRAT
refutation, elaborates it to LRAT, and checks both proof objects independently.

## Refute A Conditioned Fork

The fork row uses:

```text
a <- b -> c
conditioning_set = {b}
```

Again, the only simple path is:

```text
a, b, c
```

The middle node `b` is a non-collider on that path. Conditioning on it blocks
the path, so the d-connected claim is rejected.

## Refute An Unconditioned Collider

The collider row uses:

```text
a -> b <- c
conditioning_set = {}
```

The path `a, b, c` has a collider at `b`. Because neither `b` nor a descendant
of `b` is conditioned on, the path is blocked. The validator enumerates the
only simple path and rejects the d-connected claim.

This row now has its own source-linked CNF artifact. It asserts the selected
path, the collider fact, `not collider_opened`, and the bad active-path claim.
The Boolean rule says an active path through a collider requires that collider
to be opened by conditioning on it or a descendant, so the row refutes by the
same DRAT-to-LRAT checked route as the conditioned-chain row.

## Replay A Descendant-Opened Collider

The final row extends the collider with one descendant:

```text
a -> b <- c
b -> d
conditioning_set = {d}
path = a, b, c
```

The validator computes that `d` is a descendant of `b`. Conditioning on `d`
opens the collider at `b`, so the path from `a` to `c` is active and the
d-connected claim is checked as `sat`.

## Why This Matters

D-separation is the bridge between finite graph search and later probability
resources:

```text
untrusted search proposes a path and conditioning set
trusted checker enumerates finite paths and applies blocking rules
```

The checked evidence is purely finite and graph-theoretic. It is useful as a
resource boundary for future causal examples, but it is not a proof of general
causal inference semantics.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
```

## Trust Boundary

The validator checks DAG edges, skeleton paths, collider/non-collider status,
conditioning sets, descendant activation, and finite enumeration of all simple
paths for `unsat` rows. Full causal identification and do-calculus remain
proof-horizon material.
