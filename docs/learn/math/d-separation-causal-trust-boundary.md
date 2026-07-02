# D-Separation Causal Trust Boundary

This page separates Axeyum's finite DAG d-separation resource from causal
identification, do-calculus, probabilistic graphical-model semantics,
adjustment-set correctness, and statistical consistency.

Primary pack:

- [graph-d-separation-v0](../../../artifacts/examples/math/graph-d-separation-v0/)

Companion lessons and maps:

- [End To End: DAG D-Separation Checks](graph-d-separation-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)

## Current Finite Resource

The pack fixes small directed acyclic graphs and asks whether two endpoints are
d-connected under a listed conditioning set. The checker does not trust the
claimed path status. It recomputes the finite undirected skeleton paths and
applies the d-separation blocking rules:

```text
non-collider on path + conditioned             -> path blocked
collider on path + no conditioned descendant   -> path blocked
collider on path + conditioned descendant      -> path opened
```

The checked resource covers:

```text
chain:    a -> b -> c
fork:     a <- b -> c
collider: a -> b <- c
opened:   a -> b <- c, b -> d, condition on d
```

The evidence is finite and graph-theoretic. The `chain-conditioned-blocks` and
`collider-unconditioned-blocks` rows also pin source DIMACS artifacts and share
the Boolean CNF route that emits DRAT, elaborates to LRAT, and checks both proof
objects independently. The `fork-conditioned-blocks` row is checked by finite
enumeration, but it is not currently a separate source-linked CNF regression.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `chain-active-without-conditioning` | `sat` | checked | The listed path through the unconditioned non-collider is active. |
| `chain-conditioned-blocks` | `unsat` | checked CNF/DRAT/LRAT | Conditioning on the chain's middle non-collider blocks the only simple path. |
| `fork-conditioned-blocks` | `unsat` | checked finite enumeration | Conditioning on the fork's middle non-collider blocks the only simple path. |
| `collider-unconditioned-blocks` | `unsat` | checked CNF/DRAT/LRAT | The unconditioned collider blocks the only simple path. |
| `collider-descendant-opens` | `sat` | checked | Conditioning on a descendant of the collider opens the path. |

These rows prove only the listed finite DAG facts. They are useful seeds for
causal-graph resources because they make the graph-search boundary explicit:

```text
untrusted fast search -> proposed path and conditioning set
trusted small checking -> finite path enumeration, collider classification, and descendant replay
causal horizon         -> identification, adjustment, do-calculus, and statistical semantics
```

## What Is Not Proved Yet

The current pack does not prove:

- graphical Markov semantics for probability distributions;
- soundness or completeness of d-separation as a probabilistic independence
  criterion;
- back-door, front-door, or adjustment-set criteria;
- do-calculus rules;
- causal effect identification;
- faithfulness, causal sufficiency, latent-variable, selection-bias, or
  transportability assumptions;
- statistical consistency of any estimator learned from finite samples.

Those claims need explicit probability spaces, random variables, interventions,
identification theorems, and no-`sorry` proof artifacts before they can graduate
from the causal horizon. The finite d-separation rows are teaching and
regression resources, not causal-identification theorems.

## Query The Boundary

Find all checked finite d-separation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --proof-status checked \
  --require-any
```

Separate active-path witnesses from blocked-path refutations:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --expected-result sat \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

Find the source-linked Boolean CNF blocker rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --route boolean \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

Drill into the chain, fork, collider, and descendant-opened examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --proof-status checked \
  --text chain \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --proof-status checked \
  --text fork \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --route boolean \
  --proof-status checked \
  --text "no conditioning" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --proof-status checked \
  --expected-result sat \
  --text "conditioning on a descendant" \
  --require-any
```

There is intentionally no `horizon-frontier --text d-separation` command here:
the current pack has no committed Lean-horizon row for causal identification or
probabilistic semantics. Consumers should display the current rows as checked
finite graph evidence, not as theorem-boundary coverage.

## Graduation Criteria

Causal d-separation resources graduate only when they add:

1. a schema for probability spaces, random variables, interventions, and graph
   semantics that is distinct from finite graph path replay;
2. explicit theorem-horizon rows for graphical Markov soundness/completeness,
   back-door/front-door criteria, and do-calculus rules;
3. finite probability-table examples that link conditional-independence replay
   to the graph resource without claiming general identification;
4. source artifacts and checked certificates for any new Boolean blocker class
   before it is promoted as a solver regression;
5. display labels that keep finite d-separation checks, probability-table
   checks, causal theorem horizons, and benchmark claims separate.

Until then, `graph-d-separation-v0` remains a finite checked graph resource and
a disciplined bridge to future causal reasoning resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --expected-result sat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --expected-result unsat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --route boolean --proof-status checked --expected-result unsat --require-any
```

Expected resource boundary: the finite pack validates, the checked-row queries
return active-path and blocked-path rows, and causal identification remains an
explicit out-of-scope horizon rather than a checked claim.
