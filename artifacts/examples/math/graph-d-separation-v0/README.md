# Finite DAG D-Separation Checks

This pack adds the first causal-graph shaped resource to the graph-theory lane.
It stays finite and graph-theoretic: every claim is checked by enumerating
simple paths in a small directed acyclic graph and applying the d-separation
blocking rules.

The examples cover:

- an active chain with no conditioning;
- a CNF-backed chain blocked by conditioning on its middle non-collider;
- a fork blocked by conditioning on its middle non-collider;
- a CNF-backed unconditioned collider that blocks a path;
- a collider opened by conditioning on a descendant.

## Concepts

- `field_graph_theory`
- `field_probability_theory`
- `field_discrete_math`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`

## Trust Story

- Active-path witnesses are checked against the original DAG.
- UNSAT d-connected claims are checked by enumerating all simple skeleton paths
  between the source and target.
- The conditioned-chain blocking row also has a source-linked DIMACS artifact
  and a Boolean regression that emits and independently checks DRAT and LRAT
  proof objects.
- The unconditioned-collider blocking row has its own source-linked DIMACS
  artifact for the collider-specific rule and the same checked DRAT/LRAT route.
- Collider activation uses the finite descendant relation computed from the DAG.
- General causal identification, do-calculus, and statistical semantics remain
  outside this pack.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
```
