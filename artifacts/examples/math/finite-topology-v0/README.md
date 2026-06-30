# Finite Topology V0

This pack covers tiny finite topology examples for the `topology`
field-extension row. It uses explicit finite universes and exact rational
metric distances, not general topological-space theorems.

The examples are the finite topology shadow that will later map to Axeyum's
finite-set, Bool, and LRA routes:

- topology axiom replay for a finite list of open sets;
- closure and interior computation for a fixed subset;
- open metric-ball computation over a finite rational metric space;
- a checked Bool/CNF DRAT/LRAT rejection of a malformed open-set family.

## Concepts

- `field_topology`
- `field_set_theory_and_foundations`
- `field_real_analysis`
- `curriculum_sets`
- `curriculum_reals`
- `curriculum_sequences_and_limits`

## Trust Story

The current validator checks the finite topology by explicit set computation:
empty/universe membership, pairwise union closure, and pairwise intersection
closure. It computes closure as the complement of the interior of the
complement. The metric-ball check parses distances exactly as rational strings,
checks the finite metric table, and recomputes the open ball. The promoted bad
row checks only the final Boolean contradiction between an omitted empty set
and the topology axiom requiring the empty set to be open. It does not claim
general topology facts such as compactness, connectedness, or continuity.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_topology_bad_empty_open_emits_checked_drat_and_lrat
```
