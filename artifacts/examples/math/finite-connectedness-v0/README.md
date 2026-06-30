# Finite Connectedness V0

This pack adds the first finite connectedness resource. It uses two tiny
topological spaces so connectedness and disconnection claims reduce to exact
finite set enumeration.

The examples are:

- a connected two-point Sierpinski topology witness;
- a disconnected two-point discrete topology with an open separation;
- a clopen-subset disconnection witness;
- checked Bool/CNF DRAT/LRAT rejection of a false connectedness claim;
- a general connectedness Lean-horizon row.

## Concepts

- `field_topology`
- `field_set_theory_and_foundations`
- `field_real_analysis`
- `curriculum_sets`
- `curriculum_reals`
- `curriculum_sequences_and_limits`

## Trust Story

The validator checks the finite topology axioms, enumerates every subset of the
finite universe, recomputes clopen subsets, and recomputes open separations.
The bad-connectedness row is also encoded as a tiny `Bool/CNF` contradiction:

```text
the discrete topology has a non-trivial clopen subset {a}
the false connectedness claim says no non-trivial clopen subset exists
```

Axeyum emits a DRAT refutation, elaborates it to LRAT, and independently
checks both proof objects.

This pack is checked finite evidence for the bad connectedness claim. It is not
a proof of connected-image theorems, interval connectedness, path-connectedness,
or general topological connectedness.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_connectedness_bad_connected_claim_emits_checked_drat_and_lrat
```
