# Finite Connectedness V0

This pack adds the first finite connectedness resource. It uses two tiny
topological spaces so connectedness and disconnection claims reduce to exact
finite set enumeration.

The examples are:

- a connected two-point Sierpinski topology witness;
- a disconnected two-point discrete topology with an open separation;
- a clopen-subset disconnection witness;
- checked rejection of a false connectedness claim;
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

This pack is checked finite evidence for the bad connectedness claim. It is not
a proof of connected-image theorems, interval connectedness, path-connectedness,
or general topological connectedness.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
```
