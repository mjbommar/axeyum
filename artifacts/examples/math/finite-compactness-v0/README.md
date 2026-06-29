# Finite Compactness V0

This pack adds the first finite compactness and open-cover resource. It uses a
three-point discrete topology, so cover and intersection claims are exact
finite set checks.

The examples are:

- a finite open-cover/subcover witness;
- a checked minimal-subcover-size witness;
- a finite-intersection-family witness;
- checked rejection of a bad open cover;
- a general compactness Lean-horizon row.

## Concepts

- `field_topology`
- `field_set_theory_and_foundations`
- `field_real_analysis`
- `curriculum_sets`
- `curriculum_reals`
- `curriculum_sequences_and_limits`

## Trust Story

The validator checks the finite topology axioms, confirms that cover elements
are open, recomputes cover unions, enumerates smaller subfamilies for the
minimal-subcover claim, checks closedness by open complements, and validates
the finite-intersection property by enumeration.

This pack is checked finite evidence for the minimal-subcover and bad-cover
rows. It is not a proof of arbitrary topological compactness, Heine-Borel, or
general finite-intersection-property theorems.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
```
