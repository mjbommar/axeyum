# Finite Continuous Maps V0

This pack adds finite topological continuity and homeomorphism checks. It uses
two-point Sierpinski and discrete topologies so continuity reduces to exact
preimage enumeration.

The examples are:

- a finite continuous-map witness;
- an open-preimage witness;
- a finite homeomorphism witness;
- finite replay rejection of the non-open preimage in a bad continuity claim;
- checked QF_UF/Alethe rejection of the malformed preimage-membership table
  behind that bad continuity claim;
- checked rejection of a false homeomorphism claim;
- a general continuous-map Lean-horizon row.

## Concepts

- `field_topology`
- `field_set_theory_and_foundations`
- `field_real_analysis`
- `curriculum_sets`
- `curriculum_reals`
- `curriculum_sequences_and_limits`

## Trust Story

The validator checks finite topology axioms for the domain and codomain,
checks that the map is total, recomputes preimages of open sets, checks
continuity by finite enumeration, and checks homeomorphism by bijectivity plus
continuity of the inverse. The `qf-uf-bad-preimage-membership` row uses
QF_UF/Alethe only for the small preimage-membership consistency conflict; it
does not prove arbitrary topological continuity theorems.

This pack is checked finite evidence for the bad continuity and bad
homeomorphism rows. It is not a proof of continuous-image theorems,
homeomorphism-invariance, compactness preservation, or connectedness
preservation for arbitrary spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
```
