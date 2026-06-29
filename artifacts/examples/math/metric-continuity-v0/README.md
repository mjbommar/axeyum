# Metric Continuity V0

This pack adds the first finite epsilon-delta continuity resource. It uses a
finite rational metric-space slice and the function `f(x) = 2x`, so every
positive check and the bad-delta rejection are exact finite arithmetic.

The examples are:

- a finite Lipschitz witness;
- a finite epsilon-delta continuity witness;
- an open-ball preimage witness;
- checked rejection of an overlarge delta;
- a general continuity Lean-horizon row.

## Concepts

- `field_real_analysis`
- `field_topology`
- `field_logic_and_proof`
- `curriculum_sequences_and_limits`
- `curriculum_calculus`
- `curriculum_reals`

## Trust Story

The validator parses every distance and function value as an exact rational. It
checks the finite metric table, recomputes all finite balls, checks the
Lipschitz inequality pairwise, checks epsilon-delta containment, and validates
the documented bad-delta counterexample.

This is checked finite evidence for the bad-delta row and replay-only evidence
for the positive finite witnesses. It is not a proof of general continuity on
real metric spaces.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
```
