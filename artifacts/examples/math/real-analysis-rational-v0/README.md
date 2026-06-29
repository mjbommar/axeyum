# Real Analysis Rational V0

This pack is the bounded rational bridge for real-analysis examples. It checks
small interval, ball, epsilon-delta, and polynomial side-condition facts with
exact rational arithmetic, then keeps general real-analysis theorems marked as
Lean horizons.

The examples are:

- a closed rational interval contained in an open rational ball;
- a finite epsilon-delta sample for `f(x) = 2x + 1`;
- a small squeeze-style polynomial bound on rational samples;
- checked rejection of a false delta for the same linear function;
- a general real-analysis Lean-horizon row.

## Concepts

- `field_real_analysis`
- `field_topology`
- `field_logic_and_proof`
- `curriculum_reals`
- `curriculum_sequences_and_limits`
- `curriculum_calculus`

## Trust Story

The validator uses exact `Fraction` arithmetic. It recomputes interval endpoint
distances, finite domain balls, linear function values, polynomial bounds, and
the bad-delta counterexample from the raw pack data.

This is finite checked evidence. It is not a proof of real completeness,
general continuity, arbitrary limit laws, compactness, or the intermediate
value theorem.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
```
