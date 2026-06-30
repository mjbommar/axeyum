# Real Algebra RCF Shadow

Audience: learners and solver/proof contributors who need a careful bridge
from exact rational arithmetic to algebraic real-number constraints.

This pack is a small real-closed-field shadow, not a real-analysis library. It
checks exact rational witnesses for real order and polynomial constraints, then
checks two tiny one-variable infeasibility certificates. Completeness,
epsilon-delta arguments, and arbitrary analysis remain proof-assistant
horizons.

## Concept Rows

- `curriculum_reals`
- `curriculum_rationals`
- `curriculum_polynomials`
- `field_real_analysis`
- `field_optimization_and_convexity`

## Claims

- A rational midpoint is a real ordered-field witness.
- A positive product witness satisfies a nonlinear real constraint.
- A quadratic polynomial can have an exact rational real root.
- `x^2 < 0` has no real solution.
- A quadratic with negative discriminant has no real root, with a QF_LRA/Farkas
  artifact checking the final nonnegative-discriminant contradiction.
- The real completeness axiom and epsilon-delta analysis remain Lean-horizon.

## Validation

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
```

The validator uses exact `Fraction` arithmetic. It replays witnesses against
the original formulas, recognizes the fixed square-nonnegative row, checks the
quadratic discriminant for the negative-discriminant row, and keeps the
second-order real-completeness row marked `lean-horizon`. The promoted solver
row checks only the final linear discriminant conflict after exact replay has
computed `D = -4`.

## Limitations

These are hand-sized algebraic real examples. They do not claim a full CAD,
RCF certificate emitter, SOS checker, or proof of real completeness. Graduation
requires Axeyum encodings plus checked Farkas/SOS/RCF evidence where the row is
UNSAT.
