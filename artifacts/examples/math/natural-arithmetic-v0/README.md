# Natural Arithmetic V0

This pack covers the first bounded Peano-arithmetic slice for `naturals`:
successor arithmetic, fixed addition/multiplication identities, and bounded
negations of Peano-style facts.

The examples are exact finite natural-number artifacts:

- replay `5 + S(7) = S(5 + 7)`;
- replay `6 + 4 = 4 + 6`;
- replay `2 * (3 + 4) = 2*3 + 2*4`;
- reject a bounded counterexample to successor injectivity;
- reject a bounded predecessor of zero;
- reject a negative value in the bounded natural domain.

These checks do not claim the full induction schema or universal arithmetic
theorems over all natural numbers.

## Concepts

- `curriculum_naturals`
- `field_number_theory`
- `field_discrete_math`

## Trust Story

The validator recomputes every SAT witness with exact integer arithmetic over
nonnegative values. UNSAT rows are accepted only after enumerating the fixed
bounded natural domain named in `expected.json`.

This pack does not yet emit Axeyum BV/LIA formulas or proof artifacts. The
graduation route is deterministic QF_BV/QF_LIA lowering plus checked evidence
for bounded no-counterexample rows.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/natural-arithmetic-v0
```
