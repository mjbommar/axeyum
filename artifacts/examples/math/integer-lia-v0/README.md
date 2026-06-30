# Integer LIA V0

This pack covers the first exact linear-integer slice for `integers`: signed
order facts, integer ring replay, linear equation witnesses, interval
infeasibility, and a fixed GCD-test Diophantine rejection.

The examples are exact integer artifacts:

- replay signed trichotomy for `-3` and `4`;
- replay order transitivity for `-2 < 1 < 5`;
- replay `(a + b) - b = a` at `a = -7`, `b = 5`;
- replay `3*x - 2*y = 7` at `x = 3`, `y = 1`;
- reject `z >= 5 and z <= 2`;
- reject `2*x + 4*y = 3` because `gcd(2,4)` does not divide `3`.

These checks do not claim general quantified integer algebra or induction over
all integers.

## Concepts

- `curriculum_integers`
- `curriculum_naturals`
- `field_number_theory`

## Trust Story

The validator recomputes every row with exact integer arithmetic. SAT rows are
accepted only after replaying the listed values against the original claim.
UNSAT rows are accepted only after checking the fixed interval contradiction or
the exact GCD non-divisibility criterion.

The GCD obstruction is also a solver-backed resource. Its SMT-LIB artifact is
[`smt2/diophantine-gcd-obstruction-conflict.smt2`](smt2/diophantine-gcd-obstruction-conflict.smt2):
it encodes `2*x + 4*y = 3` as a tiny `QF_LIA` Diophantine contradiction. The
`math_resource_lia_routes` regression requires Axeyum to emit
`UnsatDiophantine` evidence and independently re-check the certificate. The
SAT witness rows and the simple interval contradiction remain exact replay rows
until they add distinct solver-regression pressure.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/integer-lia-v0
```
