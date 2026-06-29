# GCD Bezout V0

This pack covers the first compute-and-check slice for
`divisibility-and-euclid`: gcd replay, Bezout coefficient replay, direct
divisibility witnesses, and a fixed linear Diophantine rejection.

The examples are exact integer artifacts:

- replay `gcd(252, 198) = 18` and its positive common divisors;
- replay the Bezout identity `252*4 + 198*(-5) = 18`;
- replay `18 | 252` with quotient `14`;
- reject `6*x + 10*y = 15` because `gcd(6, 10)` does not divide `15`.

These checks do not claim unique factorization, prime-distribution theorems, or
general algebraic number theory.

## Concepts

- `curriculum_divisibility_and_euclid`
- `curriculum_integers`
- `field_number_theory`

## Trust Story

The validator recomputes each arithmetic fact with exact integers. SAT rows are
accepted only after replaying the listed witness against the original claim. The
UNSAT row is accepted only after recomputing the gcd of the coefficients and
checking the divisibility obstruction for the fixed Diophantine equation.

This pack does not yet emit Axeyum LIA terms or an `UnsatDiophantine`
certificate. The graduation route is to lower the fixed Diophantine row into
QF_LIA and check the resulting gcd certificate through Axeyum's integer evidence
checker.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
```
