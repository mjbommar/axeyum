# End To End: GCD And Bezout

This lesson follows one divisibility resource from exact gcd replay to a checked
linear Diophantine refutation. It uses the
[gcd-bezout-v0](../../../artifacts/examples/math/gcd-bezout-v0/) pack.

Concept rows:

- `curriculum_divisibility_and_euclid` and `curriculum_integers` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `gcd-common-divisors-replay` | `sat` | checked |
| `bezout-identity-replay` | `sat` | checked |
| `divisibility-quotient-replay` | `sat` | checked |
| `diophantine-gcd-obstruction` | `unsat` | checked |

The `sat` rows replay exact integer witnesses. The `unsat` row uses the gcd
divisibility obstruction for one fixed linear Diophantine equation.

## Replay A GCD Table

The gcd witness records:

```text
a = 252
b = 198
gcd = 18
positive common divisors = 1, 2, 3, 6, 9, 18
```

The validator recomputes `gcd(252, 198)` and enumerates the positive common
divisors. The row is accepted only because the listed maximum common divisor
and divisor table agree with exact integer arithmetic.

## Replay Bezout Coefficients

The Bezout witness records:

```text
252*4 + 198*(-5) = 18
```

The validator recomputes the left side:

```text
1008 - 990 = 18
```

It also recomputes the gcd, so the row checks both the equation and the claim
that the equation reaches the gcd.

## Replay A Divisibility Quotient

The divisibility row records:

```text
18 | 252
quotient = 14
```

The trusted replay is direct:

```text
18 * 14 = 252
```

This is the finite witness shape for a divisibility claim.

## Refute A Diophantine Equation

The fixed obstruction row asks for:

```text
6*x + 10*y = 15
```

The trusted check is:

```text
gcd(6, 10) = 2
2 does not divide 15
```

Therefore no integer solution exists. This is the same practical certificate
shape as the integer-LIA gcd obstruction, now presented from the divisibility
side of the curriculum.

## Name The Lean Horizon

The pack does not claim broad number-theory theorems:

```text
unique factorization
infinitely many primes
prime-distribution theorems
```

Those require theorem-prover reconstruction or stronger specialized proof
artifacts. The pack only checks the finite integer evidence it records.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for gcd and divisibility:

```text
untrusted fast search -> gcd, quotient, or Diophantine candidate
trusted small checking -> exact gcd/divisibility arithmetic
```

The graduation route is QF_LIA lowering plus checked `UnsatDiophantine`
evidence for fixed unsolvable linear equations.
