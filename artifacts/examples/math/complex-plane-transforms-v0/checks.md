# Checks

## `unit-root-cycle-replay`

Expected result: `sat`.

The validator recomputes the powers of `i` and checks the cycle
`1, i, -1, -i, 1`. It also checks that each non-final listed power has
norm-squared `1`.

## `conjugation-product-replay`

Expected result: `sat`.

The validator recomputes `z*w`, `conjugate(z*w)`, and
`conjugate(z)*conjugate(w)` for a fixed pair of complex numbers.

## `bad-conjugation-product-imaginary-rejected`

Expected result: `unsat`.

The validator replays the same fixed pair and computes
`conjugate(z*w) = conjugate(z)*conjugate(w) = 5 - 5i`. The malformed row claims
that the imaginary part is `5`; the source QF_LRA artifact shifts both sides by
`+5` and isolates `computed_imaginary_part_plus_five = 0`,
`claimed_imaginary_part_plus_five = 10`, and equality between them for Farkas
checking.

## `mobius-transform-witness`

Expected result: `sat`.

The validator checks the rational transform `(z - 1) / (z + 1)` at
`z = 2 + i`, including the nonzero denominator, exact quotient, and
image norm-squared.

## `bad-unit-square-real-part-rejected`

Expected result: `unsat`.

The validator rejects the false claim that every square of a unit complex
number has positive real part. The counterexample is `i^2 = -1`; after
real-pair replay, the final contradiction is checked through QF_LRA/Farkas
evidence.

The source SMT-LIB artifact records:

```text
negated_real_part = 1
negated_real_part < 0
```

The `math_resource_lra_routes` regression parses
`smt2/bad-unit-square-real-part-farkas-conflict.smt2`, emits `UnsatFarkas`
evidence, and independently checks the certificate.

## `general-complex-analysis-lean-horizon`

Expected result: `not-run`.

Holomorphic functions, contour integrals, residues, analytic continuation, and
the fundamental theorem of algebra belong in a future Lean-backed resource.
The finite rows above are exact algebraic replay checks only.
