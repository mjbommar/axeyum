# Number Systems And Arithmetic

Concept rows:

- `curriculum_naturals`, `curriculum_integers`,
  `curriculum_divisibility_and_euclid`, `curriculum_modular_arithmetic`,
  `curriculum_number_theory`, `curriculum_rationals`, and
  `curriculum_complex` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory`, `field_real_analysis`, and `field_complex_analysis`
  in the [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [natural-arithmetic-v0](../../../artifacts/examples/math/natural-arithmetic-v0/)
- [integer-lia-v0](../../../artifacts/examples/math/integer-lia-v0/)
- [gcd-bezout-v0](../../../artifacts/examples/math/gcd-bezout-v0/)
- [modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/)
- [number-theory-v0](../../../artifacts/examples/math/number-theory-v0/)
- [rationals-lra-v0](../../../artifacts/examples/math/rationals-lra-v0/)
- [complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)

## What Axeyum Checks

The arithmetic path starts with exact replay. It checks bounded natural
successor/addition facts, fixed addition and multiplication identities,
bounded Peano-style no-counterexample rows, signed integer order facts, linear
integer equations, interval infeasibility, gcd and Bezout witnesses,
divisibility quotient witnesses, congruences, CRT witnesses, modular inverses,
bounded quadratic-residue and sum-of-two-squares checks, rational density
witnesses, trichotomy and order transitivity fixed cases, and algebraic
complex arithmetic as real-pair data.

These examples are useful because every witness can be evaluated directly with
integer or rational arithmetic.

## Encode / Check Walkthrough

For natural arithmetic, encode successor and bounded identity rows:

```text
5 + S(7) = 13
S(5 + 7) = 13
2 * (3 + 4) = 2*3 + 2*4
```

The `natural-arithmetic-v0` validator replays those rows with exact
nonnegative integer arithmetic and rejects bounded counterexamples to successor
injectivity, a predecessor of zero, and a negative element in `0..7`.

For signed integer arithmetic, encode fixed comparisons and linear equations:

```text
-3 < 4
3*3 - 2*1 = 7
z >= 5 and z <= 2
```

The `integer-lia-v0` validator replays the SAT rows and rejects the impossible
interval and `2*x + 4*y = 3` by exact integer checks. For gcd and divisibility,
encode the integer witness directly:

```text
gcd(252, 198) = 18
252*4 + 198*(-5) = 18
252 = 18 * 14
```

The `gcd-bezout-v0` validator recomputes the gcd, common divisors, Bezout
identity, quotient witness, and the fixed obstruction for `6*x + 10*y = 15`.
For modular arithmetic, encode the witness and its modulus:

```text
x = 8
x == 2 mod 3
x == 3 mod 5
```

The validator checks both congruences and confirms the moduli are coprime. For
the destination number-theory slice, encode bounded residue and square-sum
witnesses:

```text
4^2 == 5 mod 11
65 = 1^2 + 8^2
14*(-1) + 21*1 = 7
```

The `number-theory-v0` pack also rejects `x^2 == 3 mod 7` by enumeration and
rejects `7 = a^2 + b^2` by the fixed mod-4 obstruction. For
rational density, encode `a = 1/3`, `b = 2/3`, and `midpoint = 1/2`; the checker
verifies `a < midpoint < b` and `midpoint = (a + b) / 2`.

For complex arithmetic, encode `1 + 2i` as `[1, 2]` and `3 - i` as `[3, -1]`.
The checker recomputes pair addition and twisted multiplication.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/natural-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/integer-lia-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```

For a fuller trace through exact rational replay, read
[End To End: Rational Midpoint](rational-midpoint-end-to-end.md).

## Horizon

General real completeness, infinite decimal/limit facts, analytic number
theory, algebraic number theory, and the fundamental theorem of algebra are not
claimed by these packs. They need Lean-backed theorem reconstruction or a much
broader theory route.
