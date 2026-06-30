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
- [complex-plane-transforms-v0](../../../artifacts/examples/math/complex-plane-transforms-v0/)

## What Axeyum Checks

The arithmetic path starts with exact replay. It checks bounded natural
successor/addition facts, fixed addition and multiplication identities,
bounded Peano-style no-counterexample rows, signed integer order facts, linear
integer equations, interval infeasibility, gcd and Bezout witnesses,
divisibility quotient witnesses, congruences, CRT witnesses, modular inverses,
bounded quadratic-residue and sum-of-two-squares checks, rational density
witnesses, Farkas-checked fixed trichotomy and order-transitivity refutations,
and algebraic complex arithmetic as real-pair data. The complex-plane pack adds
unit-root cycles, conjugation/product replay, exact rational Mobius transforms,
and a checked counterexample to a false unit-complex-square claim.

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
injectivity, a predecessor of zero, and a negative element in `0..7`. The
negative-domain row now also emits checked QF_LIA arithmetic-DPLL evidence from
the same `0 <= n <= 7` and `n < 0` contradiction.

For signed integer arithmetic, encode fixed comparisons and linear equations:

```text
-3 < 4
3*3 - 2*1 = 7
z >= 5 and z <= 2
```

The `integer-lia-v0` validator replays the SAT rows and rejects the impossible
interval by exact integer checks. Its `2*x + 4*y = 3` row now also emits a
checked QF_LIA/Diophantine certificate through the shared LIA resource
regression. For gcd and divisibility, encode the integer witness directly:

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
the nonunit inverse row, the pack also encodes `2*b == 1 mod 6` as
`2*b - 6*k = 1` and checks the Diophantine gcd obstruction. For the destination
number-theory slice, encode bounded residue and square-sum witnesses:

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
For a complex-plane transform, encode `z = 2 + i` as `[2, 1]` and replay:

```text
T(z) = (z - 1) / (z + 1) = 2/5 + (1/5)i
```

The `complex-plane-transforms-v0` validator recomputes the numerator,
denominator, denominator norm, division result, and a checked counterexample
using `i^2 = -1`.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/natural-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/integer-lia-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-plane-transforms-v0
```

For fuller traces through bounded natural arithmetic, signed integer LIA,
gcd/Bezout replay, modular congruence replay, bounded number theory, exact
rational replay, complex real-pair replay, prime-field residue replay, and
modular quotient-ring replay, read
[End To End: Natural Arithmetic](natural-arithmetic-end-to-end.md),
[End To End: Integer Linear Arithmetic](integer-lia-end-to-end.md),
[End To End: GCD And Bezout](gcd-bezout-end-to-end.md),
[End To End: Modular Arithmetic](modular-arithmetic-end-to-end.md),
[End To End: Bounded Number Theory](number-theory-end-to-end.md),
[End To End: Complex Algebraic Replay](complex-algebraic-end-to-end.md),
[End To End: Complex Plane Transforms](complex-plane-transforms-end-to-end.md),
[End To End: Rational Midpoint](rational-midpoint-end-to-end.md),
[End To End: Finite Fields](finite-fields-end-to-end.md), and
[End To End: Finite Ideals And Quotient Rings](finite-ideals-quotient-rings-end-to-end.md)
with a checked QF_UF/Alethe bad-ideal row.

## Horizon

General real completeness, infinite decimal/limit facts, analytic number
theory, algebraic number theory, and the fundamental theorem of algebra are not
claimed by these packs. They need Lean-backed theorem reconstruction or a much
broader theory route.
