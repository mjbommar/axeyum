# Number Systems And Arithmetic

Concept rows:

- `curriculum_modular_arithmetic`, `curriculum_rationals`, and
  `curriculum_complex` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory`, `field_real_analysis`, and `field_complex_analysis`
  in the [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

Example packs:

- [modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/)
- [rationals-lra-v0](../../../artifacts/examples/math/rationals-lra-v0/)
- [complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)

## What Axeyum Checks

The arithmetic path starts with exact replay. It checks congruences, CRT
witnesses, modular inverses, rational density witnesses, trichotomy and order
transitivity fixed cases, and algebraic complex arithmetic as real-pair data.

These examples are useful because every witness can be evaluated directly with
integer or rational arithmetic.

## Encode / Check Walkthrough

For modular arithmetic, encode the witness and its modulus:

```text
x = 8
x == 2 mod 3
x == 3 mod 5
```

The validator checks both congruences and confirms the moduli are coprime. For
rational density, encode `a = 1/3`, `b = 2/3`, and `midpoint = 1/2`; the checker
verifies `a < midpoint < b` and `midpoint = (a + b) / 2`.

For complex arithmetic, encode `1 + 2i` as `[1, 2]` and `3 - i` as `[3, -1]`.
The checker recomputes pair addition and twisted multiplication.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```

## Horizon

General real completeness, infinite decimal/limit facts, analytic number
theory, algebraic number theory, and the fundamental theorem of algebra are not
claimed by these packs. They need Lean-backed theorem reconstruction or a much
broader theory route.
