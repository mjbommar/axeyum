# Number Systems And Arithmetic

Concept rows:

- `curriculum_naturals`, `curriculum_integers`,
  `curriculum_divisibility_and_euclid`, `curriculum_modular_arithmetic`,
  `curriculum_number_theory`, `curriculum_rationals`, and
  `curriculum_complex` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `bridge_totality_conventions` and
  `bridge_exact_vs_floating_arithmetic`, plus
  `bridge_gcd_divisibility_witness` and
  `bridge_modular_crt_inverse_witness`, in the
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
checked incompatible CRT obstructions, checked fixed-width nonunit-inverse and
Fermat-unit residue searches, bounded quadratic-residue and
sum-of-two-squares checks, bounded Diophantine witnesses and gcd obstructions,
rational density witnesses, Farkas-checked
fixed trichotomy and order-transitivity refutations, and algebraic complex
arithmetic as real-pair data. The complex-plane pack adds
unit-root cycles, conjugation/product replay, exact rational Mobius transforms,
and checked counterexamples to false conjugation-product and
unit-complex-square claims.

These examples are useful because every witness can be evaluated directly with
integer or rational arithmetic.

## Semantic Boundaries

The arithmetic examples are deliberately exact. Natural, integer, modular, and
rational rows name their finite domain, modulus, bit width, or nonzero side
condition instead of hiding it in solver behavior. In Axeyum's core, operators
are total over their sort; for example, fixed-width BV division and shifts
follow the SMT-LIB conventions in
[BV Semantics And Partial Operations](../../research/01-foundations/bv-semantics-and-partial-operations.md).
If a frontend wants Rust panics, C undefined behavior, trapping division, or a
partial mathematical function, it must encode that guard as an ordinary claim.

Likewise, rational rows are not floating-point experiments. They teach exact
arithmetic and certificate replay; roundoff, tolerances, conditioning, and
stability need a separate numerical-honesty or QF_FP route before they become
checked claims.

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
Those rows now share the `bridge_gcd_divisibility_witness` concept: the small
checked object is the gcd computation or gcd non-divisibility certificate, not
a broad number-theory theorem.
For modular arithmetic, encode the witness and its modulus:

```text
x = 8
x == 2 mod 3
x == 3 mod 5
```

The validator checks both congruences and confirms the moduli are coprime. For
the nonunit inverse row, the pack also encodes `2*b == 1 mod 6` as
`2*b - 6*k = 1` and checks the Diophantine gcd obstruction. For the
incompatible CRT row, it derives `4*a - 6*b = 1` from `x == 1 mod 4` and
`x == 2 mod 6`, then checks that `gcd(4,6)` does not divide `1`. The composite
nonunit inverse and Fermat-style rows also have QF_BV/DRAT twins: for the
nonunit row, a 3-bit residue `b < 6` is zero-extended before asserting
`(2*b) mod 6 = 1`; for the Fermat row, a 3-bit residue `a` with `0 < a < 5` is
extended to 9 bits before asserting `a^4 mod 5 != 1`. Both bit-blasted CNF
refutations are checked by DRAT replay. These rows now share the
`bridge_modular_crt_inverse_witness` concept: the small checked object is the
listed congruence, inverse, finite residue search, fixed-width BV proof, or gcd
obstruction, not the full Chinese remainder theorem or arbitrary field theory.
For the destination number-theory slice, encode bounded residue and square-sum
witnesses:

```text
4^2 == 5 mod 11
65 = 1^2 + 8^2
14*(-1) + 21*1 = 7
```

The `number-theory-v0` pack also rejects `x^2 == 3 mod 7` by enumeration and
now also promotes that nonresidue row to a QF_BV bit-blast/DRAT regression:
`x` is a 3-bit residue with `x < 7`, `x*x` is computed at 6-bit width, and
`x^2 mod 7 = 3` is refuted by a checked DIMACS/DRAT pair. It rejects
`7 = a^2 + b^2` by the fixed mod-4 obstruction. For rational density, encode
`a = 1/3`, `b = 2/3`, and `midpoint = 1/2`; the checker verifies
`a < midpoint < b` and `midpoint = (a + b) / 2`.

For complex arithmetic, encode `1 + 2i` as `[1, 2]` and `3 - i` as `[3, -1]`.
The checker recomputes pair addition and twisted multiplication.
For a complex-plane transform, encode `z = 2 + i` as `[2, 1]` and replay:

```text
T(z) = (z - 1) / (z + 1) = 2/5 + (1/5)i
```

The `complex-plane-transforms-v0` validator recomputes the numerator,
denominator, denominator norm, division result, conjugation-product replay, and
checked counterexamples using `conjugate(z*w) = conjugate(z)*conjugate(w) =
5 - 5i` and `i^2 = -1`. The upgraded bad rows send exact-linear conflicts
through checked `UnsatFarkas` evidence.

Run the checks from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/natural-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/integer-lia-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/gcd-bezout-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
cargo test -p axeyum-solver --test math_resource_lia_routes modular_nonunit_inverse_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test math_resource_bv_routes modular_arithmetic_fermat_units_mod5_emits_checked_bv_drat
cargo test -p axeyum-solver --test math_resource_lia_routes qf_lia_resource_route_rejects_tampered_diophantine_certificate
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
cargo test -p axeyum-solver --test math_resource_lra_routes complex_algebraic_bad_product_real_part_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes complex_algebraic_bad_norm_squared_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-plane-transforms-v0
cargo test -p axeyum-solver --test math_resource_lra_routes complex_plane_bad_unit_square_real_part_artifact_emits_checked_farkas
```

For fuller traces through bounded natural arithmetic, signed integer LIA,
gcd/Bezout replay, modular congruence replay, bounded number theory, exact
rational replay, complex real-pair replay with a checked bad norm-squared
certificate, prime-field residue replay, and
modular quotient-ring replay, read
[End To End: Natural Arithmetic](natural-arithmetic-end-to-end.md),
[End To End: Integer Linear Arithmetic](integer-lia-end-to-end.md),
[End To End: GCD And Bezout](gcd-bezout-end-to-end.md),
[End To End: Modular Arithmetic](modular-arithmetic-end-to-end.md),
[End To End: Diophantine Certificate Anatomy](diophantine-certificate-anatomy-end-to-end.md),
[End To End: Bounded Number Theory](number-theory-end-to-end.md),
[End To End: Complex Algebraic Replay](complex-algebraic-end-to-end.md),
[End To End: Complex Plane Transforms](complex-plane-transforms-end-to-end.md),
[Complex Analysis Theorem Boundary](complex-analysis-theorem-boundary.md),
[End To End: Rational Midpoint](rational-midpoint-end-to-end.md),
[End To End: Finite Fields](finite-fields-end-to-end.md), and
[End To End: Finite Ideals And Quotient Rings](finite-ideals-quotient-rings-end-to-end.md)
with replayed bad-ideal rejection plus a separate checked QF_UF/Alethe
bad additive-closure row.

## Horizon

General real completeness, infinite decimal/limit facts, analytic number
theory, algebraic number theory, and the fundamental theorem of algebra are not
claimed by these packs. They need Lean-backed theorem reconstruction or a much
broader theory route.
For the focused complex-number and complex-analysis boundary, read
[Complex Analysis Theorem Boundary](complex-analysis-theorem-boundary.md).
