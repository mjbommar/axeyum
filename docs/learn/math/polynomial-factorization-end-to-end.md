# End To End: Rational Polynomial Factorization

This lesson follows one rational-polynomial resource from factor-list replay to
division, Euclidean GCD, square-free decomposition, and a fixed irreducibility
rejection with QF_LRA/Farkas evidence. It uses the
[polynomial-factorization-rational-v0](../../../artifacts/examples/math/polynomial-factorization-rational-v0/)
pack.

Concept rows:

- `curriculum_polynomials`, `curriculum_fields`, and `curriculum_rationals` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra`, `field_real_analysis`, and
  `field_complex_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `factorization-product-replay` | `sat` | replay-only |
| `polynomial-division-replay` | `sat` | checked |
| `euclidean-gcd-replay` | `sat` | checked |
| `square-free-decomposition-replay` | `sat` | checked |
| `irreducible-quadratic-rational-rejected` | `unsat` | checked |
| `irreducible-quadratic-discriminant-conflict` | `unsat` | checked QF_LRA/Farkas |
| `general-factorization-theory-lean-horizon` | `not-run` | lean-horizon |

The pack checks fixed low-degree univariate polynomials over exact rational
coefficients. It does not claim arbitrary-degree factorization theory.

## Replay A Factor List

The product row records:

```text
p(x) = x^4 - 1
factors = (x - 1), (x + 1), (x^2 + 1)
```

The validator multiplies the coefficient lists:

```text
(x - 1)(x + 1)(x^2 + 1) = x^4 - 1
```

and compares normalized rational coefficients.

## Replay Polynomial Division

The division row uses the same polynomial:

```text
(x^4 - 1) / (x - 1) = x^3 + x^2 + x + 1
remainder = 0
```

The trusted check recomputes long division and reconstructs:

```text
divisor * quotient + remainder = original polynomial
```

## Replay A Euclidean GCD

The GCD row records:

```text
left  = x^3 - x
right = x^2 - 1
gcd   = x^2 - 1
```

The validator recomputes the monic Euclidean GCD and checks the listed quotient
divisions:

```text
x^3 - x = x * (x^2 - 1)
x^2 - 1 = 1 * (x^2 - 1)
```

## Replay Square-Free Decomposition

The square-free row records:

```text
p(x) = (x - 1)^2 * (x + 2)
p'(x) = -3 + 3*x^2
gcd(p, p') = x - 1
p / (x - 1) = x^2 + x - 2
```

The validator recomputes the derivative, GCD, and quotient over exact rational
coefficients.

## Reject A Rational Linear Factorization

The irreducibility row is fixed to:

```text
x^2 + 1
```

The validator recomputes the discriminant:

```text
b^2 - 4ac = -4
```

The negative discriminant rejects rational linear factors for this fixed
quadratic.

The promoted solver row then checks the final exact-linear contradiction:

```text
discriminant + 4 = 0
discriminant >= 0
```

That source artifact lives at
`artifacts/examples/math/polynomial-factorization-rational-v0/smt2/irreducible-quadratic-discriminant-farkas-conflict.smt2`.
The route emits and independently rechecks `UnsatFarkas` evidence for the
nonnegative-discriminant conflict.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
Euclidean domains
PIDs and UFDs
Gauss lemma
irreducibility criteria
algebraic closure
complete factorization algorithms over arbitrary fields
```

Those require Lean/mathlib algebra or another kernel-checked proof route. The
pack only checks the finite exact subgoals it records.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-factorization-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes polynomial_factorization_irreducible_quadratic_discriminant_artifact_emits_checked_farkas
```

The validator prints:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current rational-polynomial resource pattern:

```text
untrusted fast search -> factor, quotient, GCD, or irreducibility candidate
trusted small checking -> exact rational coefficient arithmetic, QF_LRA certificate
remaining horizon -> broad algebraic factorization proof reconstruction
```

The graduation route is deterministic exact-rational obligations plus emitted
QF_LRA/Farkas evidence for fixed linear discriminant conflicts, and eventually
QF_NRA/SOS or algebra-specific certificates for broader no-factor rows.
