# End To End: Finite Secant Method

This lesson follows one numerical-analysis resource from exact secant-step
replay through a replayed bad source claim and a separate checked Farkas proof
row. It uses the
[finite-secant-method-v0](../../../artifacts/examples/math/finite-secant-method-v0/)
pack.

Concept rows:

- `curriculum_calculus`, `curriculum_polynomials`, `curriculum_reals`, and
  `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_numerical_analysis` and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_exact_vs_floating_arithmetic` and
  `bridge_bounded_family_asymptotic_boundary` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `secant-first-step-replay` | `sat` | replay-only |
| `secant-second-step-replay` | `sat` | replay-only |
| `secant-residual-decrease-witness` | `sat` | replay-only |
| `bad-secant-step-rejected` | `unsat` | replay-only |
| `qf-lra-bad-secant-step` | `unsat` | checked QF_LRA/Farkas |
| `general-secant-method-theory-lean-horizon` | `not-run` | Lean horizon |

Every positive row is one finite exact-rational calculation. The pack does not
prove that the secant method converges, that its denominator stays nonzero, or
that a floating-point implementation is stable.

## Replay The First Secant Step

Encode the polynomial:

```text
f(x) = x^2 - 2
```

The first witness uses `x0 = 1` and `x1 = 2`:

```text
f(1) = -1
f(2) = 2
value_delta = 2 - (-1) = 3
```

The secant update is:

```text
x_next = x1 - f(x1) * (x1 - x0) / (f(x1) - f(x0))
       = 2 - 2 * (1) / 3
       = 4/3
```

The validator recomputes both polynomial values, checks the nonzero finite
difference denominator, recomputes the correction `2/3`, and evaluates:

```text
f(4/3) = -2/9
```

## Replay The Second Secant Step

The second witness uses `x0 = 4/3` and `x1 = 3/2`:

```text
f(4/3) = -2/9
f(3/2) = 1/4
value_delta = 17/36
```

The exact correction is:

```text
(1/4) * (1/6) / (17/36) = 3/34
```

So the next point is:

```text
3/2 - 3/34 = 24/17
```

The replay row checks only this fixed step.

## Check The Residual

The same second witness records:

```text
|f(3/2)| = 1/4
|f(24/17)| = 2/289
```

The pack checks the finite inequality:

```text
2/289 < 1/4
```

That is useful evidence for one exact row, but it is not a convergence-order
theorem.

## Replay The Bad Source Row

The malformed source row claims:

```text
secant step from 1 and 2 is 3/2
```

Exact replay computes:

```text
secant step from 1 and 2 is 4/3
```

That replay row is not the proof object. It computes the source value and
leaves the certificate route to `qf-lra-bad-secant-step`.

## Check The Refutation

The committed SMT-LIB artifact
[`bad-secant-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-secant-method-v0/smt2/bad-secant-step-farkas-conflict.smt2)
records the tiny contradiction:

```text
secant_next = 4/3
secant_next = 3/2
```

Axeyum may search for the contradiction, but the accepted evidence is checked
`UnsatFarkas` arithmetic over the original source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-secant-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_secant_method_bad_step_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed secant iterates, residuals, or Farkas certificate
trusted small checking -> exact polynomial evaluation, exact secant-step replay, checked QF_LRA evidence
remaining horizon -> root existence, denominator safety, convergence order, floating-point stability
```

Use this page after
[End To End: Finite Root Finding](finite-root-finding-end-to-end.md) or before
[End To End: Finite Newton Step](newton-step-end-to-end.md). The three pages
share the same exact-iteration trust boundary while keeping convergence theory
outside the finite replay rows.
