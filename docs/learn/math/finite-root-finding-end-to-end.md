# End To End: Finite Root Finding

This lesson follows one numerical-analysis resource from exact iterate replay
through a checked bad-step rejection. It uses the
[finite-root-finding-v0](../../../artifacts/examples/math/finite-root-finding-v0/)
pack.

Concept rows:

- `curriculum_reals`, `curriculum_polynomials`, and `curriculum_calculus` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_numerical_analysis`, `field_real_analysis`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_bounded_theorem_shadow` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `bisection-bracket-replay` | `sat` | replay-only |
| `newton-step-replay` | `sat` | replay-only |
| `residual-decrease-witness` | `sat` | replay-only |
| `bad-newton-step-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-root-finding-convergence-lean-horizon` | `not-run` | Lean horizon |

Every positive row is one finite exact-rational calculation. The pack does not
prove that a root exists in every interval, that Newton converges, or that a
floating-point implementation is stable.

## Replay A Bisection Step

Encode the polynomial:

```text
f(x) = x^2 - 2
```

The witness uses the interval `[1,2]`:

```text
f(1) = -1
f(2) = 2
midpoint = 3/2
f(3/2) = 1/4
```

The validator checks the midpoint, recomputes every polynomial value, verifies
the strict sign change on `[1,2]`, and checks that the selected interval is the
sign-changing half:

```text
[1, 3/2]
```

It also checks that the interval width changed from `1` to `1/2`.

## Replay A Newton Step

For the same polynomial:

```text
f'(x) = 2*x
x_0 = 3/2
f(x_0) = 1/4
f'(x_0) = 3
```

The Newton update is:

```text
x_1 = x_0 - f(x_0) / f'(x_0)
    = 3/2 - (1/4)/3
    = 17/12
```

The validator recomputes the derivative coefficients, evaluates `f` and `f'`
at the listed point, checks that the derivative is nonzero, and checks the
listed next iterate.

## Check The Residual

The same witness records:

```text
|f(3/2)| = 1/4
|f(17/12)| = 1/144
```

The pack checks only this fixed residual decrease:

```text
1/144 < 1/4
```

That is useful evidence for one exact step, but it is not a convergence-rate
theorem.

## Check The Refutation

The promoted bad row claims:

```text
Newton step from 3/2 is 4/3
```

Exact replay computes:

```text
Newton step from 3/2 is 17/12
```

The committed SMT-LIB artifact
[`bad-newton-step-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-root-finding-v0/smt2/bad-newton-step-farkas-conflict.smt2)
records the tiny contradiction:

```text
newton_next = 17/12
newton_next = 4/3
```

Axeyum may search for the contradiction, but the accepted evidence is checked
`UnsatFarkas` arithmetic over the original source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-root-finding-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_root_finding_bad_newton_step_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed bracket, iterate, residual, or Farkas certificate
trusted small checking -> exact polynomial evaluation, exact step replay, checked QF_LRA evidence
remaining horizon -> root existence, uniqueness, convergence rates, floating-point stability
```

Use this page after
[End To End: Finite Recurrence Prefixes](finite-recurrence-prefix-end-to-end.md)
or before numerical-method examples that need exact finite iteration traces
without pretending they prove general convergence theory.
