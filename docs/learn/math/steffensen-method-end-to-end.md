# End To End: Finite Steffensen Method

This lesson follows one numerical-analysis resource from exact fixed-point
acceleration replay through a replayed bad source claim and a separate checked
Farkas proof row. It uses the
[finite-steffensen-method-v0](../../../artifacts/examples/math/finite-steffensen-method-v0/)
pack.

Concept rows:

- `curriculum_sequences_and_limits`, `curriculum_reals`, and
  `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_numerical_analysis` and `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_sequence_tail_shadow`,
  `bridge_bounded_family_asymptotic_boundary`, and
  `bridge_exact_vs_floating_arithmetic` in the atlas bridge vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `steffensen-half-step-exact-witness` | `sat` | replay-only |
| `steffensen-third-step-exact-witness` | `sat` | replay-only |
| `steffensen-residual-improvement-witness` | `sat` | replay-only |
| `bad-steffensen-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-steffensen-value` | `unsat` | checked QF_LRA/Farkas |
| `general-steffensen-method-theory-lean-horizon` | `not-run` | Lean horizon |

Every positive row is one finite exact-rational calculation. The pack does not
prove that Steffensen acceleration converges for every fixed-point map, that a
fixed point exists, that the denominator stays nonzero, or that a
floating-point implementation is stable.

## Replay The Transform

For a listed affine fixed-point map `g`, Steffensen's method uses two ordinary
fixed-point iterates and then applies a delta-squared correction:

```text
x1         = g(x0)
x2         = g(x1)
delta0     = x1 - x0
delta1     = x2 - x1
delta2     = delta1 - delta0
correction = delta0^2 / delta2
x_hat      = x0 - correction
```

The validator recomputes each value over exact rationals and rejects a row if
the second difference is zero.

## Half-Step Row

The first witness uses:

```text
g(x) = (x + 1)/2
x0 = 0
x1 = 1/2
x2 = 3/4
```

Then:

```text
delta0 = 1/2
delta1 = 1/4
delta2 = -1/4
correction = (1/4) / (-1/4) = -1
x_hat = 1
```

The listed fixed-point residual also improves on this fixed row:

```text
|g(3/4) - 3/4| = 1/8
|g(1) - 1| = 0
0 < 1/8
```

This row is a finite exact replay. It is useful because an affine contraction
is the smallest fixed-point shape where Steffensen acceleration has a clear
arithmetic story, but the row itself is not a theorem.

## Third-Step Row

The second witness uses:

```text
g(x) = 1 + (x - 1)/3
x0 = 4
x1 = 2
x2 = 4/3
```

Then:

```text
delta0 = -2
delta1 = -2/3
delta2 = 4/3
correction = 4 / (4/3) = 3
x_hat = 1
```

That is another finite affine fixed-point replay, not a convergence theorem for
arbitrary nonlinear maps.

## Replay The Bad Source Row

The malformed source row claims:

```text
half-step row accelerated value = 3/2
```

Exact replay computes:

```text
half-step row accelerated value = 1
```

That replay row is not the proof object. It computes the source value and
leaves the certificate route to `qf-lra-bad-steffensen-value`.

## Check The Refutation

The committed SMT-LIB artifact
[`bad-steffensen-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-steffensen-method-v0/smt2/bad-steffensen-value-farkas-conflict.smt2)
records the tiny contradiction:

```text
steffensen_value = 1
steffensen_value = 3/2
```

Axeyum may search for the contradiction, but the accepted evidence is checked
`UnsatFarkas` arithmetic over the original source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-steffensen-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_steffensen_method_bad_value_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed accelerated value, residual comparison, or Farkas certificate
trusted small checking -> exact rational fixed-point replay plus checked QF_LRA evidence
remaining horizon -> fixed-point existence, convergence acceleration, denominator safety, floating-point stability
```

Use this page after
[End To End: Finite Aitken Acceleration](aitken-acceleration-end-to-end.md) or
near [End To End: Finite Root Finding](finite-root-finding-end-to-end.md).
All three resources illustrate the same rule: finite iteration arithmetic can
be checked today, while general convergence and numerical-stability claims need
separate theorem or numerical-honesty routes.
