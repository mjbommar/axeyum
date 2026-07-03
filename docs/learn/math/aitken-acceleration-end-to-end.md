# End To End: Finite Aitken Acceleration

This lesson follows one numerical-analysis resource from exact sequence
acceleration replay through a replayed bad source claim and a separate checked
Farkas proof row. It uses the
[finite-aitken-acceleration-v0](../../../artifacts/examples/math/finite-aitken-acceleration-v0/)
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
| `aitken-geometric-exact-witness` | `sat` | replay-only |
| `aitken-harmonic-improvement-witness` | `sat` | replay-only |
| `aitken-residual-improvement-witness` | `sat` | replay-only |
| `bad-aitken-value-rejected` | `unsat` | replay-only |
| `qf-lra-bad-aitken-value` | `unsat` | checked QF_LRA/Farkas |
| `general-aitken-acceleration-theory-lean-horizon` | `not-run` | Lean horizon |

Every positive row is one finite exact-rational calculation. The pack does not
prove that Aitken acceleration improves every convergent sequence, that the
denominator stays nonzero, or that a floating-point implementation is stable.

## Replay The Transform

Aitken's delta-squared transform for three listed terms is:

```text
delta0      = s1 - s0
delta1      = s2 - s1
delta2      = delta1 - delta0
correction  = delta0^2 / delta2
accelerated = s0 - correction
```

The validator recomputes each value over exact rationals and rejects a row if
the second difference is zero.

## Geometric Error Row

The first witness uses:

```text
s0 = 2
s1 = 3/2
s2 = 5/4
```

Then:

```text
delta0 = -1/2
delta1 = -1/4
delta2 = 1/4
correction = (1/4) / (1/4) = 1
accelerated = 1
```

This row is a finite exact replay. It is useful because a pure geometric error
pattern is the textbook shape where the transform can recover the limit in one
step, but the row itself is not a theorem.

## Harmonic Tail Row

The second witness uses:

```text
s0 = 2
s1 = 3/2
s2 = 4/3
```

Then:

```text
delta0 = -1/2
delta1 = -1/6
delta2 = 1/3
correction = (1/4) / (1/3) = 3/4
accelerated = 5/4
```

Against the listed target `1`, the pack checks only the finite residual
comparison:

```text
|4/3 - 1| = 1/3
|5/4 - 1| = 1/4
1/4 < 1/3
```

That does not prove an asymptotic acceleration theorem.

## Replay The Bad Source Row

The malformed source row claims:

```text
geometric row accelerated value = 3/2
```

Exact replay computes:

```text
geometric row accelerated value = 1
```

That replay row is not the proof object. It computes the source value and
leaves the certificate route to `qf-lra-bad-aitken-value`.

## Check The Refutation

The committed SMT-LIB artifact
[`bad-aitken-value-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-aitken-acceleration-v0/smt2/bad-aitken-value-farkas-conflict.smt2)
records the tiny contradiction:

```text
aitken_value = 1
aitken_value = 3/2
```

Axeyum may search for the contradiction, but the accepted evidence is checked
`UnsatFarkas` arithmetic over the original source artifact.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-aitken-acceleration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_aitken_acceleration_bad_value_artifact_emits_checked_farkas
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> proposed accelerated value, residual comparison, or Farkas certificate
trusted small checking -> exact rational delta-squared replay plus checked QF_LRA evidence
remaining horizon -> convergence acceleration, denominator safety, order theory, floating-point stability
```

Use this page after
[End To End: Sequence Limit Shadows](sequence-limit-shadow-end-to-end.md) or
near [End To End: Finite Romberg Extrapolation](romberg-extrapolation-end-to-end.md).
Both resources illustrate the same rule: finite extrapolation arithmetic can be
checked today, while general convergence and numerical-stability claims need
separate theorem or numerical-honesty routes.
