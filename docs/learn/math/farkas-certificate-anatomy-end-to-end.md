# End To End: Farkas Certificate Anatomy

This lesson follows one exact linear-optimization resource from source claim to
SMT-LIB, emitted Farkas evidence, and corrupted-certificate rejection. It uses
[linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/).

Concept rows:

- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
  in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_optimization_and_convexity`, `field_linear_algebra`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `lp-feasible-point` | `sat` | replay-only |
| `objective-threshold-witness` | `sat` | replay-only |
| `objective-threshold-farkas-infeasible` | `unsat` | checked |

The checked source claim is finite and exact:

```text
The base LP region has a point with objective x + y at least 5.
```

The base region includes the budget constraint `x + y <= 4`, so that threshold
is impossible. The trusted route is not "the solver says impossible"; it is the
source inequalities plus a Farkas certificate that independently checks.

## Source Artifact

The committed SMT-LIB artifact is:

```text
artifacts/examples/math/linear-optimization-v0/smt2/objective-threshold-farkas-conflict.smt2
```

It contains exactly the final linear conflict:

```text
x + y <= 4
x + y >= 5
```

In normalized `<=` form, the second row is:

```text
-x - y <= -5
```

## Farkas Certificate

A Farkas certificate gives nonnegative multipliers for the source inequalities.
For this row, the multipliers are both `1`:

```text
1 * ( x + y <=  4)
1 * (-x - y <= -5)
```

Adding the inequalities cancels the variables:

```text
0 <= -1
```

That contradiction is small enough to check independently over exact rationals.
The search that discovered the contradiction is not the trust anchor.

The promoted resource regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_artifact_emits_checked_farkas
```

That test parses the source SMT-LIB artifact, checks the obligation is `unsat`,
emits `UnsatFarkas` evidence, and runs `Evidence::check` against the original
assertions.

## Corrupted Certificate Rejection

The same source artifact has a tamper regression:

```sh
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_rejects_tampered_farkas_certificate
```

It checks the genuine certificate first, then changes one multiplier to `0`.
With that multiplier removed, the variables no longer cancel and the
certificate must reject. If the tampered certificate still checked, the route
would not be a trustworthy small checker.

## Trust Boundary

Trusted:

- exact parsing of the committed source SMT-LIB artifact;
- pack-local replay of feasible LP witnesses;
- exact-rational Farkas certificate checking against the source assertions;
- rejection of tampered multipliers.

Not trusted by itself:

- the arithmetic search that found the contradiction;
- a Farkas certificate that has not been rechecked;
- future nonlinear, floating-point, or optimization-theorem claims outside the
  exact rational linear fragment.

Remaining horizon:

- primal/dual optimality resources beyond infeasibility;
- general convex duality and KKT theorem proofs;
- numerical optimization claims with floating-point tolerances.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_rejects_tampered_farkas_certificate
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```
