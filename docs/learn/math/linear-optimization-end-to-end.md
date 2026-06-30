# End To End: Linear Optimization

This lesson follows one exact linear-optimization resource from feasible points
to objective-threshold replay and checked Farkas evidence. It uses the
[linear-optimization-v0](../../../artifacts/examples/math/linear-optimization-v0/)
pack.

Concept rows:

- `field_optimization_and_convexity`, `field_linear_algebra`, and
  `field_real_analysis` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_linear_algebra`, `curriculum_rationals`, and `curriculum_reals`
  in the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `family_exact_rational_farkas` in the atlas example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `lp-feasible-point` | `sat` | replay-only |
| `objective-threshold-witness` | `sat` | replay-only |
| `objective-threshold-farkas-infeasible` | `unsat` | checked QF_LRA/Farkas |

The pack is an exact-rational LP slice. It checks concrete feasible witnesses
by evaluation and one impossible objective threshold by a small Farkas
certificate. It does not prove linear-programming duality, KKT conditions,
general convex optimization, or numerical optimizer convergence.

## Encode

The base LP has variables `x` and `y` with four inequalities:

```text
x >= 0
y >= 0
x + y <= 4
x + 2y <= 5
```

The first feasible row proposes:

```text
x = 1
y = 2
```

The objective-threshold witness proposes:

```text
x = 3
y = 1
objective = x + y
threshold = 4
```

The infeasible row asks for a stronger threshold:

```text
x + y >= 5
```

while keeping the same base budget constraint:

```text
x + y <= 4
```

## Replay Feasible Points

For `x = 1`, `y = 2`, the checker evaluates each inequality:

```text
x >= 0        -> 1 >= 0
y >= 0        -> 2 >= 0
x + y <= 4    -> 3 <= 4
x + 2y <= 5   -> 5 <= 5
```

For `x = 3`, `y = 1`, the checker verifies both the base constraints and the
objective threshold:

```text
x >= 0        -> 3 >= 0
y >= 0        -> 1 >= 0
x + y <= 4    -> 4 <= 4
x + 2y <= 5   -> 5 <= 5
x + y >= 4    -> 4 >= 4
```

These rows are replay-only: a solver may find the point, but the trusted check
is just exact rational inequality evaluation.

## Check The Refutation

The infeasible threshold row uses the source SMT-LIB artifact
[`objective-threshold-farkas-conflict.smt2`](../../../artifacts/examples/math/linear-optimization-v0/smt2/objective-threshold-farkas-conflict.smt2).
The final conflict is:

```text
x + y <= 4
x + y >= 5
```

In normalized `<=` form, the threshold is:

```text
-x - y <= -5
```

The Farkas multipliers are both `1`:

```text
1 * ( x + y <=  4)
1 * (-x - y <= -5)
```

Adding the two inequalities cancels every variable:

```text
0 <= -1
```

The search that discovers this conflict is untrusted. The accepted evidence is
the exact-rational `UnsatFarkas` certificate checked against the source
assertions, plus a tamper regression that corrupts the multiplier and requires
the checker to reject it.

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

## Trust Boundary

```text
untrusted fast search -> feasible point or Farkas certificate
trusted small checking -> exact inequality replay and exact Farkas arithmetic
remaining horizon -> LP duality, KKT, convex analysis, and numerical convergence
```

For the proof-object anatomy of the same Farkas route, read
[End To End: Farkas Certificate Anatomy](farkas-certificate-anatomy-end-to-end.md).
For the combined matrix/LP bridge, read
[End To End: Linear System And LP Replay](linear-system-end-to-end.md).
