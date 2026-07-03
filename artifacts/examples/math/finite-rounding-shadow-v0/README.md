# Finite Rounding Shadow Checks

This pack is for learners and solver contributors who need a tiny exact
example of the boundary between rational arithmetic and rounded numerical
arithmetic. It uses a fixed three-decimal rounding grid as a finite numerical
shadow. It does not model IEEE floating-point, machine exceptions, subnormals,
or a general roundoff theorem.

The fixed transcript is:

```text
x = 1
y = 1/10000

exact_sum   = x + y = 10001/10000
exact_delta = exact_sum - x = 1/10000
```

On a three-decimal grid with scale `1000`, nearest-grid replay rounds:

```text
round3(x)         = 1
round3(y)         = 0
round3(exact_sum) = 1
```

So the rounded increment after summing is:

```text
round3(exact_sum) - round3(x) = 0
```

The trusted checker recomputes:

- the exact rational sum and exact increment;
- the three-decimal scale and nearest-grid residuals;
- the rounded increment after summing;
- the exact difference between the exact and rounded increments;
- a malformed equality claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove a hardware floating-point result or numerical
stability theorem. It only checks this fixed rational transcript and keeps the
broader floating-point route as future QF_FP or numerical-honesty work.

## Concept Rows

- `curriculum_rationals`
- `curriculum_reals`
- `field_real_analysis`
- `field_numerical_analysis`
- `bridge_exact_vs_floating_arithmetic`

## Trust Boundary

```text
untrusted fast search -> candidate exact/rounded arithmetic claim
trusted small checking -> exact rational replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-rounding-shadow-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_rounding_shadow_bad_rounded_delta_artifact_emits_checked_farkas
```
