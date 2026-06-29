# End To End: Real Algebra RCF Shadow

This lesson follows one real-algebra resource from exact rational witnesses to
two tiny real-closed-field-style infeasibility checks. It uses the
[reals-rcf-shadow-v0](../../../artifacts/examples/math/reals-rcf-shadow-v0/)
pack.

Concept rows:

- `curriculum_reals`, `curriculum_rationals`, and `curriculum_polynomials` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_real_analysis` and `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `ordered-field-midpoint-witness` | `sat` | replay-only |
| `nra-product-threshold-witness` | `sat` | replay-only |
| `quadratic-root-real-witness` | `sat` | replay-only |
| `square-nonnegative-unsat` | `unsat` | checked |
| `negative-discriminant-no-real-root` | `unsat` | checked |
| `real-completeness-lean-horizon` | `not-run` | lean-horizon |

The pack is a small algebraic shadow of real-closed-field reasoning. It is not
a CAD engine, SOS checker, or real-analysis library.

## Replay An Ordered-Field Witness

The midpoint row records:

```text
left = 1
right = 2
midpoint = 3/2
```

The validator checks:

```text
1 < 3/2 < 2
3/2 = (1 + 2) / 2
```

This is the same ordered-field shape as a rational density witness, now marked
as a real-algebra row.

## Replay A Nonlinear Product Witness

The nonlinear row records:

```text
x = 3/2
y = 4/3
x >= 1
y >= 1
x*y = 2
```

The validator recomputes the exact product and confirms the threshold
constraint. This is witness replay for one nonlinear arithmetic formula.

## Replay A Quadratic Root

The root row records the polynomial:

```text
p(x) = 9/4 - 3*x + x^2
root = 3/2
```

The validator evaluates:

```text
9/4 - 3*(3/2) + (3/2)^2 = 0
```

So the listed rational value is a real root of the fixed quadratic.

## Check Two Tiny Unsat Certificates

The square row asks for:

```text
x^2 < 0
```

The trusted checker recognizes the fixed square-nonnegative shape and rejects
the row.

The quadratic row asks for:

```text
x^2 + 1 = 0
```

The validator computes the discriminant:

```text
b^2 - 4ac = 0 - 4 = -4
```

A negative discriminant certifies that this quadratic has no real root.

## Name The Lean Horizon

The final row records the theorem-prover boundary:

```text
least-upper-bound completeness
epsilon-delta limits over real numbers
```

Those are not consequences of the finite algebraic rows. They require Lean
artifacts or another kernel-checked proof route.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current real-algebra resource pattern:

```text
untrusted fast search -> rational real witness or tiny algebraic UNSAT claim
trusted small checking -> exact Fraction replay, square/nonnegative shape, discriminant check
remaining horizon -> CAD/SOS/RCF certificates and Lean completeness theorems
```

The graduation route is deterministic NRA polynomial constraints plus checked
SOS/RCF-style evidence for nonlinear `unsat` rows.
