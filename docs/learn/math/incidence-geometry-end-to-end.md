# End To End: Incidence Geometry

This lesson follows
[incidence-geometry-v0](../../../artifacts/examples/math/incidence-geometry-v0/)
from exact line-equation replay to a checked false point-on-line claim. It is a
small coordinate resource for `field_geometry`, not a synthetic geometry
chapter.

Concept rows:

- `field_geometry`, `field_linear_algebra`, and `field_real_analysis` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)
- `bridge_coordinate_orientation_geometry` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `line-equation-through-two-points` | `sat` | replay-only |
| `line-intersection-witness` | `sat` | replay-only |
| `point-on-line-witness` | `sat` | replay-only |
| `bad-incidence-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-incidence-geometry-lean-horizon` | `not-run` | lean-horizon |

Every row uses exact rational coordinates. The pack does not claim projective,
synthetic, or configuration theorems.

## Replay A Line Equation

The line row commits the coefficients:

```text
2x - y + 1 = 0
```

For `(0,1)`:

```text
2*0 - 1 + 1 = 0
```

For `(2,5)`:

```text
2*2 - 5 + 1 = 0
```

The validator accepts the row only after recomputing both values exactly.

## Replay An Intersection

The intersection row uses:

```text
x + y - 3 = 0
x - y - 1 = 0
```

The determinant of the coefficient matrix is:

```text
1*(-1) - 1*1 = -2
```

Since the determinant is nonzero, the two lines are not parallel. The listed
point `(2,1)` is checked by direct substitution into both equations.

## Reject A False Incidence Claim

The bad row reuses the line:

```text
2x - y + 1 = 0
```

At `(2,2)`, exact replay gives:

```text
2*2 - 2 + 1 = 3
```

The malformed claim says the point lies on the line, so it requires the same
line value to equal `0`. The SMT-LIB artifact isolates exactly that conflict:

```text
line_value = 3
line_value = 0
```

Axeyum must emit `Evidence::UnsatFarkas`, and the independent evidence checker
must accept it. This keeps the untrusted coordinate encoding separate from the
trusted small certificate check.

## Horizon

This resource does not prove:

- projective duality;
- Desargues, Pappus, Pascal, or Brianchon-style theorems;
- synthetic diagram reasoning;
- incidence theorems over arbitrary fields or projective planes.

Those belong in Lean-backed geometry resources or in explicitly scoped
algebraic proof-certificate routes.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/incidence-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes incidence_geometry_bad_point_on_line_artifact_emits_checked_farkas
```

## Axeyum Identity

```text
untrusted fast search -> candidate line equations and point-incidence claims
trusted small checking -> exact rational replay plus QF_LRA/Farkas certificate
remaining horizon -> general synthetic and projective geometry proofs
```
