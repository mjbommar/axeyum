# Finite Inversion Geometry Checks

This lesson follows
[finite-inversion-geometry-v0](../../../artifacts/examples/math/finite-inversion-geometry-v0/)
from exact coordinate replay through a checked Farkas contradiction. It is a
finite rational coordinate certificate, not a proof of general inversion
geometry.

## Concept

For inversion in the unit circle centered at the origin:

```text
I(p) = p / |p|^2
```

The resource fixes one rational point so the checker can replay every value
without diagrams, floating-point tolerances, or coordinate-free geometry
assumptions.

## What Gets Checked

| Row | Result | Evidence |
|---|---|---|
| `inversion-image-witness` | `sat` | replay-only |
| `inverse-distance-product-witness` | `sat` | replay-only |
| `inversion-collinearity-witness` | `sat` | replay-only |
| `bad-inversion-image-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-inversion-geometry-lean-horizon` | `not-run` | Lean horizon |

## Inversion Image

The inversion row uses:

```text
C = (0,0)
P = (2,1)
r^2 = 1
```

The validator recomputes:

```text
|P - C|^2 = 2^2 + 1^2 = 5
scale = 1/5
I(P) = (2/5, 1/5)
```

## Distance Product

For unit-circle inversion:

```text
|P|^2 = 5
|I(P)|^2 = (2/5)^2 + (1/5)^2 = 1/5
|P|^2 * |I(P)|^2 = 1
```

The pack checks this exact product for the fixed rational point.

## Collinearity

The center, point, and inverse point are collinear because:

```text
det((2,1), (2/5,1/5)) = 2*(1/5) - 1*(2/5) = 0
```

This is determinant replay, not diagram reasoning.

## Bad Inversion Row

The malformed row claims that the inverse image has x-coordinate `1/2`.
Exact replay computes:

```text
inverse_x = 2/5
```

The source SMT-LIB artifact fixes the replayed value and the malformed value:

```smt2
(set-logic QF_LRA)
(declare-const inverse_x Real)
(assert (= inverse_x (/ 2 5)))
(assert (= inverse_x (/ 1 2)))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## What This Does Not Prove

The pack does not prove general Euclidean inversion theorems. It does not prove
angle preservation, circle-line correspondences, generalized circle inversion,
or power-of-a-point.

Those remain named in the Lean-horizon row:

```text
finite coordinate replay: checked now
general inversion geometry: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-inversion-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_x_artifact_emits_checked_farkas
```
