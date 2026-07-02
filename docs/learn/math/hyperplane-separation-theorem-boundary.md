# Hyperplane Separation Theorem Boundary

This page separates Axeyum's finite hyperplane-separation resource from
general convex-separation, Farkas-duality, Hahn-Banach, SDP-duality, and
optimization theorem claims.

Primary pack:

- [finite-separation-v0](../../../artifacts/examples/math/finite-separation-v0/)

Companion lessons and maps:

- [End To End: Finite Hyperplane Separation](finite-separation-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack works over one exact rational triangle:

```text
v0 = (0, 0)
v1 = (1, 0)
v2 = (0, 1)
weights = (1/3, 1/3, 1/3)
point = (1/3, 1/3)
```

The validator checks the finite convex-combination witness:

```text
weights are nonnegative
sum(weights) = 1
sum_i weights_i * v_i = (1/3, 1/3)
```

The separator witness is also fixed:

```text
normal = (1, 1)
threshold = 1
outside_point = (2, 2)
vertex_scores = [0, 1, 1]
outside_score = 4
margin = 3
tight_indices = [1, 2]
```

The validator checks only that displayed finite hull point, dot-product table,
outside-point margin, and supporting face. It does not prove that arbitrary
convex sets can be separated.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `convex-combination-replay` | `sat` | replay-only | The displayed point is the listed convex combination of the triangle vertices. |
| `separating-hyperplane-replay` | `sat` | replay-only | The displayed hyperplane separates this finite triangle from `(2,2)`. |
| `supporting-face-replay` | `sat` | replay-only | The listed tight indices are exactly the finite face supported by `x + y = 1`. |
| `bad-convex-combination-point-rejected` | `unsat` | replay-only | Exact replay rejects the false point `(1/2, 1/3)` and computes x-error `1/6`. |
| `qf-lra-bad-convex-combination-point` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated contradiction `point_x_error = 1/6` and `point_x_error = 0`. |
| `bad-separator-rejected` | `unsat` | replay-only | Exact replay rejects the false bound `outside_score <= 1` after computing `outside_score = 4`. |
| `qf-lra-bad-separator` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated contradiction `outside_score = 4` and `outside_score <= 1`. |
| `general-separation-theorem-lean-horizon` | `not-run` | lean-horizon | General separation and duality theorems remain future proof-assistant work. |

The checked rows are small exact-linear contradictions after replay computes
the finite point or score. They are not proofs of strict or weak separation for
general convex sets, Farkas theorem, Hahn-Banach, supporting-hyperplane
theorems, SDP strong duality, KKT sufficiency, or convergence of optimization
algorithms.

## What Is Not Proved Yet

The current pack does not prove:

- separation for arbitrary finite-dimensional convex sets;
- strict separation, weak separation, or supporting-hyperplane theorems;
- closedness, compactness, nonempty-interior, or disjointness side conditions;
- Farkas theorem or alternative-theorem equivalences;
- Hahn-Banach or infinite-dimensional functional separation;
- cone duality, SDP strong duality, or Slater-condition consequences;
- KKT sufficiency, active-set correctness, or optimization convergence;
- numerical robustness, conditioning, or floating-point behavior.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. Finite separator
rows may become examples or regression seeds for those theorem routes, but
they are not theorem evidence by themselves.

## Query The Boundary

Find separation theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text separation \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-separation-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-separation-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-separation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-convex-combination-point \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-separation-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-separator \
  --require-any
```

## Graduation Criteria

General separation and duality resources graduate only when they add:

1. precise Lean theorem statements for finite-dimensional strict/weak
   separation, supporting hyperplanes, Farkas alternatives, cone duality, or
   Hahn-Banach-style functional separation;
2. explicit hypotheses for convexity, closedness, compactness, nonempty
   interior, disjointness, affine hull, finite dimensionality, cone closure,
   or Slater-style regularity;
3. no-`sorry` proofs with an axiom audit;
4. links from finite separator packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, separation rows remain bounded/computable resources:

```text
untrusted fast search -> proposed hull point, separator, face, or malformed claim
trusted small checking -> exact rational replay and Farkas evidence
theorem horizon       -> convex separation, Farkas theorem, Hahn-Banach, duality, and optimization theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-separation-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text separation --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-separation-theorem row remains `lean-horizon`.
