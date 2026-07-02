# SDP Duality Theorem Boundary

This page separates Axeyum's finite SDP resource from general semidefinite
programming weak duality, strong duality, Slater conditions, KKT sufficiency,
complementary-slackness theory, interior-point convergence, and numerical
stability claims.

Primary pack:

- [finite-sdp-v0](../../../artifacts/examples/math/finite-sdp-v0/)

Companion lessons and maps:

- [End To End: Finite SDP Checks](finite-sdp-end-to-end.md)
- [Hyperplane Separation Theorem Boundary](hyperplane-separation-theorem-boundary.md)
- [KKT Sufficiency Theorem Boundary](kkt-sufficiency-theorem-boundary.md)
- [Active-Set Method Theorem Boundary](active-set-method-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational two-by-two SDP witness:

```text
C = [[1, 0],
     [0, 2]]

minimize <C, X>
subject to <I, X> = 1
           X is positive semidefinite
```

The primal matrix is:

```text
X = [[1, 0],
     [0, 0]]
```

The dual witness is:

```text
y = 1
S = C - yI
  = [[0, 0],
     [0, 1]]
```

The validator checks the displayed matrix arithmetic:

```text
primal principal minors = 1, 0, 0
slack principal minors  = 0, 1, 0
<I, X>                  = 1
<C, X>                  = 1
dual objective          = 1
duality gap             = 0
```

Those rows check one finite rational primal/dual certificate. They do not prove
weak duality for arbitrary SDP pairs, strong duality under Slater conditions,
KKT sufficiency for cone programs, or convergence of an SDP algorithm.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `finite-sdp-primal-psd-replay` | `sat` | replay-only | The listed primal matrix is symmetric, PSD by two-by-two principal minors, and satisfies the trace-one constraint. |
| `finite-sdp-objective-replay` | `sat` | replay-only | The Frobenius inner product `<C, X>` is recomputed as `1`. |
| `finite-sdp-dual-slack-replay` | `sat` | replay-only | The slack matrix `C - yI` is recomputed, checked PSD, and paired with zero primal-dual gap. |
| `bad-sdp-objective-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false objective `0` after exact replay computes objective error `1`. |
| `bad-sdp-duality-gap-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false duality gap `1/2` after exact replay computes gap `0`. |
| `bad-sdp-slack-entry-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false bottom-right slack entry `1/2` after exact replay computes `1`. |
| `general-sdp-duality-lean-horizon` | `not-run` | lean-horizon | General SDP duality, Slater conditions, complementary slackness, and KKT sufficiency remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes an
objective error, gap error, or slack-entry error. They are not proofs of SDP
duality theorems.

## What Is Not Proved Yet

The current pack does not prove:

- weak duality for arbitrary primal/dual SDP formulations;
- strong duality under Slater, closedness, compactness, or constraint
  qualification hypotheses;
- cone duality, self-duality of the PSD cone, or separating-hyperplane
  consequences;
- complementary-slackness or KKT sufficiency for arbitrary semidefinite
  programs;
- rank, strict-feasibility, facial-reduction, or degeneracy theory;
- interior-point, active-set, first-order, or augmented-Lagrangian convergence;
- floating-point PSD tests, eigenvalue tolerances, conditioning, or solver
  library behavior.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite SDP rows
are exact examples and regression seeds, not theorem evidence for the general
SDP family.

## Query The Boundary

Find SDP theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text SDP \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked objective, gap, and slack-entry contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --route Farkas \
  --proof-status checked \
  --text objective \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --route Farkas \
  --proof-status checked \
  --text gap \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-sdp-v0 \
  --route Farkas \
  --proof-status checked \
  --text slack \
  --require-any
```

## Graduation Criteria

General SDP resources graduate only when they add:

1. precise Lean theorem statements for SDP weak duality, strong duality,
   Slater-condition consequences, cone duality, or complementary slackness;
2. explicit hypotheses for finite-dimensional symmetric matrices, PSD cones,
   primal/dual feasibility, strict feasibility, closedness, rank conditions, or
   constraint qualifications;
3. no-`sorry` proofs with an axiom audit;
4. links from finite SDP packs to theorem statements as examples, not as proof
   evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, SDP rows remain bounded/computable resources:

```text
untrusted fast search -> proposed primal matrix, dual variable, slack, or malformed claim
trusted small checking -> exact PSD/objective/slack/gap replay and Farkas evidence
theorem horizon       -> SDP weak/strong duality, Slater, cone KKT, convergence, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sdp-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text SDP --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-sdp-duality row remains `lean-horizon`.
