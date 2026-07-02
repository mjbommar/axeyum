# Active-Set Method Theorem Boundary

This page separates Axeyum's finite active-set QP resource from general
active-set method correctness, finite termination, anti-cycling,
degeneracy-handling, convergence, warm-start, and numerical-stability theorem
claims.

Primary pack:

- [finite-active-set-qp-v0](../../../artifacts/examples/math/finite-active-set-qp-v0/)

Companion lessons and maps:

- [End To End: Finite Active-Set QP Checks](finite-active-set-qp-end-to-end.md)
- [KKT Sufficiency Theorem Boundary](kkt-sufficiency-theorem-boundary.md)
- [Hyperplane Separation Theorem Boundary](hyperplane-separation-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The main witness fixes one two-variable quadratic program:

```text
f(x,y) = (x - 2)^2 + (y - 1)^2
x <= 1
y >= 0
```

The unconstrained minimizer is `(2,1)`, but it violates `x <= 1` by one unit.
The finite active-face witness fixes:

```text
active face: x = 1
candidate: (1,1)
objective: 1
gradient: (-2,0)
active multiplier: 2
inactive multiplier: 0
inactive lower-bound slack: 1
stationarity residual: (0,0)
```

The degenerate witness fixes another quadratic:

```text
g(x,y) = (x - 1)^2 + y^2
x <= 1
candidate: (1,0)
active multiplier: 0
stationarity residual: (0,0)
```

Those rows check displayed active-set arithmetic. They do not prove that an
active-set algorithm finds the active set, terminates, avoids cycling, or
converges on arbitrary quadratic programs.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `unconstrained-minimizer-replay` | `sat` | replay-only | The unconstrained minimizer and active-bound violation are recomputed exactly. |
| `active-face-candidate-replay` | `sat` | replay-only | Fixing `x = 1` gives the listed active-face candidate `(1,1)`. |
| `active-set-kkt-replay` | `sat` | replay-only | The listed active and inactive multipliers satisfy finite KKT stationarity and complementarity. |
| `inactive-constraint-slack-replay` | `sat` | replay-only | The lower-bound constraint is inactive at `(1,1)` with slack `1` and multiplier `0`. |
| `bad-inactive-slack-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that the inactive lower-bound constraint is tight. |
| `bad-active-set-free-gradient-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false active-face candidate `(1,0)`, where free-coordinate stationarity error is `2`. |
| `degenerate-active-bound-replay` | `sat` | replay-only | A tight active bound can have zero multiplier when the gradient is already zero. |
| `bad-degenerate-active-multiplier-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects a false positive multiplier at the degenerate active bound. |
| `general-active-set-method-lean-horizon` | `not-run` | lean-horizon | Active-set algorithm theory remains future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a slack
or stationarity error. They are not proofs of the active-set method.

## What Is Not Proved Yet

The current pack does not prove:

- correctness of active-set algorithms for arbitrary convex QPs;
- finite termination under nondegeneracy assumptions;
- anti-cycling rules or pivot-selection correctness;
- degeneracy handling beyond the displayed zero-multiplier witness;
- equality-constrained solve correctness for arbitrary working sets;
- convergence rates, warm-start behavior, or sensitivity theory;
- relationship to interior-point, SQP, projected-gradient, or proximal methods;
- floating-point conditioning, tolerances, or solver-library behavior.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite pack is
valuable because it supplies small exact witnesses and malformed-row
regressions, not because it proves the algorithmic theorem.

## Query The Boundary

Find active-set theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text active-set \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked slack, free-gradient, and degeneracy rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --text inactive \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --text free-gradient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-active-set-qp-v0 \
  --route Farkas \
  --proof-status checked \
  --text degenerate \
  --require-any
```

## Graduation Criteria

General active-set resources graduate only when they add:

1. precise Lean theorem statements for active-set correctness, working-set
   pivot validity, finite termination, or degeneracy handling;
2. explicit hypotheses for convexity, positive semidefinite or positive
   definite Hessians, linear constraints, nondegeneracy, constraint
   qualifications, pivot rules, and stopping criteria;
3. no-`sorry` proofs with an axiom audit;
4. links from finite active-set packs to theorem statements as examples, not
   as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, active-set rows remain bounded/computable resources:

```text
untrusted fast search -> proposed working set, face solution, slack, multiplier, or malformed claim
trusted small checking -> exact active-face/KKT/slack replay and Farkas evidence
theorem horizon       -> active-set correctness, finite termination, degeneracy, cycling, convergence, and numerical stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-active-set-qp-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text active-set --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-active-set-method row remains `lean-horizon`.
