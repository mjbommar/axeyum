# Root-Finding Convergence Theorem Boundary

This page separates Axeyum's finite root-finding resource from root-existence,
uniqueness, bisection convergence, Newton convergence, error-rate, and
floating-point stability theorem claims.

Primary pack:

- [finite-root-finding-v0](../../../artifacts/examples/math/finite-root-finding-v0/)

Companion lessons and maps:

- [End To End: Finite Root Finding](finite-root-finding-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)

## Current Finite Resource

The pack works over displayed exact rational data for `f(x) = x^2 - 2`.
The bisection witness fixes:

```text
left = 1
right = 2
midpoint = 3/2
f(left) = -1
f(midpoint) = 1/4
f(right) = 2
selected interval = [1, 3/2]
selected width = 1/2
```

The Newton witness fixes:

```text
current = 3/2
f(current) = 1/4
f'(current) = 3
next = current - f(current)/f'(current) = 17/12
f(next) = 1/144
```

Those are finite algorithm rows. They are useful regression seeds for
polynomial evaluation, exact rational arithmetic, derivative replay, and
malformed-claim rejection, but they do not prove that either method converges.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `bisection-bracket-replay` | `sat` | replay-only | The displayed interval update is one exact bisection step for `x^2 - 2`. |
| `newton-step-replay` | `sat` | replay-only | The displayed Newton update from `3/2` computes `17/12`. |
| `residual-decrease-witness` | `sat` | replay-only | This one Newton step decreases the listed exact residual from `1/4` to `1/144`. |
| `bad-newton-step-rejected` | `unsat` | replay-only | Exact replay rejects the false claim that the next Newton iterate is `4/3`. |
| `qf-lra-bad-newton-step` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated contradiction `newton_next = 17/12` and `newton_next = 4/3`. |
| `bad-bisection-width-rejected` | `unsat` | replay-only | Exact replay rejects the false claim that the selected interval has width `1/3`; it computes `1/2`. |
| `qf-lra-bad-bisection-width` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated width-excess contradiction. |
| `general-root-finding-convergence-lean-horizon` | `not-run` | lean-horizon | Root-finding convergence, existence, uniqueness, rates, and floating-point stability remain future theorem/numerical-honesty work. |

The checked rows are small scalar contradictions after exact replay computes
the displayed iterate or interval width. They are not proofs of the
intermediate value theorem, bisection convergence, Newton local convergence,
quadratic convergence, basin-of-attraction facts, or implementation-level
floating-point behavior.

## What Is Not Proved Yet

The current pack does not prove:

- existence of a root in every sign-changing interval;
- uniqueness of the root in an interval;
- bisection convergence for arbitrary continuous functions;
- Newton local or global convergence;
- linear, superlinear, or quadratic convergence rates;
- derivative nonzero, Lipschitz, convexity, or monotonicity side conditions
  beyond the displayed row;
- stopping criteria, certified error bounds, or interval enclosure theorems;
- floating-point roundoff, conditioning, stability, or library behavior;
- a general polynomial-root theorem or real-completeness dependency.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts, plus numerical-honesty metadata for any floating-point run,
before they can graduate from horizon rows.

## Query The Boundary

Find root-finding theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text root-finding \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-newton-step \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-root-finding-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-bisection-width \
  --require-any
```

## Graduation Criteria

General root-finding resources graduate only when they add:

1. precise Lean theorem statements for IVT/root existence, uniqueness,
   bisection convergence, Newton convergence, convergence rates, and error
   bounds;
2. explicit hypotheses for continuity, sign-changing intervals, differentiable
   neighborhoods, nonzero derivatives, simple roots, Lipschitz or convexity
   conditions, interval containment, and precision models;
3. no-`sorry` proofs with an axiom audit;
4. numerical-honesty metadata for floating-point implementations, including
   rounding model, precision, reproducibility, and failure modes;
5. finite root-finding packs retained as examples and regression seeds;
6. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, root-finding rows remain bounded/computable resources:

```text
untrusted fast search -> proposed iterate, bracket, residual, or malformed claim
trusted small checking -> exact rational replay and Farkas evidence
theorem horizon       -> root existence, uniqueness, convergence, rates, and floating-point stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-root-finding-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text root-finding --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-root-finding row remains `lean-horizon`.
