# Martingale Theorem Boundary

This page is a trust-boundary note for learners, proof contributors, solver
contributors, and downstream consumers. It explains what Axeyum's finite
martingale resource checks today, and what remains a theorem-prover horizon.

Primary pack:

- [finite-martingales-v0](../../../artifacts/examples/math/finite-martingales-v0/)

Companion lessons and maps:

- [End To End: Finite Martingales](finite-martingales-end-to-end.md)
- [Probability And Statistics](probability-and-statistics.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack works over a two-step finite probability space:

```text
P(uu) = P(ud) = P(du) = P(dd) = 1/4

F0 = {uu, ud, du, dd}
F1 = {uu, ud}, {du, dd}
F2 = {uu}, {ud}, {du}, {dd}
```

The fair-walk process is:

```text
M0 = 0
M1(up) = 1
M1(down) = -1
M2(uu), M2(ud), M2(du), M2(dd) = 2, 0, 0, -2
```

The validator checks finite partitions, adaptedness, conditional expectations,
square-submartingale inequalities, and a bounded stopping-time replay by exact
rational arithmetic.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `finite-martingale-witness` | `sat` | replay-only | The table is adapted and satisfies finite martingale equalities. |
| `square-submartingale-witness` | `sat` | replay-only | The square process satisfies finite submartingale inequalities. |
| `bounded-stopping-replay` | `sat` | replay-only | The capped first-hit stopping time has `E[M_tau] = E[M0] = 0`. |
| `bad-stopped-expectation-rejected` | `unsat` | replay-only | Exact replay rejects the false claim `E[M_tau] = 1/2`. |
| `qf-lra-bad-stopped-expectation` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated scalar contradiction. |
| `bad-martingale-rejected` | `unsat` | replay-only | Exact replay rejects a malformed terminal table whose up-block conditional expectation is `3/2`, not `1`. |
| `qf-lra-bad-martingale` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated conditional-expectation contradiction. |
| `general-martingale-lean-horizon` | `not-run` | lean-horizon | General martingale theorems remain future Lean work. |

The checked rows are finite scalar contradictions after replay has recomputed
the mathematical quantities. They are not proofs of general stochastic-process
theorems.

## What Is Not Proved Yet

The following stay out of the checked finite resource:

- martingale convergence theorems;
- optional stopping for arbitrary stopping times;
- Doob maximal and submartingale inequalities;
- uniform integrability and other side conditions;
- stochastic integration;
- Brownian motion, semimartingales, SDEs, and continuous-time martingales;
- simulation, floating-point, or sampling-quality claims.

Those require theorem statements with explicit hypotheses and no-`sorry` Lean
proofs before they can graduate from horizon rows.

## Query The Boundary

Find martingale theorem-horizon rows and the finite shadows beside them:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text martingale \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-stopped-expectation \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-martingale \
  --require-any
```

## Graduation Criteria

General martingale resources graduate only when they add:

1. precise Lean theorem statements for the target theorem family;
2. explicit probability-space, filtration, adaptedness, integrability,
   stopping-time, boundedness, or uniform-integrability hypotheses;
3. no-`sorry` proofs with an axiom audit;
4. finite packs retained only as examples and regression seeds;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, the finite martingale rows remain bounded/computable resources:

```text
untrusted fast search -> candidate filtration, process, stopping time, or malformed row
trusted small checking -> exact finite partitions, rational averages, and Farkas evidence
theorem horizon       -> general martingale and stochastic-process theory
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text martingale --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --proof-status lean-horizon --require-any
```

Expected resource boundary: the finite pack validates, the `horizon-frontier`
query shows `checked-finite-shadow`, and the general theorem row remains
`lean-horizon`.
