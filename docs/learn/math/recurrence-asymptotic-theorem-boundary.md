# Recurrence And Asymptotic Theorem Boundary

This page separates Axeyum's finite recurrence-prefix resource from general
recurrence solving, closed-form, induction-over-all-`n`, convergence,
stability, and asymptotic theorem claims.

Primary pack:

- [finite-recurrence-prefix-v0](../../../artifacts/examples/math/finite-recurrence-prefix-v0/)

Companion lessons and maps:

- [End To End: Finite Recurrence Prefixes](finite-recurrence-prefix-end-to-end.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack works over displayed finite prefixes. The Fibonacci witness fixes:

```text
F_0 = 0
F_1 = 1
F = [0, 1, 1, 2, 3, 5, 8]
```

The validator checks only the listed steps:

```text
F_2 = F_1 + F_0 = 1
F_3 = F_2 + F_1 = 2
...
F_6 = F_5 + F_4 = 8
```

A second witness checks a finite affine recurrence:

```text
x_0 = 0
x_{n+1} = 2*x_n + 1
x = [0, 1, 3, 7, 15]
```

A third witness checks the same Fibonacci data as fixed matrix-state replay:

```text
A = [[1, 1], [1, 0]]
state_n = [F_{n+1}, F_n]
```

That matrix trace is still finite replay. It is useful as a bridge to linear
algebra and numerical iteration, but it does not prove a closed form or a
theorem over all indices.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `fibonacci-prefix-replay` | `sat` | replay-only | The displayed prefix satisfies the Fibonacci recurrence through `F_6`. |
| `affine-recurrence-prefix-replay` | `sat` | replay-only | The displayed affine prefix satisfies `x_{n+1} = 2*x_n + 1` through four steps. |
| `companion-matrix-prefix-replay` | `sat` | replay-only | The displayed two-dimensional states follow the fixed companion matrix. |
| `bad-fibonacci-value-rejected` | `unsat` | replay-only | Exact replay rejects the false claim `F_6 = 9`; the prefix computes `8`. |
| `qf-lra-bad-fibonacci-value` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated scalar contradiction `F_6 = 8` and `F_6 = 9`. |
| `bad-affine-step-rejected` | `unsat` | replay-only | Exact replay rejects the false claim `x_4 = 14`; the affine prefix computes `15`. |
| `qf-lra-bad-affine-step` | `unsat` | checked | A QF_LRA/Farkas row checks the isolated transition-residual contradiction. |
| `general-recurrence-theory-lean-horizon` | `not-run` | lean-horizon | General recurrence theory remains future proof-assistant work. |

The checked rows are finite scalar contradictions after exact replay computes
the displayed values. They are not proofs of induction schemas, Binet-style
closed forms, generating-function convergence, algorithmic complexity bounds,
or numerical stability.

## What Is Not Proved Yet

The current pack does not prove:

- recurrence laws for all natural numbers;
- induction principles or loop-invariant schemas beyond displayed prefixes;
- closed-form solutions such as Binet's formula;
- recurrence solving for arbitrary linear or nonlinear recurrences;
- asymptotic growth, big-O, or tight runtime bounds;
- convergence or stability of iterative methods;
- generating-function convergence or analytic combinatorics;
- floating-point iteration, conditioning, or numerical stability claims.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. Finite graph-search
runtime counters and generating-function coefficient rows are adjacent bounded
shadows, not proof of asymptotic theorems.

## Query The Boundary

Find recurrence theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text recurrence \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into each checked scalar contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-fibonacci-value \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-recurrence-prefix-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-affine-step \
  --require-any
```

Find the broader finite asymptotic-boundary bridge:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_family_asymptotic_boundary \
  --proof-status checked \
  --require-any
```

## Graduation Criteria

General recurrence and asymptotic resources graduate only when they add:

1. precise Lean theorem statements for induction over all `n`, closed forms,
   recurrence solving, convergence, stability, or asymptotic growth;
2. explicit hypotheses for initial conditions, recurrence class, domain,
   monotonicity, boundedness, spectral radius, or cost model;
3. no-`sorry` proofs with an axiom audit;
4. finite recurrence-prefix packs retained as examples and regression seeds;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, recurrence-prefix rows remain bounded/computable resources:

```text
untrusted fast search -> proposed prefix, matrix trace, cost table, or malformed claim
trusted small checking -> exact finite recurrence replay and Farkas evidence
theorem horizon       -> induction over all n, closed forms, asymptotics, convergence, and stability
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-recurrence-prefix-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text recurrence --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the general
recurrence-theory row remains `lean-horizon`.
