# Synthetic graduated corpus (neutral, status-by-construction)

Committed, **generated** SMT-LIB v2 benchmarks for *neutral, graduated*
head-to-head measurement of `axeyum_solver::check_auto` against Z3 on the
nonlinear divisions **QF_NRA** and **QF_NIA**.

## Why this exists

[`PLAN.md`](../../../PLAN.md)'s course correction (2026-06-23) and its
"methodology lesson" flag that competitor regress slices (cvc5/bitwuzla
`test/regress`) are **solver-flavored, easy, and depth-hiding** — so a "parity"
number measured on them is not honest, and a low decide-rate gap is invisible.

This corpus is the opposite: it is **generator-built, neutral** (no
competitor-specific options/logics), and **graduated** (a difficulty knob per
family), so the measurement reveals *gradual depth* — the largest knob axeyum
decides — instead of a binary "both trivially solve".

Crucially, **every file's `(set-info :status …)` is established by
construction**, independent of any solver:

- **SAT** files carry an explicit witness that the generator verifies with exact
  integer/rational arithmetic *before emission* (a generation run aborts on a bad
  witness). A `:status sat` is therefore a checkable fact.
- **UNSAT** files encode an infeasibility with an elementary independent
  argument (sum-of-squares positivity, even-power non-negativity, infinite
  descent for `x²=2y²`, or an enumerated quadratic-non-residue table).

Because the status does not depend on Z3, a **DISAGREE** in measurement (axeyum
decides ≠ Z3, or ≠ `:status`) is a genuine solver bug — in axeyum *or* Z3 — not a
mislabeled file. DISAGREE=0 is both the soundness gate and the bug-detector.

## Generator

[`scripts/gen-graduated-nra-nia.py`](../../../scripts/gen-graduated-nra-nia.py)
emits the corpus deterministically:

```sh
python3 scripts/gen-graduated-nra-nia.py
```

Output: 33 QF_NRA files + 32 QF_NIA files under `QF_NRA/graduated/` and
`QF_NIA/graduated/`. Each file name carries a trailing zero-padded knob
(`…-k07`, `…-d04`, `…-n08`) so the harness can compute a per-family
**DECIDE-FRONTIER** (largest knob decided).

## Families and status provenance

### QF_NRA (real nonlinear)

| family | status | knob | how status is known (by construction) |
|---|---|---|---|
| `nra-sat-witness-kNN` | sat | var count k=1..8 | rational witness `xi=i/(i+1)` substituted; `sum(xi²)=S` checked exactly by the generator |
| `nra-sos-unsat-kNN` | unsat | var count k=1..8 | `x1²+…+xk²+1 < 0` is impossible: LHS ≥ 1 > 0 (sum-of-squares positivity) |
| `nra-neg-square-dNN` | unsat | even degree 2d=2..12 | `x^(2d) < 0` is impossible: even power ≥ 0 |
| `nra-sos-strict-unsat-dNN` | unsat | even degree 2d=2..10 | `(x-1)^(2d)+(y-2)^(2d)+1 < 0` is impossible (sum of even powers +1 ≥ 1) |
| `nra-circle-line-mNN` | sat | Pythagorean-triple scale | witness `(a,b)` on `x²+y²=c²` (a Pythagorean triple) and on a line through it; checked exactly |

### QF_NIA (integer nonlinear)

| family | status | knob | how status is known (by construction) |
|---|---|---|---|
| `nia-pythagorean-mNN` | sat | triple scale m=1..8 | witness `(3m,4m,5m)` for `x²+y²=z²`, `1≤·≤5m`; checked |
| `nia-product-kNN` | sat | prime-pair index 1..8 | witness `(p,q)` for `x·y=p·q`, `2≤·≤max(p,q)`; checked |
| `nia-sum-sq-2-nNN` | unsat | bound N=4..32 | `x²=2y²`, `1≤x,y≤N`: `√2` irrational ⇒ no positive-integer solution (infinite descent), bounded so QF |
| `nia-no-square-mod-bNN` | unsat | bound mult b=1..8 | `x²=m·t+r` with `r` a quadratic **non-residue** mod `m`; the full residue table `{i² mod m}` is enumerated by the generator to confirm `r∉` it before emission |

The whole status set was additionally cross-checked against `z3 -T:25`: **0 of 65
files disagreed** with the by-construction `:status` (a second independent
oracle confirming the labels).

## Measurement harness

[`crates/axeyum-bench/examples/measure_graduated.rs`](../../../crates/axeyum-bench/examples/measure_graduated.rs)
shells the system `z3` binary (handles QF_NRA/QF_NIA natively) and times
axeyum's `check_auto` on the same files, reporting decided counts, agreement
against **both** `:status` and Z3, DISAGREE, PAR-2, and the per-family
DECIDE-FRONTIER:

```sh
cargo build --release -p axeyum-bench --example measure_graduated
target/release/examples/measure_graduated \
  corpus/public-curated/synthetic/QF_NRA/graduated 30000 \
  bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json
target/release/examples/measure_graduated \
  corpus/public-curated/synthetic/QF_NIA/graduated 30000 \
  bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json
```

## Measured baselines (30 s, axeyum vs z3 4.13.3 — DISAGREE=0)

Artifacts:
[`bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json`](../../../bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json),
[`bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json`](../../../bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json).

**QF_NRA** — considered 33, axeyum decided **30** (sat 14, unsat 16, unknown 3),
z3 decided 33, agree 30, **DISAGREE 0**. PAR-2 axeyum 5.45 s vs z3 0.01 s.
Decide-frontier: sat-witness 8/8, sos-unsat 8/8, neg-square 6/6, circle-line 6/6,
**sos-strict-unsat 2/5** (the only NRA family with a gap — high-degree shifted
sum-of-squares; degrees 6/8/10 return `unknown`).

**QF_NIA** — considered 32, axeyum decided **16** (sat 16, unsat 0, unknown 16),
z3 decided 32, agree 16, **DISAGREE 0**. PAR-2 axeyum 36.74 s vs z3 0.12 s.
Decide-frontier: pythagorean 8/8, product 8/8 (both SAT families fully decided),
but **sum-sq-2 0/8 and no-square-mod 0/8** — axeyum returns `unknown` on every
bounded integer-nonlinear *infeasibility*. This is an honest measured gap (the
NIA decider does not yet refute these), never a wrong verdict.

A low/partial decide-rate is expected and fine. The deliverable is a **neutral,
graduated, by-construction** number with **DISAGREE=0** — and a frontier that
pinpoints exactly where each decider stops.
