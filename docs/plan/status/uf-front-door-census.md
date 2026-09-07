# Lane uf-front-door-census — a cause for UF's 32 reference-only losses

<!-- plan-section: lane-status -->

Status: **in progress.** Population framing measured and committed; the
per-file front-door trace is running.

Plan anchor: `docs/plan/families/smt-quantified/uf.md` (Cause: unknown).
Predecessors: the [S3 census](../../research/11-design-review/2026-09-05-parity-loss-census.md)
(class refuted) and [S11a](s11a-uf-ackermann-cap.md) (which refuted it).

## Method, fixed before the run

1. **Front door only.** Classification comes from `solve_smtlib`
   (`uf_unknown_probe`) with `AXEYUM_QTRACE=1`, never from `explain_corpus`,
   which runs `check_auto_explained` on the flat assertion view and is measured
   to disagree with the front door on 134 of 397 committed benchmarks.
2. **Classify by the stage that spent the budget**, computed from the qtrace
   timeline — not by the terminal message.
   `crates/axeyum-solver/src/auto.rs::qtrace` prints `since.elapsed()`, and
   `finish_quantified_solve` passes **one shared `t0`** to
   `forall-exists-witness`, `finite-expansion`, `uf-fmf-probe`, `egraph`,
   `mbqi` and `uf-fmf-full`. Those six numbers are **cumulative**, so a stage's
   own cost is the difference from the previous line. Only `mbqi-quick` carries
   a stage-local `t0`. Reading a printed `+N s` as one stage's cost overstates
   it by everything above it.
3. **Every diagnostic invocation is wrapped in an external `timeout`.**
4. Measurement host s7 (idle, load 0.14, 16 cores), `taskset -c 0-7`, 24 s
   budget, release binary from a `git archive --touch` snapshot of `cc75cd023`.

## Finding 1 — the loss population is 100% refutation, and that alone
## refutes the finite-model-finding hypothesis

From `bench-results/parity-details/UF.tsv` at parity run 2026-09-06T22:35:13Z
(solver commit `c28d7b7c65`), the 200-file division splits:

| axeyum | cvc5 | declared | files |
|---|---|---|---:|
| unsolved | unsolved | unknown | 77 |
| **unsat** | **unsat** | unsat | **61** |
| **unsolved** | **unsat** | unsat | **30** |
| **sat** | unsolved | sat | **20** |
| unsolved | unsolved | unsat | 4 |
| unsolved | unsolved | sat | 2 |
| **unsolved** | **unsat** | unknown | **2** |
| **unsat** | unsolved | unsat | **2** |
| **sat** | unsolved | unknown | **2** |

- **All 32 reference-only losses are cvc5 `unsat`.** Not one is a satisfiable
  query. Bounded finite-model finding — the August gap analysis's named UF
  lever — searches for a model; it cannot close an unsat file. The hypothesis is
  refuted by the population, before any trace is read.
- **22 of the 24 axeyum-only wins are `sat`**, and there is **no sat/sat cell at
  all**: every satisfiable UF file this division decides, only we decide. Our
  UF strength is model finding; our UF weakness is refutation.
- The two columns are drawn from the **same benchmark families** — FFT,
  Fundamental_Theorem_Algebra, Hoare, Arrow_Order, TypeSafe, coinductive_list
  all appear on both sides — so the split is by satisfiability, not by source.

## What is still running

The per-file qtrace census of the 32 (class, budget-spending stage, dominant
stage, wall, evidence line) → `bench-results/parity-losses-20260906/UF.front-door.census.tsv`.

## Landed changes

| Commit | What |
|---|---|
| (this) | Lane status, method, and the population framing |
