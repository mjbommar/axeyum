# Lane uf-front-door-census — a cause for UF's 32 reference-only losses

<!-- plan-section: lane-status -->

Status: **complete.** Cause measured, the obvious lever built and refuted,
two levers recommended with scoring populations and exit criteria.

Plan anchor: `docs/plan/families/smt-quantified/uf.md` (its Cause and Lever
sections are updated by this lane).
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

## Finding 2 — the cause, and the lever test that refuted the obvious one

Full note:
[the front-door census](../../research/11-design-review/2026-09-06-uf-front-door-census.md).
Per-file artifacts in `bench-results/parity-losses-20260906/`.

- **50.4% of the loss population's wall (347.0 s of 688.0 s) is spent in the
  pure-UF finite-model finder**, on 32 files every one of which is `unsat`. A
  finite-model rung is the budget-dominant stage on 16 of the 32.
- **25 of 32 saturate `MAX_GROUND_TERMS = 8192`**; the 7 `search-timeout` files
  spend 3.1–21.2 s inside the untraced cap-hit refutation check at
  `qinst_egraph.rs:1341`.
- **11 of 32 return with 5–19 s of the 24 s budget unspent**, all of them
  `route-decline(residual-quantifier)`: out of routes, not out of time.
  **6 overshoot**, one to 62 866 ms.
- **The reallocation lever was built and refuted**: probe budget `t/2` → `t/16`
  decides 0 of the 32 and costs 1 of the 24 axeyum-only wins.
- **The 24 wins are the finite-model finder and nothing else**: gated off, 22 of
  24 become `unknown`. 21 of 24 decide in 1.1 s or less.

## Gates and what did not run

- `./scripts/check-links.sh` — all links ok.
- No Rust in the tree was changed by this lane. The two measurement patches
  (`bench-results/parity-losses-20260906/measurement-patch-*.py`) are applied to
  a throwaway snapshot only, and are committed so the A/B is reproducible.
  Cross-check that they are inert when ungated: the s6 patched binary with no
  env set and the s7 unpatched binary agree on verdict **and** detail for 32 of
  32.
- **Did not run:** the full 200-file `bench-results/parity-lists/UF.txt` sweep;
  any workspace cargo gate (no compiled code changed); the `MAX_GROUND_TERMS`
  A/B; instrumentation of which chains overflow `CHAIN_INSTANCE_CAP`.

## Landed changes

| Commit | What |
|---|---|
| `2da495b0b` | Lane status, method, and the population framing |
| `ea61aeb80` | First ten files classified through the front door |
| `5483ceb12` | All 32 classified; the 50.4% finite-model finding |
| `a9aa0c557` | The 24 axeyum-only wins A/B; the finder is their sole producer |
| (this) | The loss A/B, the design-review note, and `uf.md`'s Cause and Lever |
