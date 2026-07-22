# SMT-COMP Full-Library Work Stream — RESUME HERE

**This folder is the single entry point to resume the SMT-COMP measurement /
full-library inventory / gap-closing work stream.** Paused 2026-07-22.

Read this file top to bottom; every artifact and open thread is linked below.

---

## 1. What this work stream is

Build a faithful, in-tree replica of the **entire SMT-COMP scoring pipeline**,
run **axeyum against the whole SMT-LIB library** to get an honest per-logic
decide/decline/**wrong** map, and turn the measured gaps into a **rank-ordered
plan** to close the distance to Z3/cvc5/Bitwuzla. It also surfaced a **P0
floating-point soundness bug** and produced a merge that needs finishing.

The rank-ordered plan this feeds:
[`../full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md).

---

## 2. Current-state snapshot (2026-07-22, at pause)

### ⚠️ Blockers to know before touching anything
- **`main` is RED (does not compile).** `crates/axeyum-solver/src/reconstruct/quantifier.rs:537`
  has a non-exhaustive match — the Lean lane added `ExprNode::Proj`
  (`axeyum-lean-kernel/src/expr.rs:162`) but never committed the match arm.
  This was a **pre-existing broken commit on the Lean lane** (repro didn't
  compile either); a merge of `repro/smtcomp-scoring` into `main` carried it
  over. **Not lost work, not a bad merge — one missing match arm.** Fix belongs
  to the Lean lane (correct `Proj` handling) or a sound-decline stopgap.
- **Do not `git reset`/`revert` the merge blindly** — the CAS agent has live
  uncommitted WIP in the `main` worktree (`/nas4/.../claude-axeyum-cas-work`);
  a hard reset would destroy it. `main` and `repro` are both advancing under
  other agents. Any reconciliation must be coordinated when worktrees are quiet.
- **The running s4 binary is STALE (pre-FP-fix).** The staged
  `/nas3/data/axeyum/harness/bin/axeyum-smtcomp` predates the FP soundness fix,
  so its `WRONG` count keeps rising on FP benchmarks. **The measured decide/wrong
  numbers from this run are provisional** until re-staged with the fixed binary.

### Live s4 run
- Config: SMT-COMP §6 selection (64,345 files, seed `20260721`), 300 s ceiling,
  **s4 only, N=8** thread-pinned (thermal-safe — the fleet cooks at 92–99 °C
  under full load; see gotchas). Distributed launcher: `scripts/smtcomp_repro/distribute_run.sh`.
- Progress at pause: **~30 % (≈19.5k/64,345), WRONG=2** (both FP-family,
  stale binary). Outputs on NAS: `/nas3/data/axeyum/harness/full-inventory/raw_selection/`
  (`log_0..7.log`, `raw_*.json` on shard completion).
- **Monitor lapsed** — no live WRONG alarm. On resume, re-arm a `WRONG` grep
  over the shard logs.

### Git
- Work committed on `repro/smtcomp-scoring` (the shared checkout at
  `/home/mjbommar/projects/personal/axeyum`); merged into `main` (`87ff5335`+).
- ~32 uncommitted files in this checkout = other lanes' live WIP (FP fix, Lean
  fixtures, `STATUS.md`, frontier JSONs) — **not ours to commit.**

---

## 3. DONE (with artifact paths)

- **Scoring-pipeline replica** — full SMT-COMP §7 scoring (all 5 tracks,
  sequential, division parallel/PAR-2/sequential/24s/sat/unsat, disagreement
  removal, Best-Overall/Biggest-Lead/Largest-Contribution rankings) + §6
  selection + §5 resource-limited execution. **40+ unit tests.**
  → `scripts/smtcomp_repro/{scoring,runner,selection,smtlib_meta,compete,inventory,select_library}.py`,
  `tests/`.
- **Competition CLI** (argv1 `.smt2` → `sat`/`unsat`/`unknown`) →
  `crates/axeyum-bench/examples/smtcomp_cli.rs`.
- **Distributed runner + clean-stop** (shard across s-hosts; kill children not
  just parents to avoid orphan runaways) →
  `scripts/smtcomp_repro/{distribute_run.sh,stop_run.sh}`.
- **Full SMT-LIB 2024 fetched to NAS** — non-incremental **438,631** +
  incremental **44,333** → `/nas3/data/axeyum/corpus/smtlib-2024/`.
- **228-file pilot inventory** (complete, charted, 0 wrong) →
  `bench-results/smtcomp-repro-20260721/` (README, JSON, PNG charts, `chart.py`).
- **Rank-ordered gap-closing plan** →
  `docs/plan/full-library-gap-closing-plan-2026-07-22.md`.
- **SMT-COMP 2024 reference numbers gathered** (QF_BV 98 %, QF_ABV 99.7 %,
  QF_LIA 94 %, QF_FP 92 %, UFLIA best 57 %) — inline in the plan.
- **P0 FP wrong-`sat` found + isolated** — QF_ABVFP/QF_BVFP KLEE `query.26`,
  `(fp.add roundTowardNegative …)`; repro preserved →
  `bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/`.
  **Root-cause fixed locally by the FP lane** (exact-zero sign under directed
  rounding, add + fma); full-slice revalidation still open (see §4).

---

## 4. IN PROGRESS / BLOCKED

| Item | State | Owner / next |
|---|---|---|
| **`main` red — `ExprNode::Proj` match arm** | blocked | Lean lane commits the arm, or add a sound-decline stopgap; then main compiles |
| **The merge (`repro`→`main`)** | landed but on a red tree | finish once the arm lands; reconcile when CAS/Lean worktrees quiet |
| **s4 §6 run** | ~30 %, running, **stale binary** | let finish OR re-stage fixed binary and restart for trustworthy numbers |
| **P0 FP fix revalidation** | fix local; not slice-revalidated | re-run QF_FP/QF_BVFP/QF_ABVFP selected slices → DISAGREE 0 |
| **Branch/worktree topology** | tangled (repro vs main, 321 behind) | coordinated reconcile onto main (user-directed) |

---

## 5. REMAINING (rank-ordered — see the plan for detail)

From [`../full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md) §3:

0. **Fix P0 FP wrong-`sat`** + revalidate (soundness floor). *(fix landed; revalidate)*
1. **Finish the measurement** — restart s4 run with the FIXED binary; on
   completion run `inventory.py` → dated `bench-results/` record + charts;
   feeds G1/G2/G3 of [`../gap-analysis-z3-lean-2026-07-21.md`](../gap-analysis-z3-lean-2026-07-21.md).
2. **Strings** (QF_SLIA+QF_S ≈ 103k benchmarks, weak decide) — P2.7.
3. **Quantifier sat-direction / MBQI (T2.6.5) + MAM (T2.6.1)** — biggest
   capability gap (>100k quantified at ~0 %) — P2.6, gated on e-graph+CDCL(T).
4. **CDCL(T) keystone migration** — P1.4/P1.5.
5. **Nonlinear NIA/NRA frontier** — P2.5.
6. **QF_BV/FP hard-tail perf** — P1.1/P1.2 measure-and-flip.
7. **Proof/Lean denominator** — G5/G6.
8. **Breadth backlog** — P2.10 (deferred).

---

## 6. Artifacts & locations (the full map)

**Repo (`/home/mjbommar/projects/personal/axeyum`):**
- Harness: `scripts/smtcomp_repro/` — `scoring.py` `runner.py` `selection.py`
  `smtlib_meta.py` `compete.py` `inventory.py` `select_library.py`
  `distribute_run.sh` `stop_run.sh` `run_repro.sh` `tests/` (+ `provenance.py`
  from another agent). Docs: `scripts/smtcomp_repro/README.md`, `RESULTS.md`.
- CLI: `crates/axeyum-bench/examples/smtcomp_cli.rs`.
- Plan: `docs/plan/full-library-gap-closing-plan-2026-07-22.md`.
- Bench records: `bench-results/smtcomp-repro-20260721/` (228-file + charts),
  `bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/` (P0 repro).

**NAS (`/nas3/data/axeyum/`, shared, ~16 TB free):**
- Corpus: `corpus/smtlib-2024/non-incremental/non-incremental/<LOGIC>/…` (438,631),
  `corpus/smtlib-2024/incremental/…` (44,333).
- Run: `harness/full-inventory/selected.txt` (64,345), `selection_manifest.json`,
  `raw_selection/` (shard logs + raw JSON).
- Staged binaries (⚠ axeyum one is STALE): `harness/bin/{axeyum-smtcomp,cvc5,bitwuzla}`.
- Staged harness copy: `harness/smtcomp_repro/*.py`.

**Reference solvers (repo, gitignored):** `references/smtcomp-solvers/{cvc5,bitwuzla}`.

**External reference:** SMT-COMP 2024 Single Query results —
`https://smt-comp.github.io/2024/results/`.

---

## 7. Gotchas learned (don't relearn the hard way)

- **Thermal:** s4/s5/s6/s7 hit **92–99 °C** under full core load (s4 also runs
  our `llama-server`). Run **s4 only, N=8, thread-pinned** (`RAYON_NUM_THREADS=1`
  so workers == active cores). Never full-load them.
- **Orphan runaways:** `pkill -f compete.py` orphans `axeyum-smtcomp` children,
  whose `--timeout-ms` does NOT fire on hard files → they run unbounded and pile
  up, cooking the box. **Always stop with `scripts/smtcomp_repro/stop_run.sh`**
  (kills children first).
- **Multi-worktree fleet:** `main` lives in `/nas4/.../claude-axeyum-cas-work`;
  many lanes (Lean-kernel, CAS, FP, codex) work in separate worktrees. This
  checkout is on `repro/smtcomp-scoring`. Never `checkout`/`reset`/`branch -f`
  another lane's live worktree.
- **Alphabet skew:** `selected.txt` is sorted; quantified logics (`AUF*`,
  `ALIA`, non-`QF_` `BV`/`LIA`) sort first and axeyum declines them → the early
  running decide-rate reads low. The strong `QF_*` block comes later.

---

## 8. Exact resume steps

1. **Un-break `main`** — get the Lean lane's `ExprNode::Proj` arm committed (or
   add a sound-decline stopgap), confirm `cargo check --workspace` is clean.
2. **Reconcile branches** onto `main` (user-directed; worktrees quiet).
3. **Re-stage the FIXED axeyum CLI** to `/nas3/data/axeyum/harness/bin/` and
   **restart the s4 §6 run** (`scripts/smtcomp_repro/distribute_run.sh
   /nas3/data/axeyum/harness/full-inventory/selected.txt 300 <outdir> selection`),
   re-arm a WRONG grep.
4. On completion: `python3 scripts/smtcomp_repro/inventory.py <outdir>/raw_*.json
   --solver axeyum --ceiling-s 300 --out inventory.json`; also score cvc5 +
   bitwuzla on the same files (G3); commit a dated `bench-results/` record.
5. Then pick up the plan at Rank 1 → 2 → 3
   ([`../full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md)).

---

*Paused 2026-07-22. Owner on resume: the SMT-COMP/quantifier measurement lane.*
