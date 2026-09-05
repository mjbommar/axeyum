## Status

**A5 repair history.** Fail-closed LRA/IDL restarts exposed wide-core and
first-solve allocation growth, mixed-numeric parsing, native recursion,
unhonored construction deadlines, and declaration-scale quadratic work. Their
pushed bounded/iterative repairs and every non-credited partial stream are
retained in the
[failure/repair record](docs/plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md);
the current release returns typed `unknown` on each former abort trigger.

Axeyum is a working research-grade automated-reasoning stack with a pure-Rust
default path, replay-checked SAT models, multiple independently checked UNSAT
evidence routes, broad but uneven theory support, an independent Lean-core
checker/importer, and several consumers. It is not yet a drop-in Z3 replacement
or a replacement for the Lean system.

The [Lean requirements](docs/plan/lean-kernel-requirements-2026-08-13.md) are
**WIP**. Trusted surface, re-derived by `gen-lean-axiom-ledger.py --check`
rather than authored, 2026-08-19: `complex 0 · creal 0 · integer 0 · logic 0 ·
nat 0 · rat 0 · string 0 · real 30` — `real`, the axiomatized package, is the
only nonzero row. "Int reconstruction remains assumption-bearing" was true until
that day and is not.

**Declared is not reached; both are published**
([ADR-0509](docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)).
The 30 stay declared, reached by no shipped route. The package is kept as the
negative control those measurements are read against — delete it and no such
measurement can fail — now one assumed law over a constructed carrier
([ADR-0515](docs/research/09-decisions/adr-0515-a-negative-control-is-one-assumed-law-over-a-constructed-carrier.md)).

Exact pushed repairs for the A5 (linear-arithmetic), A3 (string/integer) and
A2 (stale-branch) streams — commit-by-commit, with the non-credited partial
streams retained — are in the
[A5/A3/A2 repair journal](docs/plan/a5-a3-repair-journal-2026-08.md). The
current release returns typed `unknown` on each former abort trigger; A3 yields
to A4.
### A1 arithmetic resource closure — `DONE`, archived

The two measured resource defects and their pushed repairs are in
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md).
Moved 2026-08-19: it is closed work, and this file is for what is true
now. Nothing was deleted.

### Current evidence snapshot

- The committed regression scoreboard contains **35 baselines across 24 logic
  fragments**: **762/992** files decided, **674** oracle-compared, and **zero
  recorded disagreements**. This is bounded regression evidence, not universal
  soundness or representative SMT-LIB coverage. See
  [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md).
- The refreshed 4-second frontier artifacts report BV reduction **38**
  (baseline 30), LIA cuts **35** (baseline 26), NIA UNSAT **40** (baseline 40),
  NRA degree **40** (baseline 40), and string bound **40** (baseline 8). These
  are load-sensitive local frontier measurements; they do not raise baselines.
- The append-only head-to-head ledger currently covers **nine divisions**
  (QF_SLIA, QF_BV, UF, QF_LIA, QF_RDL, QF_LRA, QF_UFLIA, QF_IDL, QF_NIA — the
  [2026-08-21 gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md)
  §1.3 found the committed `QF_ABV.txt` and `QF_UF.txt` parity lists have never
  been run). Its weak measured edges, all from the 2026-08-21 sweep at solver
  commit `cb4a391c9`, are QF_NIA **39/83 = 47.0%**, QF_IDL
  **66/118 = 55.9%**, QF_UFLIA **113/180 = 62.8%** (up from 94/180 after the
  theory-core-minimisation fix, ADR-0538), QF_LRA **88/134 = 65.7%**, and
  QF_RDL **102/148 = 68.9%**. Every credited entry has zero disagreements.
  Read the latest entry per division, sorted by **solver commit** (not date —
  two commits share the 2026-08-21 date) in
  [`bench-results/PARITY.md`](bench-results/PARITY.md); never copy an older
  entry merely because it has a higher score. `scripts/check-parity-freshness.py`
  exits 1 as of the 2026-09-05 performance review: all nine divisions are past
  the 14-day budget.
- QF_BV evidence mode decides 130 UNSAT rows: **93/130 certified (71.5%)**,
  **79/130 rechecked from serialized text alone (60.8%)**, and **93/93
  certified rows independently checked against a fresh re-parse and term
  arena**. Neither check had a failure. The remaining 37 are bare UNSAT
  decisions because the evidence-producing route could not decide them within
  60 seconds. (`bench-results/PARITY.md`, 2026-08-17T20:21:52Z, solver commit
  `c799be2f7`.)
- The broader evidence audit still records **58 uncertified occurrences**,
  **eight independently checked results without Lean reconstruction**, and
  **two QF_NIA `IntPow2` proof-production errors**. Do not combine these
  denominators with the newer QF_BV-only experiment.
- "Lean compatible" means what the compatibility matrix measures: K0 1/1 and
  K1 6/6 (an independent checker and a versioned import route), K2 through K6
  at 0 — no native source, tactics, workflow, runtime, or ecosystem yet. Two
  pins are distinct and every claim names which: `lean-toolchain`, the
  cross-check pin (4.34.0-rc1, ADR-1594/1660), and the Mathlib corpus pin
  (Lean 4.30.0, mathlib4 `c5ea0035`, lean4export `a3e35a58`). Independent
  checkability is measured by replay in pinned Lean: 4,478 proved
  declarations, 4,394 accepted, 50 `Type`-valued theorems Lean refuses, 34
  blocked behind them (ADR-1661). Imports are a labeled tier, never the
  axiom-free headline (ADR-0601, ADR-1664). `by axeyum` lets Lean check
  axeyum-produced terms as a tactic (ADR-1666). Cross-library statement
  identity runs through the carrier correspondence ledger (ADR-1665). Full
  detail, the per-chair breakdown, and the open items:
  [`docs/math-department/14-lean-lang.md`](docs/math-department/14-lean-lang.md).
- The previous 64,345-file full-library candidate is not a result: it produced
  zero admissible raw shards. Resumable/process-free readiness work exists, but
  a representative current-main run has not been admitted or published.

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|
<!-- plan-generated: landed-changes -->
Older landed changes (including the 2026-08-06 A1/A2 closure commits) remain
in Git and their dated result notes; this table is deliberately bounded to
changes that still determine the immediate queue.
