# Axeyum plan, status, and next actions

> **Generated; do not edit by hand.** Sources: project-wide sections in
> [`docs/plan/global/`](docs/plan/global/README.md), one file per lane in
> [`docs/plan/status/`](docs/plan/status/README.md). Edit **your lane's file**
> and run `python3 scripts/gen-plan.py`; `--check` is a gate. This file was
> touched 67 times in 24 hours by concurrent lanes on 2026-08-13/14 and one
> lane's edit was swept into another's commit — that is what the split fixes.

**Canonical project tracker.** This is the repository's single mutable source
for current project status, ordered work, blockers, and resume guidance. Read it
first; a lane updates its own file under `docs/plan/status/`, never this one.

- Last consolidated: **2026-10-05**, against `main` at `a38d5f5da`
  (2026-09-17). All work has been paused since that commit; nothing is in
  flight, and every lane file was archived the same day.
- Status vocabulary: `TODO` · `WIP` · `BLOCKED` · `DONE` · `PAUSED`.
- History moved out of this file. The 770 lane files of the August–September
  campaigns are in [`docs/plan/archive/lanes/`](docs/plan/archive/README.md);
  the global sections this rewrite replaced (A1–A13, L0–L4) are preserved
  verbatim in `docs/plan/archive/global-2026-09-17/`; the index of every dated
  plan note and what superseded it is [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md).

`STATUS.md` is a compatibility pointer and there is no root `TODO.md`. Dated
notes under [`docs/plan/`](docs/plan/README.md),
[`docs/research/`](docs/research/README.md) and
[`bench-results/`](bench-results/README.md) are evidence and task detail; they
do not set order or current state. This file does.

## Status

Axeyum is a working research-grade reasoning stack: a pure-Rust default path,
replay-checked SAT models, several independently checked UNSAT evidence routes,
broad but uneven theory support, an independent Lean-core checker and importer,
a kernel-checked fact library, a CAS, and three external consumers. It is not
yet a drop-in Z3 replacement or a replacement for Lean.

Every number below names its source. "(not re-run)" means it was copied from
the cited file on 2026-10-05, not re-measured.

### Solver — the parity ledger

Latest entry per division by **solver commit** in
[`bench-results/PARITY.md`](bench-results/PARITY.md): all sixteen were taken on
2026-09-11, fifteen at `c1d6db6fe` against cvc5 1.3.4 (Bitwuzla 0.9.1 for QF_ABV, QF_BV and QF_FP), QF_UFLRA at
`14712b1f4` against z3 4.13.3. **0 disagreements in every division.** Axeyum /
reference on identical 200-file lists, 24 s:

| ≥ 95 % | 85–95 % | < 85 % |
|---|---|---|
| QF_UF 200/200 · QF_FP 199/200 · QF_SLIA 193/194 · QF_RDL 152/154 · UF 90/93 · QF_BV 186/194 | QF_ABV 186/197 · QF_S 186/197 · QF_IDL 113/123 · QF_UFLIA 161/180 · QF_LIA 119/139 | QF_LRA 107/145 · QF_UFLRA 142/198 · QF_NRA 117/186 · QF_DT 114/192 · QF_NIA 41/87 |

The ledger frame is old: `c1d6db6fe` is 976 commits behind `a38d5f5da`. Gains
measured after it are **not ledger entries** and are listed separately:

- **2026-09-17 board A/B** ([README](bench-results/board-ab-20260917-adr2142/README.md)):
  Axeyum alone, 16 × 200 files, `60e23fa39` decides **2,432 of 3,200** (+8 over
  its parent, 0 losses, 0 of 4,380 `:status` disagreements). Where that board
  differs most from the ledger: QF_NIA **87** (ledger 41), QF_DT **171** (114),
  QF_NRA 124 (117), QF_UFLIA 167 (161), QF_UFLRA 149 (142). No reference ran.
- **Shipped after that board** (ADR A/Bs, pinned lists;
  [coordinator record](docs/plan/archive/lanes/coordinator-three-repos-2026-09-16.md)):
  QF_LRA 107 → 113 ([ADR-2147](docs/research/09-decisions/adr-2147-a-violated-disequality-is-a-case-split-not-an-unknown.md)),
  QF_UFLRA 148 → 150, UFNIA 54 → 61
  ([ADR-2148](docs/research/09-decisions/adr-2148-nia-lemmas-versus-slice-versus-iteration.md)).
- The five weakest divisions each have a mechanism named at `file:line`
  ([stock-take, 2026-09-16](docs/plan/five-divisions-stock-take-2026-09-16.md)).

### Library, CAS, Lean

- **Facts** (counted 2026-10-05 over `artifacts/facts/*.json`): **2,971** —
  proved 2,692 · open 267 · computed 5 · refuted 4 · conjectured 3.
- **Trusted surface** (`docs/plan/lean-axiom-ledger-v1.json`, population as of
  2026-08-17, not re-run — `gen-lean-axiom-ledger.py --check` builds Rust):
  30 declared axioms, all in the `axreal` package; every other prelude 0.
  **Declared is not reached**
  ([ADR-0509](docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)):
  both are published, and the 30 are reached by no shipped route — the package
  is kept as the negative control those measurements are read against.
- **CAS** (`scripts/check-cas-trust-registry.py`, run 2026-10-05): 1,280 public
  functions — 151 certified, 110 checker, 1,019 uncertified; floor 151 held.
- **Lean replay** ([ADR-1661](docs/research/09-decisions/adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md),
  2026-09-10, not re-run): of 4,478 proved declarations pinned Lean accepts
  4,394; 50 are `Type`-valued theorems Lean refuses; 34 are blocked behind them.
  What "Lean compatible" means is fixed in
  [`14-lean-lang.md`](docs/math-department/14-lean-lang.md) (ADR-1668).

### Evidence

- **QF_BV certification** (`PARITY.md` evidence entry, 2026-08-17,
  `c799be2f7`, not re-run): 93/130 UNSAT certified (71.5 %), 79/130 re-checked
  from serialized text alone, 0 certificates failed. The other 37 are bare UNSAT.
- **SAT engine**: the native core is the only engine
  ([ADR-1908](docs/research/09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md));
  BatSat is removed and the referee is an external CaDiCaL/Kissat binary on
  our DIMACS text
  ([ADR-1910](docs/research/09-decisions/adr-1910-the-sat-referee-is-an-external-binary-reading-dimacs-text-and-batsat-is-removed.md)).

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|


Rows come from active lane files; with none active the table is empty. The
2026-09-17 results above are the last landings.

## Next Actions

**P0 preempts every track:** a wrong verdict, a crash, data loss, or a gate that
cannot fail (or is red) is reproduced, root-caused, regressed and repaired
first. Otherwise work runs in five tracks; within a track, take the first
unblocked item. Tracks may run in parallel, one lane per item.



### SOL — Solver parity

Close the measured gap to the named reference division by division, never
trading a verdict for speed. Every lever ships only under the ship criterion
(0 stable losses, 0 flips, ≥ 1 stable gain on pinned **and** held-out); a lever
that fails it stays OFF with its A/B in an ADR. Detail:
[families](docs/plan/families/README.md),
[stock-take 2026-09-16](docs/plan/five-divisions-stock-take-2026-09-16.md),
[CDCL consolidation plan](docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md).

1. **SOL-1 Re-measure the board on head.** The ledger frame `c1d6db6fe` is 976
   commits behind `a38d5f5da`; the A13 frame `db31113fa` is 425 behind; and the
   ledger is badly stale for QF_NIA (41 ledger vs 87 on the 09-17 board) and
   QF_DT (114 vs 171). Run all 16 lists through `scripts/parity-run.sh` at one
   commit, plus a same-day z3/cvc5 reference board on the identical lists.
   *Exit:* 16 ledger entries at one solver commit, 0 disagreements, and
   `scripts/check-parity-freshness.py` exits 0 (it exits 2 today — ENG-1).
2. **SOL-2 Finish CDCL(T) consolidation (phase B4).** ADR-1908 made the native
   core the one CDCL(T) driver, but `ufbv_online.rs:1468` and `:3498` still
   build `CdclT`; ADR-1913 scopes it as a swap gated on one probe. *Exit:* no shipping path
   constructs `CdclT`; board verdict-invariant against SOL-1.
3. **SOL-3 Linear arithmetic depth** (QF_LRA 107/145, QF_UFLRA 142/198,
   QF_IDL 113/123 on the ledger). In order: budget hand-back from a
   non-converging online search (the `ecoliMILP` shape) and the `sc-19…25`
   search cost; the 7 files stopped at a pivot-0 deadline poll
   (`simplex.rs:1441`); the 49 `cilled`/`minepump` QF_UFLRA files that land at
   ~25 s; `dl-online` as a portfolio arm and QF_IDL's 19 early declines.
   *Exit per lever:* ship criterion, plus the five LRA/DL/LIA z3 fuzzes green.
4. **SOL-4 Nonlinear and quantified** (QF_NIA, QF_NRA, UF/UFNIA/UFLIA).
   67 of 116 undecided QF_NIA rows timed out inside the linear relaxation
   (stock-take, before ADR-2148 shipped); S12's
   coefficient-width rung was never built; ADR-2149 (nested-binder activation)
   is registered OFF with no A/B run; ADR-2134 (+4 pinned QF_NRA, 0 held-out
   movers) stays OFF. *Exit:* one shipped lever per division under the ship
   criterion, or an ADR recording why the named mechanism is not the block.
5. **SOL-5 Dispatch cost and cause coverage.** `int-real-relax` decides 0 of
   198 rows while costing 754 s (ADR-2106); QF_RDL's last 2 files have no
   census; the families tree has no files for QF_DT, QF_S, QF_UFLRA and calls
   QF_FP "not entered". *Exit:* the rung is budgeted or removed by A/B; every
   ledger division has a family file with a cause or an explicit "no".

### LIB — Library and the flywheel

Make the flywheel automatic: the system should establish theorems nobody wrote
proofs for, through the one trust anchor (ADR-0601), as graded statement
families (ADR-0603). The metric is the trusted base and unassisted results, not
volume. The L0–L4 programme (ADR-0717) is done through S6, C3, G5 and D5;
what remains is below. Detail:
[throughput](docs/formalized-math-2026-08/05-throughput.md),
[CAS](docs/math-department/13-computer-algebra.md).

1. **LIB-1 Closed-loop batch discovery (D6).** *Exit:* a batch establishes a
   theorem whose checked proof consumes a theorem an earlier batch established,
   with no human-written target proof and an empty axiom footprint.
2. **LIB-2 Statement families, MOS-0.** None of the MOS files exist yet
   (`artifacts/statement-families/`, `scripts/check-statement-families.py`).
   *Exit:* every family row resolves to its declaration and receipt, and the
   targeted negative controls fail.
3. **LIB-3 CAS remainders.** Seven items of `13-computer-algebra.md` are `[~]`
   (1, 3–7, 9), e.g. moving four of five CAS arithmetic copies onto
   `axeyum-arith`, Galois groups, multivariate factorization. *Exit:* each item's
   own remainder, and the certified floor in `check-cas-trust-registry.py`
   rises above 151.
4. **LIB-4 Library artifact compatibility C4/C5.** C4's first demand-gated
   feature measured +0 population survival (ADR-1667). *Exit:* a C4 feature with
   nonzero survival, or C4 closed by ADR; C5 stays conditional on adapter use.

### EVD — Evidence and Lean

Every unsat/valid carries a machine-checkable proof, and every claim names
which check it passed. Detail: [evidence family](docs/plan/families/evidence/README.md),
[Lean](docs/math-department/14-lean-lang.md),
[proof-gap matrix](docs/plan/generated/proof-gap-matrix.md).

1. **EVD-1 Re-measure QF_BV evidence on head** (last: 93/130 certified,
   2026-08-17) and split the bare-UNSAT rows by route provenance; re-check
   whether the two QF_NIA `IntPow2` proof-production errors recorded in August
   still reproduce. *Exit:* a fresh evidence-mode ledger entry; zero production
   errors; certified, text-rechecked, arena-checked and bare counts kept apart.
2. **EVD-2 Delete the SOS reconstruction fallback.** ADR-1673 relabelled it and left
   deletion open; `reconstruct_sos_certificate_wrapper_to_lean_module` is still
   in `axeyum-solver/src/reconstruct.rs`.
   *Exit:* the wrapper is gone and no reconstruction emits a statement-only shim.
3. **EVD-3 Lean residuals.** ℤ and an LRAT route for `by axeyum` (ADR-1666 is
   ℕ only); the 50 `Type`-valued theorems and 34 blocked declarations
   (ADR-1661); the unfinished 1,077-command audit (107 excluded). *Exit:*
   each closes with its own run and regenerated Lean matrices
   (`gen-lean-compatibility.py --check`, `gen-lean-complete-parity.py --check`).
4. **EVD-4 Propositional SAT entry.** RAT in the backward elaborator, the last
   piece after ADR-1722. *Exit:* RAT proofs elaborate to LRAT checked by
   `check_lrat`.

### CON — Consumers

Real users drive the product surface: the Python bindings, cindergraph (C
source graphs) and Glaurung (binary analysis) consume Axeyum; the SMT-LIB front
door serves everyone else. Foreign repositories are pushed only by the user.

1. **CON-1 Glaurung's default-backend decision.** Its ADR-0272 timing
   campaign was inconclusive; re-register it with a work-bounded budget.
   *Exit:* a registered campaign result that decides the default.
2. **CON-2 The defects pipeline over a real C library** (cindergraph → QF_BV
   → `axeyum_cli` → sanitizer replay; `python/examples/cindergraph_defects/`).
   *Exit:* findings on an unmodified upstream library, each replayed.
3. **CON-3 cindergraph's `for (;;)` empty-body policy.** Needs a Joern run.
   *Exit:* the policy pinned by a test against recorded Joern output.
4. **CON-4 SMT-LIB session semantics.** ADR-0342 is still `proposed`:
   scoped declarations under `push`/`pop`, reset epochs, atomic continued
   errors; then `define-fun-rec`, full `(reset)`, parametric `declare-sort`.
   *Exit:* accepted ADR; textual fixtures compare ordered outputs; a malformed
   command cannot partially mutate session state.

### ENG — Engineering hygiene

Gates that cannot fail, stale labels and abandoned state are how false claims
ship. Detail: [architecture review](docs/research/11-design-review/2026-08-27-architecture-review.md),
[gate divergence](docs/refactor-2026-08/gate-divergence-2026-08-14.md).

1. **ENG-1 Red gates on `a38d5f5da`.** `check-plan-authority.py` (global/ was
   60,663 bytes against a 32,000 cap; fixed by this consolidation) and
   `check-parity-freshness.py` (exit 2: `PARITY.md:1972` "Budget curve" header
   unrecognised); the `AlgS` shape duplicates red the hygiene gate on hosts with
   a fresh `shape_search`. Land the DONE-lane archive gate. *Exit:* each exits
   0 on main and each has a mutation control that kills exactly one test.
2. **ENG-2 Worktrees and branches.** `git worktree list` shows 203 entries
   (198 agent worktrees); 14 branches are unmerged into `main` (13 dated
   2026-08-22…31, one 2026-09-01). *Exit:* a read-only inventory classifies
   each (dirty/merged/unmerged/target size); unmerged work is merged or
   recorded abandoned; then exact-target removal.
3. **ENG-3 ADR status sweep.** 72 ADRs read `Status: proposed`, including
   shipped decisions (ADR-2121, ADR-2126, ADR-2142). *Exit:* every decision on
   `main` reads `accepted`; every OFF lever reads `proposed` or `deferred` with
   its A/B.
4. **ENG-4 Split `creal.rs`.** It fuses name registry, field struct, build
   order and dispatch (441 fields at the review; 11,595 lines on 2026-10-05, after a partial split — topological order and the generated `STEPS` table landed, ADR-1512/1530). *Exit:* the review's split
   lands with prelude projection byte-identical and the kernel suites green.

## Families and divisions

The per-division source of truth for **state, cause, lever and exit criterion**
is [`docs/plan/families/`](docs/plan/families/README.md); measurements live in
the [ledger](bench-results/PARITY.md). This table is the index.

| Family | On the board | State, 2026-10-05 |
|---|---|---|
| [SMT, quantifier-free](docs/plan/families/smt-quantifier-free/README.md) | 15 divisions | QF_UF closed at 200/200; every other gap has a named cause except QF_RDL's last 2 (not re-censused since S1). The family tree has no files yet for QF_DT, QF_S and QF_UFLRA, and still lists QF_FP and QF_UFLRA as "not entered" although both have ledger rows (SOL-5). |
| [SMT, quantified](docs/plan/families/smt-quantified/README.md) | UF (90/93) | cause measured ([uf.md](docs/plan/families/smt-quantified/uf.md)); nested-binder activation measured and OFF (ADR-2149, proposed). UFNIA, UFLIA, AUFDTLIRA are scored on A13 lists, not the board. |
| [Certificate chain](docs/plan/families/evidence/README.md) | none, by construction | a division can reach parity with empty certificates and no board row shows it — hence EVD. |
| [Propositional SAT](docs/plan/families/sat/README.md) | not entered | CNF entry point and binary DRAT landed (ADR-1722); RAT in the backward elaborator is the piece left. |
| [SMT-COMP other tracks](docs/plan/families/smt-comp-tracks/README.md) | not entered | model validation is the cheap entry. |
| [Hardware model checking](docs/plan/families/model-checking/README.md) | not entered | best architectural fit (AIGER in, AIG certificate out); unscoped. |
| [Boolean optimization / counting](docs/plan/families/boolean-optimization/README.md) | not entered | no input formats. |

Two standing cautions. **Our reference is not the frontier** in several
divisions — OpenSMT, Yices2 and SMTInterpol lead some logics we score against
cvc5, so "parity" means parity with the named reference
([survey](docs/research/02-ecosystems/competition-landscape-2026-09/README.md)).
And **a division without an established cause gets a census, not a slice.**

## Workstream state

All tracks are `PAUSED` since `a38d5f5da` (2026-09-17) with nothing in flight;
the state column is what a resuming lane inherits.

| Track | State | Boundary |
|---|---|---|
| SOL — solver parity | `PAUSED`; A13 queue closed 2026-09-17 (ADR-2147 and ADR-2148 shipped, ADR-2134 and ADR-2149 OFF) | Every measured number is on an old frame; SOL-1 re-measure gates any new scoring. |
| LIB — library / flywheel | `PAUSED`; L0–L4 phases done through S6, C3, G5, D5 (2026-08-30/31) | The loop has closed by hand, never automatically (LIB-1); statement families not started (LIB-2). |
| EVD — evidence and Lean | `PAUSED`; Lean chair's Next Ten all ticked; BatSat removed (ADR-1910) | QF_BV evidence last measured 2026-08-17; SOS fallback still present. |
| CON — consumers | `PAUSED`; the 2026-09-16 improvement lists closed for Axeyum (16/16) | Glaurung's default-backend decision is open (CON-1); cindergraph and Glaurung are pushed by the user only. |
| ENG — hygiene | `WIP` — this consolidation | Two gates red on `a38d5f5da` (ENG-1); 198 agent worktrees and 14 unmerged branches (ENG-2). |

## Resume protocol

1. Read this file first. Do not reconstruct priority from dated notes, archived
   lane files, branch names, or worktree age.
2. Verify live state (`git status --short --branch`, `git fetch origin`,
   `git rev-parse HEAD origin/main`, `git worktree list`). Re-derive any
   baseline you will score against; the boards quoted in Status are snapshots.
3. Pick the first unblocked item of the relevant track in **Next Actions**
   (P0 work preempts). Read its linked detail and the
   [foundational DAG](docs/research/08-planning/foundational-dag.md) before
   editing.
4. Open a lane file `docs/plan/status/<lane>.md` naming the item ID (e.g.
   `SOL-2`), with a `lane-status` block and landed rows
   ([format](docs/plan/status/README.md)). Work in an isolated worktree; one
   writer per branch.
5. Iterate on the narrowest relevant tests; run the aggregate gate once on the
   finished branch and confirm nonzero test counts. Commit with
   `scripts/lane-commit.sh`; merge and push per
   [multi-agent-operations](docs/contributor-guide/multi-agent-operations.md).
6. When the item meets its exit criterion (or is refuted), mark the lane `DONE`,
   **move the file to `docs/plan/archive/lanes/`**, update the item's line in
   the track here if its state changed, and run `python3 scripts/gen-plan.py`.
   Keep at most ~25 active lane files.

## Planning rules

- **One mutable tracker.** `PLAN.md`, generated from `docs/plan/global/` and
  active lane files. `STATUS.md` is a pointer; no root `TODO.md`; no other
  document may claim project-wide priority.
- **Dated notes are evidence, not queue.** A note under `docs/plan/` (stock-takes,
  gap logs, "what to build", improvement lists, roadmaps) records what was
  measured and proposed on its date. Anything still open from it is either an
  item here or not scheduled.
- **Labels.** Items are `SOL-n`, `LIB-n`, `EVD-n`, `CON-n`, `ENG-n`. Older
  labels (A1–A13, L0–L4, S1–S12, C/D/G phases, MOS-, W-, chair "Next Ten") are
  historical; resolve them through [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md) and the archive.
- **Lane lifecycle.** A lane file exists only while its item is active. On
  `DONE` it moves to `docs/plan/archive/lanes/`; at most ~25 are active.
- **Evidence outranks prose.** Benchmark TSV/JSON, generated matrices, test
  output, Git objects and remote refs decide status; correct prose that disagrees.
- **Wrong verdicts preempt everything (P0):** a wrong sat/unsat, a crash, data
  loss, or a gate that cannot fail is reproduced, root-caused, regressed and
  repaired before any breadth or performance item.
- **No false green.** A focused pass is not a full gate; a running job is not a
  pass; a local commit is not integration; a pinned-list gain alone ships nothing
  (the ship criterion is 0 stable losses, 0 flips, ≥ 1 stable gain on pinned
  and held-out).
- **No journal growth.** Global sections carry state, order and exits; detail
  goes in a dated note or artifact. `scripts/check-plan-authority.py` caps
  `global/` at 32,000 bytes and each lane file at 3,000.
- **Decisions require ADRs** for public operators, rewrites, encodings,
  backends, evidence artifacts, logic fragments, and priority-changing
  architecture.
- **Determinism and replay are promises:** stable order, explicit seeds and
  limits, original-term SAT replay, independent UNSAT checking.
- **Graph rank is advisory.** Degree, centrality and cost estimates never bypass
  fact-frontier legality, held-out isolation, or the theorem-credit contract.
- **Proof data does not leak into autonomous discovery:** proof/value edges may
  sequence work but are excluded from producer inputs and autonomous credit.

## Durable detail map

- **History:** [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md) (every dated plan note, its date, what
  superseded it); [`docs/plan/archive/`](docs/plan/archive/README.md) (lane files
  under `lanes/`, the replaced global sections under `global-2026-09-17/`).
- **Measurements:** [`PARITY.md`](bench-results/PARITY.md) (read the latest
  entry per division by solver commit), [`SCOREBOARD.md`](bench-results/SCOREBOARD.md),
  [families](docs/plan/families/README.md),
  [proof-gap matrix](docs/plan/generated/proof-gap-matrix.md),
  [capability matrix](docs/research/08-planning/capability-matrix.md).
- **Foundations:** [roadmap](docs/research/08-planning/roadmap.md),
  [foundational DAG](docs/research/08-planning/foundational-dag.md),
  [research questions](docs/research/08-planning/research-questions.md),
  [ADR index](docs/research/09-decisions/README.md),
  [2026-08-27 architecture review](docs/research/11-design-review/2026-08-27-architecture-review.md).
- **Mathematics and Lean:** [math department](docs/math-department/README.md)
  (chairs, [CAS](docs/math-department/13-computer-algebra.md),
  [Lean](docs/math-department/14-lean-lang.md)); fact ledger `artifacts/facts/`
  (`scripts/validate-facts.py`).
- **Strategy, frozen history:** `docs/refactor-2026-08/`,
  `docs/mathematics-2026-08/`, [`docs/formalized-math-2026-08/`](docs/formalized-math-2026-08/05-throughput.md)
  — read for reasoning, not for queue.
- **Working practice:** [contributor guide](docs/contributor-guide/README.md),
  [multi-agent operations](docs/contributor-guide/multi-agent-operations.md),
  public summary [`PROJECT-STATE.md`](docs/PROJECT-STATE.md).

## Consolidation record

### 2026-10-05

`PLAN.md` had grown to 75,717 lines and its global sections were three to seven
weeks stale. The 770 lane files moved to `docs/plan/archive/lanes/`; the replaced
sections are kept verbatim in `docs/plan/archive/global-2026-09-17/`; A1–A13
and L0–L4 became five tracks. Stale claims corrected, each checked against the
tree at `a38d5f5da`:

- The header said "last consolidated 2026-08-13" and cited A5-era SHAs.
- Status and Workstream quoted 2026-08-21 and 2026-09-05 parity numbers; every
  division has a 2026-09-11 ledger entry, and the 09-17 board is newer still.
- A13 read `PAUSED` with items 1–4 open; all four closed on 2026-09-17
  (`f7cd4195f`, `aa4ea0b6b`, `aab5d2db7`, `4d7c61ad5`). Its item 5 said the
  frame was 313 commits behind; it is now 425.
- A12 asked for a `CdclT` ADR and BatSat retirement; ADR-1908 and ADR-1910 are
  both accepted, and BatSat is out of `Cargo.lock`. Only phase B4 is left.
- L0–L4 read `TODO`; the phase lane files report S0–S6, C0–C3, G0–G5, D0–D5
  done on 2026-08-30/31. Only D6, C4 and C5 remain.
- A9 listed four open Lean items; `14-lean-lang.md` ticks all ten.
- Families said QF_RDL had "fourteen" unexplained files; the ledger gap is 2.
- The math chair's "Next Five" landed on 2026-09-06 and was never ticked.

### 2026-08-05

Removed two conflicting append-only root journals and one subsidiary live
tracker, made this file the only project-level authority, and corrected five
stale claims (CAS wave 24, an August-1 resume block, seven-vs-eleven divisions,
T3.5 ordering, PLAN-vs-STATUS authority). Detail is in Git history.
