# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

## Current focus

- **Plan authored** (2026-06-15): the full track/phase/task plan is under
  [`docs/plan/`](docs/plan/README.md), built from the five reference reviews in
  [`docs/plan/references/`](docs/plan/references/README.md).
- **P3.0 trust ledger — DONE** (2026-06-15): typed `TrustId` taxonomy + pedantic
  levels, per-result `trusted_steps` on `EvidenceReport`, golden-tested
  [trust-ledger.md](docs/research/08-planning/trust-ledger.md) (5 of 11
  reductions are trust holes), ADR-0031. The trusted base is now countable.
- **T1.1.1 subsumption + T1.1.2 BVE — DONE (correctness)** (2026-06-15):
  `axeyum_cnf::simplify` (model-preserving tautology removal + forward subsumption
  + self-subsuming resolution) and `axeyum_cnf::eliminate_variables` (bounded
  variable elimination by resolution with a `Reconstruction` stack to lift reduced
  models back to the original, the non-increasing/size/occurrence bounds). 13 tests
  total incl. brute-force equisatisfiability + per-model reconstruction + SAT/DRAT
  preservation. DRAT-step emission inside the proof-producing solve and the measured
  perf delta ride P4.5 + the pipeline-integration step.
- **P4.5 — WIP, blocked on host RAM (transitioning to s4).** Landed: the bench
  harness now gives workers a 512 MB stack (fixes a stack overflow a deeply-nested
  instance triggered, which aborted the batch); a committed curated QF_BV slice
  `corpus/qfbv-curated/` (36 files); `just bench-qfbv-curated`. The instrument is
  validated on `corpus/micro` (3/3 decided, agree=3, DISAGREE=0). **The full
  curated baseline OOM-killed this 26–32 GB host twice** (unbounded Z3/sat-bv
  worker memory) — to be run on s4 with a per-process memory cap (see host-setup).
- **Machine transition:** see [docs/plan/host-setup.md](docs/plan/host-setup.md).
  All work is on branch `docs/readme-plan-parity-roadmap` (pushed to origin).
- **Next task (on s4):** run the curated baseline under a memory cap, commit the
  artifact, then wire subsumption + BVE into the bit-blast→CNF→solve pipeline and
  re-measure the inprocessing delta.

## Already shipped this session (pre-plan)

The reachability / symbolic-execution / certificate surface that motivated this
plan is built and committed on the current branch:

- BMC driver, k-induction (unbounded safety), symbolic-memory BMC,
  `SymbolicExecutor` (path exploration + test-suite enumeration + path-condition
  optimization), and self-rechecking certificates (`UnsatProof::recheck`,
  `SafetyCertificate::recheck`, `EndToEndUnsatOutcome::recheck`).
- These map onto Track 4 (use cases) and Track 3 (the recheck family); the plan
  records what remains around them.

## Phase status

### Track 1 — Engine & Performance
| Phase | Title | Status |
|---|---|---|
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — T1.1.1 subsumption + T1.1.2 BVE landed |
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | TODO |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | TODO |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | TODO |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | TODO |
| P1.6 | Theory combination (th_eq bus, interface equalities) | TODO |
| P1.7 | PBLS local-search BV engine (portfolio) | TODO |
| P1.8 | Strategy & tactics (combinators + probes + per-logic scripts) | TODO |

### Track 2 — Theories & Breadth
| Phase | Title | Status |
|---|---|---|
| P2.1 | BV lazy blasting + word-level slicing + BV theory-checker | TODO |
| P2.2 | Arrays: lazy ROW axioms + extensionality + func_interp models | TODO |
| P2.3 | EUF on the e-graph (from Ackermann to incremental) | TODO |
| P2.4 | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | TODO |
| P2.5 | NRA: incremental linearization → nlsat/CAD | TODO |
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | TODO |
| P2.7 | Strings (unbounded, full `str.*`, regex) | TODO |
| P2.8 | FP polish (unspecified values, min/max ±0, lazy conversion) | TODO |
| P2.9 | Datatypes lazy (e-graph splitting + occurs-check) | TODO |

### Track 3 — Proofs & Lean
| Phase | Title | Status |
|---|---|---|
| P3.0 | Reduction trust ledger (TrustId + pedantic levels) | DONE |
| P3.1 | LRAT clausal upgrade (+ in-tree check_lrat) | TODO |
| P3.2 | Alethe term/proof IR + emitter (`axeyum-alethe`) **[critical path]** | TODO |
| P3.3 | Alethe for QF_BV (bitblast_* + CNF rules + resolution/drat; Carcara CI) | TODO |
| P3.4 | Embedded Alethe checker subset (self-checking) | TODO |
| P3.5 | Alethe for reductions (arrays → Ackermann → int-blast) | TODO |
| P3.6 | In-tree Rust Lean kernel (`axeyum-lean-kernel`, from nanoda) | TODO |
| P3.7 | Alethe→Lean reconstruction (proof terms) | TODO |

### Track 4 — Use Cases & Frontend
| Phase | Title | Status |
|---|---|---|
| P4.1 | Warm lazy arrays / symbolic memory (ADR-0030 deferred half) | TODO |
| P4.2 | Symbolic-execution CFG frontend (angr/unicorn-class) | TODO |
| P4.3 | Optimization: OMT lexicographic/Pareto + MILP hardening | TODO |
| P4.4 | SMT-LIB command-surface completeness (declare-sort, reset, get-proof, …) | TODO |
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | WIP — harness fix + curated slice landed; baseline pending on s4 (OOM here) |

## Changelog

- **2026-06-15** — Cloned full reference set (added Z3 to `scripts/fetch-references.sh`).
  Ran five Opus sub-agents over Z3 core, Z3 theories, bitwuzla+CaDiCaL/Kissat,
  proof/Lean, and an axeyum self-audit. Authored the end-to-end plan under
  `docs/plan/` with this STATUS tracker and the master `PLAN.md` index.
- **2026-06-15** — **P3.0 done.** New `axeyum_solver::trust` module (`TrustId`,
  `TrustStep`, `ALL_TRUST_IDS`, `trust_ledger_markdown`); `EvidenceReport.trusted_steps`
  records per-result trust dependencies across all producers; golden test +
  `docs/research/08-planning/trust-ledger.md`; 4 per-result tests; ADR-0031.
  Trusted base is now countable: 5 trust holes (array-elim, ackermann, int-blast,
  datatype-elim, fpa2bv) — the targets for Track 3 P3.5.
- **2026-06-15** — **T1.1.1 subsumption pass.** New `axeyum_cnf::simplify`
  (`SubsumeStats`): model-preserving tautology removal + forward subsumption (64-bit
  signature fast-reject) + self-subsuming resolution; 7 tests incl. brute-force
  equivalence and SAT/DRAT preservation. P1.1 → WIP.
- **2026-06-15** — **P4.5 (WIP) + s4 transition.** Bench harness worker stack
  raised to 512 MB (deeply-nested-term stack-overflow fix); committed curated
  QF_BV slice `corpus/qfbv-curated/` (36 files) + `just bench-qfbv-curated`;
  GPU horizon note; `docs/plan/host-setup.md` transition checklist. Full baseline
  OOM-killed the host — deferred to s4 with memory caps.
- **2026-06-15** — **T1.1.2 bounded variable elimination.** New `axeyum_cnf::bve`
  (`eliminate_variables`, `BveOptions`, `BveOutcome`, `BveStats`, `Reconstruction`):
  Davis–Putnam resolution with the CaDiCaL non-increasing/size/occurrence bounds and
  a reverse-replay reconstruction stack (equisatisfiable, not model-preserving — the
  reduced model extends via `Reconstruction::extend`). 6 tests incl. brute-force
  equisatisfiability + per-model reconstruction + bound-respect + SAT/DRAT preservation.
