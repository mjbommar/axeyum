# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

## Current focus

- **Plan authored** (2026-06-15): the full track/phase/task plan is written under
  [`docs/plan/`](docs/plan/README.md), built from the five reference reviews in
  [`docs/plan/references/`](docs/plan/references/README.md).
- **Next task to start:** Track 1 → [P1.1 SAT inprocessing](docs/plan/track-1-engine/P1.1-sat-inprocessing.md),
  task **T1.1.1 forward subsumption** (smallest first step toward the
  highest-leverage performance win, BVE), run in parallel with Track 3 →
  [P3.0 trust ledger](docs/plan/track-3-proof-lean/P3.0-trust-ledger.md) (small,
  unblocks the proof track) and Track 4 →
  [P4.5 benchmarking](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md)
  (establish the measured Z3 head-to-head harness before tuning).

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
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | TODO |
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
| P3.0 | Reduction trust ledger (TrustId + pedantic levels) | TODO |
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
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | TODO |

## Changelog

- **2026-06-15** — Cloned full reference set (added Z3 to `scripts/fetch-references.sh`).
  Ran five Opus sub-agents over Z3 core, Z3 theories, bitwuzla+CaDiCaL/Kissat,
  proof/Lean, and an axeyum self-audit. Authored the end-to-end plan under
  `docs/plan/` with this STATUS tracker and the master `PLAN.md` index.
