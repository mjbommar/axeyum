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
- **P4.5 — DONE.** Committed measurement slice `corpus/qfbv-curated/` (43 files,
  **width-capped ≤64 bits**) + recorded baseline
  `bench-results/baselines/qfbv-curated-sat-bv-vs-z3-2s.json`: sat-bv vs Z3 4.13.3,
  2 s, budgets — **32/43 decided (8 sat + 24 unsat), 11 unknown, agree=32,
  DISAGREE=0, replay failures=0**, PAR-2 ≈1.07 s. Harness now gives workers a
  512 MB stack (deep-term fix). `just bench-qfbv-curated`.
- **Known robustness gap (Track 1 / P1.2):** sat-bv allocates eagerly during
  lowering on wide terms (a 1024-bit multiply / 20k-bit vector → multi-GB alloc)
  *before* the node budget is enforced, aborting instead of returning `unknown`.
  Curating by width sidesteps it; the real fix is graceful oversized-encoding
  refusal. This is why the original size-based slice OOM'd two hosts.
- **Machine transition to s4 done:** repo at the same path on `server4` (123 GB,
  2× RTX 4060 Ti 16 GB, CUDA 12.4); `corpus/public` symlinked to NAS
  `/nas3/data/...`; z3 + rust verified; 54/54 cnf tests pass. See
  [docs/plan/host-setup.md](docs/plan/host-setup.md).
- **T1.1.4 inprocessing made near-linear + time-bounded — DONE** (2026-06-16):
  `axeyum_cnf::simplify` rewritten to forward one-watch occurrence-list subsumption
  (CaDiCaL/Kissat `subsume.cpp`/`forward.c`); `axeyum_cnf::bve` rewritten to full
  literal occurrence lists + a touched-variable queue (`elim.cpp`/`eliminate.c`);
  both gained `_within(deadline)` variants, and `sat_bv` now bounds inprocessing to
  ≤50% of the remaining solve budget (partial passes stay sound: subsumption
  model-preserving, BVE equisatisfiable + valid reconstruction). The old size guard
  was lifted (512/2048 → 200k/1M admission ceiling). Each pass adds a 400-formula
  randomized brute-force test. **Curated A/B (sat-bv vs Z3, 2 s, s4): 8 sat / 24
  unsat / 11 unknown, agree=32, DISAGREE=0, replay failures=0, PAR-2 1.095 s** —
  i.e. decision-identical to baseline (32/43) with no regression; the earlier
  13–22 s pass hangs and the 3-instance regression are gone.
- **Why inprocessing still decides none of the 11 unknowns (gates the next lever):**
  the unknowns are either (a) **structurally BVE-resistant multipliers** (`mulhs64`:
  45 105 vars, BVE eliminates 417 / clauses 201 656→201 379 ≈ 0.1% — non-increasing
  resolution cannot collapse a multiplier), so the bottleneck is the **SAT search
  itself → P1.3 (SAT-core modernization)**; or (b) reduced-but-still-hard (e.g.
  `commute08` 18 296→7 038 clauses) where the reduced formula still doesn't close in
  the remaining budget. Inprocessing is now correct/fast/safe infrastructure that
  pays off once P1.3 / P1.2 land; it stays off by default.
- **T1.1.3 inprocessing wired into the solve pipeline — DONE (sound), measured
  net-negative with current passes** (2026-06-16):
  `SolverConfig::cnf_inprocessing` (off by default) runs `simplify` (subsumption,
  model-preserving) then `eliminate_variables` (BVE, equisatisfiable) on the
  Tseitin formula in `sat_bv_backend`; a reduced `sat` model is lifted back to
  the original CNF variables via `Reconstruction::extend` before the existing
  AIG→model→original-term replay. 3 A/B tests + bench `--inprocess` flag +
  `just bench-qfbv-curated-inprocess`. **Correctness proven** across the curated
  slice (DISAGREE=0, model_replay_failures=0; 27 instances inprocessed end to end
  incl. SAT reconstruction, BVE eliminating up to 296 vars).
- **Key measured finding (gates P1.1):** the correctness-first passes do **not**
  scale to solve-relevant CNF. At a 5k-var/20k-clause cap the pass took **13–22 s**
  on `mulhs16`/`commute08`, blew the 2 s budget, regressed 3 decided instances to
  `unknown`, and decided **none** of the 11 existing unknowns. `simplify` is an
  `O(clauses²)` sweep; `bve` rescans all clauses per candidate (`O(vars·clauses)`
  per round). Inprocessing is therefore guarded to ≤512 vars / ≤2048 clauses
  (provably cheap, ≤121 ms here) — at which size the committed A/B is
  decision-identical to baseline (32/43, PAR-2 1.071 s vs 1.063 s). **Real win
  needs occurrence-list indexing first.**
- **Next task (T1.1.4):** give `axeyum_cnf::simplify` and `axeyum_cnf::bve`
  occurrence-list / signature indexing (near-linear passes) so inprocessing can
  run on the wide instances (the 11 unknowns) without escaping the solve budget;
  then re-run `just bench-qfbv-curated-inprocess` and lift the size guard.

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
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — subsumption+BVE landed (T1.1.1/2), wired into the solve pipeline (T1.1.3), made occurrence-list near-linear + time-bounded (T1.1.4): safe, no regression, but the curated unknowns are SAT-search-bound (→ P1.3) or BVE-resistant. Vivification / glue tiers remain |
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
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | DONE — committed slice + baseline (32/43 decided, agree=32, DISAGREE=0) |

## Changelog

- **2026-06-16** — **T1.1.4 inprocessing made near-linear + time-bounded.**
  `simplify` → forward one-watch occurrence-list subsumption (variable-keyed
  signature so self-subsuming witnesses aren't false-rejected); `bve` → full
  literal occurrence lists + touched-variable queue (lazy clause removal,
  resolution-budget safety net), running to a fixpoint in one drain. Added
  `simplify_within`/`eliminate_variables_within` deadline variants; `sat_bv`
  bounds inprocessing to ≤50% of the remaining solve budget and the old 512/2048
  size guard was lifted to a 200k/1M admission ceiling. Two new 400-formula
  randomized brute-force tests (subsumption equivalence, BVE equisatisfiability +
  reconstruction). Curated A/B: 32/43 decided, agree=32, DISAGREE=0, 0 replay
  failures, PAR-2 1.095 s — no regression vs baseline; the prior 13–22 s pass
  hangs and 3-instance regression are gone. The 11 unknowns stay unknown because
  they are multiplier-structural (BVE ≈0% on `mulhs*`) or reduced-but-still-hard,
  i.e. SAT-search-bound (→ P1.3). Commits 4c99d7e (a), 154936d (b), this (c).
- **2026-06-16** — **T1.1.3 inprocessing wired into the bit-blast→CNF→solve
  pipeline + measured on s4.** New `SolverConfig::cnf_inprocessing`
  (`with_cnf_inprocessing`, off by default); `sat_bv_backend` runs
  `simplify`+`eliminate_variables` on the Tseitin formula behind a
  `maybe_inprocess` size guard, solves the reduced formula, DRAT-checks /
  `prove_unsat`s the reduced formula, and lifts a reduced `sat` model back via
  `Reconstruction::extend` before the original-term replay (`inprocess_ms`
  folded into `translate`; per-pass stats recorded). 3 A/B tests
  (`tests/sat_bv.rs`), bench `--inprocess` flag (config + JSON metadata + run
  fingerprint), `just bench-qfbv-curated-inprocess`, committed artifact
  `qfbv-curated-sat-bv-inprocess-vs-z3-2s.json`. **Measurement:** with the
  current `O(clauses²)` subsumption + per-candidate-rescan BVE, inprocessing is a
  net regression (13–22 s passes blow a 2 s budget) and decides none of the 11
  unknowns; correctness is intact (DISAGREE=0, 0 replay failures). Guarded to
  ≤512 vars/≤2048 clauses → decision-identical to baseline (32/43, PAR-2 1.071 s).
  Real win deferred to T1.1.4 (occurrence-list indexing).
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
