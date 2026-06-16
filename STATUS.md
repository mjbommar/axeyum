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
- **P1.2 preprocessing wired into the bench + measured — DONE** (commit 0c594ac).
  `check_with_preprocessing` (commit 86cd28a) + bench `--preprocess` flag
  (`just bench-qfbv-curated-preprocess`): the trail is threaded through
  solve_planned→solve_one→classify_result→replay_model so a `sat` model
  reconstructs before replaying the originals. Curated A/B: 32/43, agree=32,
  DISAGREE=0, 0 replay failures, PAR-2 1.060 s — decision-identical, model-sound
  across all 43 incl. the oracle path; reduced the DAG on 5/43 (the instances with
  top-level `x=t` structure), no-op on the multiplier-heavy rest. Correct
  infrastructure; the PAR-2 payoff needs a corpus with explicit defines.
- **P1.4 e-graph keystone COMPLETE** (commits eb3e9e6, 0c5840f, c47dc0c, 2c735b5,
  d81bf46): `axeyum-egraph` (ADR-0032) is a standalone, backtrackable,
  explanation-producing, independently-checkable equality bus — hash-cons +
  congruence cascade, `explain`, push/pop, `check_congruence`, theory-var lists.
  17 tests. This unblocks the Track-2 theory upgrades and the CDCL(T) loop.
- **P1.5 two slices DONE** (commits f69aa40, 8d97081): `prove_unsat_by_congruence`
  (conjunctive) and `prove_unsat_lazy` (offline DPLL(T) over boolean structure —
  boolean skeleton via sat-bv + e-graph theory check + explain-based blocking
  clauses). Sound EUF UNSAT proving with independently-checked conflicts.
- **Next task — options (pick highest-leverage):**
  (a) **SAT model construction + dispatch wiring** so the EUF path returns
      replay-checked `sat` models and `check_auto`/QF_UF instances route through it
      (completes the "model replays" exit of T1.5.5 for pure UF).
  (b) **`TheorySolver` trait + online theory propagation** (T1.5.1–T1.5.4): refactor
      the offline loop into an incremental theory plugged into the warm CDCL core
      (uses the e-graph's push/pop), with lazy `get_antecedents` and final-check.
  (c) **P1.6 theory combination (e-graph UF + bit-blaster BV)** for *complete*
      QF_UFBV — the offline loop today only proves UNSAT, since the uninterpreted
      abstraction ignores BV semantics.
  Recommend (a) then (c): a complete, model-replaying QF_UF path is the cleanest
  Track-2 unlock; (b) is an efficiency refactor. Deferred Track-1 perf option still
  open: T1.2.8 two-level AIG rewriting in `axeyum-aig`.

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
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — T1.2.1 trail + T1.2.2 propagate_values + T1.2.3 solve_eqs landed (model-sound, unit-tested, 36 tests). Next: wire the preprocessing pipeline into the solve path + measure; then elim_unconstrained / max_bv_sharing / bv_slice / AIG 2-level (T1.2.4–T1.2.9) |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | TODO |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | **DONE** — `axeyum-egraph` (ADR-0032): hash-cons + union-find + congruence cascade (T1.4.1/2), proof-forest `explain` (T1.4.3), backtrackable push/pop (T1.4.4), independent `check_congruence` (T1.4.5), per-class theory-var lists (T1.4.6). 17 tests incl. brute-force + backtracking property tests |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive) + `prove_unsat_lazy` (offline DPLL(T): boolean skeleton + e-graph theory check + explain-based blocking clauses). Sound UNSAT over arbitrary boolean structure, conflicts independently checked. Next: `TheorySolver` trait + online propagation (T1.5.1–T1.5.4), SAT model construction, theory combination with BV (P1.6) for complete QF_UFBV |
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

- **2026-06-16** — **EUF prover differentially validated** (commit a73d34a).
  `tests/euf_egraph_diff.rs` cross-checks `prove_unsat_lazy` against the trusted
  Ackermann `QF_UFBV` path: 6 instances (congruence/transitivity/two-arg conflicts,
  a disjunctive refutation, two sat) all agree. The "verified against the eager
  path" check (T1.5.4).
- **2026-06-16** — **P1.5 lazy DPLL(T) loop** (commit 8d97081). `prove_unsat_lazy`
  lifts the conjunctive prover to arbitrary boolean structure: equality atoms →
  fresh Boolean vars, boolean skeleton solved by sat-bv, model theory-checked on
  the e-graph, conflicts turned into explain-based blocking clauses, re-solve to
  fixpoint. Sound EUF UNSAT over disjunctions the conjunctive pass can't see. 8
  euf_egraph tests.
- **2026-06-16** — **P1.5 first slice: EUF congruence UNSAT prover** (commit f69aa40).
  `axeyum-egraph` wired into the solver; `prove_unsat_by_congruence` abstracts
  assertions as uninterpreted equality logic and proves UNSAT by congruence +
  constant distinctness (sound, incomplete), every conflict re-checked by the
  independent `check_congruence` and carrying an UNSAT core. 5 tests. The EUF-on-
  the-e-graph core; next is the lazy boolean loop for full QF_UF.
- **2026-06-16** — **P1.4 e-graph keystone COMPLETE: T1.4.4–T1.4.6** (commits
  c47dc0c, 2c735b5, d81bf46). T1.4.4 backtrackable push/pop trail (path compression
  dropped; every mutation trailed; 150-iteration rebuild property test). T1.4.5
  independent `check_congruence` (own union-find + congruence closure re-validates
  every `explain`). T1.4.6 per-class theory-variable lists (the interface-equality
  bus, merge-propagated + backtracked). The e-graph is now a complete keystone;
  next is P1.5 CDCL(T).
- **2026-06-16** — **T1.4.3 e-graph explanations** (commit 0c5840f). Nieuwenhuis–
  Oliveras proof forest alongside the union-find; `merge(a,b,reason)` records edges;
  `explain(a,b)` returns the minimal input-reason set entailing the equality
  (explain-to-LCA, congruence premises recovered recursively). Soundness
  property-tested (replay named merges → re-derives the equality). 9 tests.
- **2026-06-16** — **P1.4 e-graph keystone started: T1.4.1+T1.4.2** (commit eb3e9e6).
  New dependency-free `axeyum-egraph` crate (ADR-0032): hash-consed e-node creation
  over a root-keyed signature table, path-compressing union-find, and the
  deferred-merge cascade that re-canonicalizes parents to close transitive
  congruence. 5 tests incl. a 300-iteration brute-force congruence-oracle property
  test. Next: T1.4.3 explanations.
- **2026-06-16** — **bench `--preprocess` + measurement** (commit 0c594ac).
  propagate_values+solve_eqs wired into the bench setup phase; trail threaded to
  reconstruct the model before the original-assertion replay. Curated A/B: 32/43,
  agree=32, DISAGREE=0, 0 replay failures, PAR-2 1.060 s (≈ baseline 1.063);
  DAG reduced on 5/43. `just bench-qfbv-curated-preprocess`,
  `qfbv-curated-sat-bv-preprocess-vs-z3-2s.json`.
- **2026-06-16** — **`check_with_preprocessing` wrapper** (commit 86cd28a). Façade
  entry that runs propagate_values+solve_eqs before a backend, composes their
  ModelReconstructionTrails, and on `sat` reconstructs + replays against the
  original assertions (mirrors check_with_array_elimination; wraps at the
  `&mut`-arena layer). 5 integration tests through the real sat-bv backend. Not yet
  on the bench/default path — see Current focus for the setup-phase wiring approach.
- **2026-06-16** — **T1.2.3 solve_eqs** (commit e1682ce). Top-level `(= x t)`
  oriented to `x := t` with a memoized occurs-check, substituted to a fixpoint,
  recorded in the trail; generalizes propagate_values. DAG interning keeps
  substitution linear. 200-trial randomized chain-of-definitions reconstruction
  test. axeyum-rewrite at 36 tests. Next: wire propagate_values+solve_eqs into the
  solve path (the `check_with_preprocessing` wrapper) and measure.
- **2026-06-16** — **P1.2 started: T1.2.1 model-reconstruction trail + T1.2.2
  propagate_values** (commit d5c49b6). New `axeyum_rewrite::ModelReconstructionTrail`
  (eliminated-symbol → defining-term steps, reverse-replay `reconstruct`, composable
  `append`) generalizing the bit-blast-lift / array-`project_model` / BVE-reconstruct
  patterns. First consumer `propagate_values`: top-level `var = const` (and bare /
  negated Boolean) facts substituted to a fixpoint, model-sound via the trail
  (proven end to end). Pure axeyum-rewrite, 32 tests. **Next:** `solve_eqs` (T1.2.3,
  `var = term` elimination — the big variable-count win) and wiring the preprocessing
  pipeline into the solve path + measuring the curated slice.
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
