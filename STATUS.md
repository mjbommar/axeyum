# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

## Current focus

- **P2.6 quantifier e-matching vertical — keystone-complete, wired & validated**
  (2026-06-16): trigger *inference* (single-cover + greedy multi-pattern set
  cover), congruence-aware multi-pattern join, the instantiation fixpoint loop
  (verified multi-round chaining), nested triggers fired purely via congruence
  (involution test), **dispatch wiring into `solve`** (too-wide-BV / infinite-domain
  quantifier fallback → keystone before MBQI), and the capability ledger/matrix
  updated. All gated.
  - **MBQI-on-keystone assessed, deliberately deferred:** `eval` does support UF
    application against a model (`eval.rs:200`), so it's feasible — but the
    keystone's trigger e-matching already instantiates at *all* congruent ground
    matches (strictly more aggressive than model-guided selection), and the
    existing value-based `prove_unsat_by_mbqi` already does arithmetic
    bound-probing. A ground-term-candidate MBQI would be near-duplicate machinery
    that only helps *trigger-less UF universals* (rare). Skipped as low marginal
    value vs. the duplication/maintenance cost; revisit only if a real corpus shows
    the gap.
  - **Next action (new thrust):** P1.5 — `TheorySolver` trait + online theory
    propagation, lifting `euf_egraph`'s offline DPLL(T) (`prove_unsat_lazy`) into
    an online CDCL(T) theory interface (assert-literal / theory-propagate /
    explain / final-check on the backtrackable e-graph). This is the keystone for
    P1.6 theory combination (interface equalities → complete QF_UFBV without
    Ackermann), the real z3-parity gap. Larger refactor → start with a fresh
    context. Secondary: migrate `axeyum_rewrite`'s bespoke trigger closure onto the
    keystone to unify on the validated path.
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
- **SAT model construction + dispatch wiring DONE** (commits c08c763, 6ce85b0):
  `check_qf_uf` decides QF_UF with replay-checked `sat` models (differentially
  validated vs Ackermann), and `check_auto` now routes UF instances through it
  first (congruence fast-path), falling back to the complete Ackermann bit-blast on
  `unknown`. Full solver test suite + micro bench regression-free.
- **Next task — P1.6 theory combination (e-graph UF + bit-blaster BV)** for
  *complete* QF_UFBV. Today the EUF path fast-paths only when the answer is settled
  by congruence alone; a theory-consistent boolean model whose constructed values
  violate BV arithmetic → `unknown` → Ackermann fallback. Combination closes this:
  on a theory-consistent boolean model, send the e-graph's induced equalities AND
  disequalities (from the class structure + the asserted diseqs) to the bit-blaster
  as BV constraints and let it decide / produce the model — or the Nelson–Oppen
  interface-equality exchange on the `th_var` bus (T1.4.6) the e-graph already
  carries. Read `docs/plan/track-1-engine/P1.6-theory-combination.md`. Also open:
  the `TheorySolver` trait + online propagation (T1.5.1–T1.5.4 efficiency refactor),
  and the broader Track 2 theories (lazy arrays P2.2, datatypes P2.9, quantifiers/
  e-matching P2.6) which all migrate onto the e-graph + CDCL(T) loop.
- **T1.2.8 AIG two-level rewriting — attempted, reverted (negative result,
  2026-06-16).** `axeyum-aig` already does level-0/1 rewrites (constants,
  idempotence, contradiction, OR-absorption, consensus). Adding the bitwuzla
  positive-AND-operand subsumption/contradiction (`x∧(x∧y)=x∧y`, `x∧(¬x∧y)=0`) was
  correct + semantics-tested but **regressed a borderline Float128 fp.fma**
  (`decides_symbolic_float128_fma`) from sat to a batsat **timeout** — CNF-structure-
  induced SAT chaos on a borderline instance. Reverted (no net benefit measured, a
  concrete regression). If retried: gate behind a flag and measure broadly on the
  curated slice + the FP tests before enabling; AIG rewrites need measurement, not
  blind application (the P1.2 methodology point, reconfirmed).

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
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive), `prove_unsat_lazy` (offline DPLL(T)), and `check_qf_uf` (full decision with **replay-checked sat models** from e-graph classes + function interps). Conflicts independently checked; **differentially validated vs Ackermann**. T1.5.5 met for the equality/UF fragment. **Online `TheorySolver` trait + `EufTheory` landed** (one backtrackable e-graph, explained conflict cores, lockstep push/pop) — the online theory side of the loop. Remaining: drive it from an online CDCL search with theory propagation (T1.5.1–T1.5.4) + dispatch wiring; theory combination with BV (P1.6) for complete QF_UFBV |
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
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | WIP — full e-matching vertical slice on the keystone: `enumerate_apps` + `ematch` engine + `instantiate_forall_via_egraph` (congruence-aware, single/multi-var, nested/joint triggers) + `prove_quantified_unsat_via_egraph` (the **instantiation loop**: instantiate → re-solve via `check_auto` → fixpoint, sound UNSAT). trigger *inference* (single + multi-pattern set cover) landed; loop **wired into `solve`** (infinite/too-wide-domain fallback → keystone before MBQI). Next: MBQI on the keystone (model-guided instance selection over the congruence), then migrate `axeyum_rewrite`'s bespoke closure onto the keystone. (Verified: the multi-pattern join is already congruence-correct — `ematch` binds variables to canonical e-class roots and `trigger_to_pattern` never mutates the union-find, so raw `ENodeId` equality in `merge_substitutions` *is* root equality.) |
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

- **2026-06-16** — **P1.5 online `TheorySolver` trait + `EufTheory`** (pending commit).
  First slice of the *online* CDCL(T) theory interface (vs the offline
  `prove_unsat_lazy` model-enumeration): `TheorySolver` (`assert(atom,value)` →
  `Ok` or a conflicting `Vec<TheoryLit>`; `push`/`pop`) and `EufTheory`, an EUF
  solver over **one** backtrackable keystone `EGraph` kept in sync with the search.
  Asserting `eq` merges sides (reason = atom index, so `EGraph::explain`
  reconstructs the conflict core); asserting `¬eq` records a disequality; conflicts
  = a violated disequality or two distinct constants forced equal. 4 tests
  (congruence conflict + explained core, merge backtracked on `pop`, constant
  collision, transitivity core). Exported; lays the theory side of the CDCL(T) loop
  that P1.6 combination builds on.
- **2026-06-16** — **P2.6 congruence-only nested trigger test** (commit 8e0a61c).
- **2026-06-16** — **P2.6 multi-round instantiation test** (commit 8d0a9e4).
  Added `instantiation_loop_refutes_across_multiple_rounds`: a refutation that
  only closes because round 1 (`∀x. f(x)=g(x)` over ground `f(a)`) introduces
  `g(a)`, which round 2 (`∀x. g(x)=0`) can then match — proving the fixpoint loop
  genuinely chains instances across rounds, not just single-shot.
- **2026-06-16** — **P2.6 keystone wired into `solve` dispatch** (commit 2a6d4bd).
  The infinite/too-wide-domain quantifier fallback in `solve` now tries the
  congruence-aware `prove_quantified_unsat_via_egraph` (keystone) **before** MBQI:
  finite-domain expansion refuses domains wider than `QUANT_EXPAND_BIT_LIMIT`
  (2¹⁰), and since UF is finite-scalar-only in the IR, a `∀x:BV32. f(x)=…`
  quantifier surfaces there — exactly where e-matching modulo the ground
  congruence refutes (fire `f(x)` at ground `f(a)`). Only ever returns `unsat`
  (sound, instances implied) or falls through to MBQI on `unknown`. New
  `auto::tests` dispatch test proves the `solve` → keystone route end to end.
- **2026-06-16** — **P2.6 multi-pattern trigger inference** (commit c82c175).
  `select_triggers` infers a (possibly multi-term) trigger set from the body when
  no single subterm covers all bound variables — single-cover preferred, else a
  greedy set cover over function-app candidates. `instantiate_forall_via_egraph`
  e-matches each trigger and joins the per-trigger substitutions consistently on
  shared variables (`merge_substitutions`), so `∀x,y. f(x)=g(y)` instantiates from
  `{f(x), g(y)}`. 9 qinst tests.
- **2026-06-16** — **P2.6 e-matching instantiation loop** (commit 6902f84).
  `prove_quantified_unsat_via_egraph`: split ground/universals, then instantiate →
  re-check (`check_auto`) → fixpoint; ground-unsat ⇒ sound refutation. Closes the
  e-matching vertical slice on the keystone (e-graph → ematch → instantiation →
  ground refutation). 8 qinst tests.
- **2026-06-16** — **P2.6 multi-variable quantifiers** (commit 0fdf634).
  `instantiate_forall_via_egraph` now peels nested `∀x.∀y.…`, requires a trigger
  covering all bound variables, maps each to its own `Var(index)`, and builds the
  full substitution. With nested/multi-arg trigger support, the keystone
  instantiation covers single/multi-var quantifiers with `f(g(x))` / `g(x,y)`
  triggers. 6 qinst tests.
- **2026-06-16** — **P2.6 nested/multi-arg triggers** (commit c658839).
  `instantiate_forall_via_egraph` generalized from unary to arbitrary triggers via
  the full `ematch` engine: `f(g(x))`, `g(x, a)` (ground parts matched by class).
  5 qinst tests.
- **2026-06-16** — **P2.6 keystone quantifier instantiation** (commit 5ac7343).
  `instantiate_forall_via_egraph` wires `ematch` into instantiation: builds the
  ground e-graph (merging ground equalities), e-matches a unary trigger, emits
  congruence-aware instances (a=b ⇒ f(a),f(b) fire once). The keystone now drives
  EUF and quantifier instantiation end to end. 3 tests.
- **2026-06-16** — **P2.6 e-matching engine** (commit 30ebec9). `EGraph::ematch`:
  full single-pattern matching modulo congruence (nested patterns, repeated-variable
  consistency, all substitutions) — the matching engine quantifier instantiation
  runs. Built on the keystone; matching is intrinsically up to congruence. 23 tests.
- **2026-06-16** — **P2.6 e-matching foundation** (commit ff53168).
  `EGraph::enumerate_apps(decl)` — distinct applications of a function symbol modulo
  congruence (one per class, canonical arg roots), the single-symbol trigger that
  drives quantifier instantiation. The first step toward e-matching / unbounded
  quantifiers (the biggest functional gap; today only finite-domain expansion).
- **2026-06-16** — **QF_UF upgraded to checked** (commit 799cd43); **T1.2.8 AIG
  rewrite attempted + reverted** (regressed a borderline FP128 instance — negative
  result recorded).
- **2026-06-16** — **EUF dispatch path hardened** (commit 21ca0a9). 120-iteration
  randomized differential test: random pure equality/UF formulas decided by both
  `check_qf_uf` and Ackermann must agree. Hardens the now-production EUF fast-path.
- **2026-06-16** — **EUF e-graph path wired into `check_auto`** (commit 6ce85b0).
  UF instances try `check_qf_uf` (congruence fast-path) before the Ackermann
  bit-blast; sound for QF_UFBV (replay-checked sat, re-checked unsat), Ackermann
  fallback on unknown. Full solver test suite + micro bench regression-free.
- **2026-06-16** — **T1.5.5 `check_qf_uf` with replay-checked sat models** (commit
  c08c763). Full QF_UF decision on the e-graph: lazy DPLL(T) + a candidate model
  built from e-graph classes (distinct class values, constants pinned, function
  interpretations) replayed against the originals as the soundness gate. Decisions
  + models differentially agree with Ackermann on all 6 cases. The "model replays"
  half of T1.5.5.
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
