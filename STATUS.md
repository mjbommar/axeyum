# STATUS.md — live tracker

The mutable state file. [PLAN.md](PLAN.md) is the map; this is where we are.
Update the **Current focus**, the **phase table**, and the **changelog** every
session. Status legend: `TODO` · `WIP` · `DONE` · `BLOCKED`.

## Current focus

- **Session 2026-06-19 — robustness + proof certs + capability-gap sweep (resume here).**
  **28 validated commits**; whole `axeyum-solver` crate green on test/clippy/doc/fmt (977
  tests; the workspace fmt gate, previously red on committed `axeyum-scenarios` drift, is now
  clean). Method: 4 read-only *capability-gap probe* passes (each found concrete reproducing
  queries; see the per-commit changelog), closing every tractable in-`solver` finding, plus
  the proof-cert widening below. Highlights beyond the proof track:
  - **Robustness (the no-OOM/no-hang rules):** NRA OOM bound (below); the **integer-NIA solve
    HANG fixed** (a regression from the new int-blast width ladder — `a*b≠b*a` livelocked
    ignoring the timeout; now deadline-threaded + trimmed ladder + commutative canonicalization
    → fast `Unsat`); the **optimizer** now honors `config.timeout` (`*_with_config` variants),
    decides `mod`/`div` objectives, and degrades fragment-out-of-scope objectives to graceful
    `OptOutcome::Unknown` (never `Err`). Probing found **no OOM/panic/unsoundness** anywhere.
  - **z3 feature breadth — measured gaps closed:** datatype Int/Real fields (was a hard `Err`),
    guarded-finite Int `∀`, sat-side **valid-universal** elimination (incl. nested `∀`), the
    NIA ground-vs-`∃` inconsistency, **EUF-over-Real (QF_UFLRA)** routing (was a hard `Err`),
    `bv2nat` out-of-range UNSAT, integer-NIA UNSAT via real relaxation, and the QF_LIA evidence
    certificate (E). The solver is now solid across arrays, mixed theories, strings, FP-via-BV,
    and most quantifier shapes (verified by the 3rd/4th passes).
  - **Process note:** sub-agents must be re-validated with **`cargo fmt --all --check`** (clippy
    doesn't catch fmt drift) and an **OS `timeout` guard** (to prove termination, not trust it);
    rust-analyzer diagnostics after a sub-agent run are frequently STALE — verify with a real
    build/clippy, not the diagnostics.
  - **NRA OOM gap CLOSED** — deterministic `MAX_CROSS_PRODUCTS` admission bound (graceful
    `unknown`, never OOM, bounded *or* unbounded). The standing-rule violation is retired.
    See the 2026-06-19 changelog + `scripts/mem-run.sh` / `just test-guarded` (64 GiB cap).
  - **Transitive-closure cert widening DONE & fully validated** — both the Ackermann
    (`prove_qf_ufbv_unsat_alethe`) and array-elim (`prove_qf_abv_unsat_alethe_via_elimination`)
    certificates now discharge argument/index equalities holding by *transitive closure*
    of asserted equalities (`a=b ∧ b=c ⊢ a=c`) via `eq_transitive` chains, not only direct
    assertions. Strictly additive (existing certs byte-unchanged), validated at **all three
    levels**: in-tree `check_alethe`, external **Carcara**, and **Lean-kernel**
    reconstruction to `False`.
  - **Zero-trust certs WIRED into `produce_evidence` (Ackermann + array + datatype)** — a
    QF_UFBV / QF_ABV / QF_DT `unsat` in the covered fragment now carries a zero-trust-hole
    Alethe certificate (reductions *proven* via `eq_congruent`/`eq_transitive`, not trusted
    DRAT) via `zero_trust_alethe_certificate`. Retires the Ackermann / ArrayElim /
    DatatypeElim trust holes **in practice** for those fragments (the ledger stays
    binary "trust hole" — coverage is fragment-level, not universal). Also fixed
    `evidence_route` misrouting datatype queries to the BV path (see changelog).
  - **Next proof-track task (resume) — certify general read-over-write (ROW-distinct)**
    for the array-elim trust hole: `select(store(a,i,v),j) → ite(i=j, v, select(a,j))`,
    `i≠j`. **Dependency chain mapped this session:** (1) the checker rule **already exists**
    and is tested — `read_over_write` in `axeyum-cnf/src/alethe.rs` (`is_read_over_write`
    L1424, tests L4364); (2) the **emitter** `prove_qf_abv_unsat_alethe_via_elimination`
    declines store rewrites because `ArrayElimination` (`axeyum-rewrite/src/arrays.rs`)
    exposes only `selects()`/`abstraction()`, **not the ROW redexes/expansions it performed**
    — so emitting `read_over_write` steps needs `eliminate_arrays` to expose them
    (**coordinate with the `axeyum-rewrite` agent**) or fragile re-derivation from the
    originals; (3) **Lean reconstruction has no `ite`/`read_over_write` support** yet
    (`reconstruct.rs`), so closing the Lean loop needs that too. So ROW-distinct is a
    cross-crate, partly-coordination-gated, multi-slice effort — not a clean in-`solver`
    increment. Other open trust holes (lowest pedantic first): `int-blast` (3),
    `xor-gaussian` (3), `datatype-elim` (4), `fpa2bv` (5) — each a from-scratch certificate.
  - **Remaining frontier (the in-`solver` tractable gap-cycle is exhausted; these are the hard
    keystones / coordination-gated items the 4 passes surfaced):**
    - **arith-UF SAT model (gap C, keystone, COORDINATION-GATED on `axeyum-ir`):** QF_UFLIA/
      UFLRA `sat` returns `Unknown` because an `Int`/`Real`-sorted UF's function-table model
      can't be built — `FuncValue` and the ground evaluator key function applications by
      `Value::scalar_code()` (`axeyum-ir/src/eval.rs:232`, panics on Int/Real), so both the
      table representation AND `eval`'s lookup need Int/Real-value keys (an `axeyum-ir` change),
      then `euf.rs::project_replay_build` can build + replay it. UNSAT is decided; only the
      SAT-side model build is blocked. NOT a clean in-`solver` increment.
    - **`∃∀` alternation (keystone):** `∃y.∀x. x+y≥x` → `Unknown` (should be SAT, y=0). After
      skolemizing `∃y→c`, `∀x. x+c≥x` is NOT valid for arbitrary `c` (valid only when `c≥0`),
      so the valid-universal pass can't decide it; needs `∃`-witness selection over the
      universal's validity condition (LIA/LRA quantifier elimination, or model-based).
    - **Irrational NRA roots / CAD-lite (keystone):** `x*x==2 ∧ x>0` (Real) → `Unknown`
      (witness √2); the linear-abstraction + point-lemma NRA never finds irrational witnesses.
    - **Coordination-gated (other lanes):** array-of-array / datatype-element arrays (needs
      `Sort::Array` to carry element *sorts* — `axeyum-ir`); first-class `(declare-fun x Float…)`
      through `solve`/SMT-LIB (front-end wiring, `Sort::Float` exists); `(reset)` clearing +
      `(declare-sort)` (`axeyum-smtlib`); ROW-distinct emitter exposure (`axeyum-rewrite`).

- **Destination-2 advanced & a destination-3 milestone landed (2026-06-18).** See
  the two 2026-06-18 changelog entries for detail. In short:
  - **Real Lean 4 kernel now checks reconstructed refutations** (`render_lean_module`
    / `prove_unsat_to_lean_module`, gated `tests/lean_crosscheck.rs`): QF_UFBV/LRA/∀/∃
    refutations type-check in a real `lean` toolchain with `#print axioms` showing no
    `sorryAx`. (Toolchain installed via `elan`; analogue of the Z3 oracle.)
  - **Destination-2 lever found, fixed, measured, decided.** Fair public-slice
    head-to-heads vs Z3 (committed baselines): lazy-bv is **inert** on p4dfa (0/113
    heavy ops); **word-level reduction is the lever** — after fixing the unbounded
    `solve_eqs` (deterministic fuel, `solve_eqs_bounded`), `--preprocess` decides
    **4/113 @3s and 7/113 @20s vs eager 2/3**, DISAGREE=0. Ratified in **ADR-0037**
    (reduction is the destination-2 priority; batsat stays default; custom cores
    specialized). The full pipeline is now wired into the default `solve()` path.
  - **Precise next steps (resume here):** (1) **deeper word-level reduction** to pull
    the 6 remaining `EncodingBudget` instances below the encode ceiling and shrink the
    99 timeout CNFs (AC-tree flattening / `ite`-chain simplification / `bv_slice` /
    `max_bv_sharing`) — *this is `axeyum-rewrite` P1.2, the concurrent agent's active
    area; coordinate to avoid collision*; (2) ~~flip `SolverConfig::preprocess`
    default-on~~ **DONE (2026-06-18, commit `6cb2f1b`)** — `preprocess` now defaults
    on; the default `solve()` path runs the full reduction pipeline, guarded
    (skip-on-quantifier + best-effort fall-back to the original on any pass error);
    full-workspace behaviour check green (103 binaries). ADR-0034 updated.
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
- **P3.2 Alethe resolution-layer checker — first slice DONE** (2026-06-16): the
  Alethe (veriT/cvc5 SMT proof format) IR + s-expr `parse_alethe`/`write_alethe` +
  a sound `check_alethe` for the propositional resolution layer in
  `axeyum-cnf::alethe`. A `resolution`/`th_resolution` step is verified by
  `{premises, ¬conclusion}`-UNSAT, decided by the **proof-producing** core and
  **re-checked by `check_drat`** (so each accepted step's entailment is itself
  independently verified, not trusted to the SAT search); a step is recorded only
  after it verifies; UNSAT requires a verified empty clause `(cl)`. 7 tests incl. 3
  negative/rejection. The resolution rung connecting to the DRAT/LRAT clausal
  proofs. **`lrat_to_alethe` bridge landed**: a CNF/QF_BV UNSAT now goes
  `solve_with_drat_proof → DRAT → LRAT → Alethe`, re-checkable by *both* `check_lrat`
  and `check_alethe` (end-to-end test). **Typed-term IR landed**:
  `AletheTerm` (`Const`/`App`) replaces opaque-string atoms (resolution keys on the
  canonical `key()`), plus the **core EUF theory rules**
  `eq_reflexive` / `eq_symmetric` / `eq_transitive` / `eq_congruent` and the
  **Boolean CNF-introduction** rules `and_pos` / `and_neg` / `or_pos` / `or_neg`,
  checked structurally against their exact tautology shapes (strict, order-sensitive;
  broken shapes rejected). plus the entailment-checked
  clause-manipulation rules `contraction`/`reordering`/`weakening`. 16 tests.
  **EUF proof EMISSION** (`prove_qf_uf_unsat_alethe`): the solver turns a congruence
  conflict into an Alethe proof — **transitivity** (`assume`s + `eq_symmetric` for
  reversed edges + `eq_transitive` + `resolution` to `(cl)`) and **depth-1
  congruence** (`f(x⃗) ≠ f(y⃗)` with each `xᵢ=yᵢ` derived by transitivity, then one
  `eq_congruent` step). **Self-validated** — returns `Some` only when `check_alethe`
  accepts, so a construction bug yields `None`, never a wrong proof. The proof track
  is bidirectional (check + emit) for the EUF transitivity + depth-1-congruence
  fragment, including **nested** structural congruence (`f(g(a)) ≠ f(g(b)) ∧ a=b`)
  via a recursive `derive_eq` (transitivity-then-congruence, recursing on args). 10
  tests, each re-checked. **EUF emission is now general** (2026-06-16): `prove_qf_uf_unsat_alethe` was rebuilt
  around `EGraph::explain_steps` — it builds an e-graph over the conflict core (all
  terms added before merging, so congruence edges survive in the proof forest),
  walks the structured explanation between the disequality sides, and converts each
  `Input`→assume / `Congruence`→`eq_congruent` (recursing on args), threaded through
  `eq_transitive`. This handles the **mixed congruence-in-transitivity** case
  (`f(a)=c ∧ a=b ∧ f(b)≠c`) the old bfs emitter returned `None` on — any congruence
  refutation now emits a `check_alethe`-accepted proof (self-validated). The bfs
  helpers were removed. **`term_to_alethe` converts any interpreted-op application**
  (not just `Apply`/`Eq`), so emission covers congruence over interpreted operators
  too — e.g. **array extensionality** (`a=b ∧ select(a,i)≠select(b,i)` ⇒ a checkable
  `eq_congruent` proof), pairing with the array-extensionality decision in dispatch.
  **Arithmetic `la_generic` checking landed** (`check_alethe_lra`): a linear-arith
  tautology clause is verified by `¬clause`-UNSAT via the **Farkas-certified**
  `check_with_lra` (coefficients re-derived, not trusted); `axeyum-cnf` gained a
  pluggable `check_alethe_with(_, extra)` callback so it stays arithmetic-free.
  **`la_generic` EMISSION landed** (`prove_lra_unsat_alethe`): an unsat LRA
  conjunction → an `la_generic` + resolution Alethe proof, **self-validated** by
  `check_alethe_lra` (so axeyum both checks AND emits arithmetic proofs, the full
  "trusted small checking" identity for LRA). **`lia_generic` (integer) checking +
  emission landed** (`prove_lia_unsat_alethe`): the integer counterpart, decided by
  the **integer-complete** `check_with_lia_simplex` so integrality is honored —
  `(cl (<= x 0) (>= x 1))` is *accepted* by `lia_generic` (no integer in the open
  interval) yet *rejected* by the real `la_generic` (`x=0.5` falsifies it), the
  distinction enforced by a dedicated test. Linear `*` guarded to a constant factor
  (genuine `var*var` ⇒ rejected); integer numerals parse as plain `i128`; emission
  self-validated via `check_alethe_lra`. Remaining (P3.2/3.3): more BV theory
  rules; emit Alethe for the *reductions* (P3.5: array/function elimination,
  int-blasting); Carcara CI cross-check; extract `axeyum-alethe` crate (ADR).
- **P2.9 datatypes — structural refutation DONE** (2026-06-16):
  `prove_datatype_unsat_structurally` — the three datatype structural axioms over a
  term-level union-find: **acyclicity** (`x = cons(h, x)` ⇒ unsat), **distinctness**
  (`x = nil ∧ x = cons(…)` ⇒ unsat), and **injectivity** (`cons(h,x) = cons(h,y) ∧
  x ≠ y` ⇒ unsat — the datatype-*field* injectivity case the eager `build_dt_eq`
  relaxes away, the genuine gap-closer). Unions definite equalities, closes under
  injectivity while checking distinctness, then reports unsat on a same-class
  datatype disequality or a containment cycle. Sound (each union/edge forced by a
  definite (dis)equality + a datatype axiom) + wired into `check_auto_dispatch`
  ahead of the eager expansion. 7 tests (incl. two NOT-refuted SAT cases).
- **P3.1 LRAT checker + DRAT→LRAT elaborator — DONE** (2026-06-16): a second,
  independent UNSAT-proof checker alongside `check_drat`, in the stronger *clausal*
  LRAT format (every clause has an id; each addition carries antecedent hints, so
  checking is **linear** — follow the hints — not a RUP search). `check_lrat`
  (sound: accepts a clause only when its hint chain performs genuine RUP to a
  conflict; rejects a satisfied/under-determined/missing/never-conflicting hint),
  `elaborate_drat_to_lrat` (RUP DRAT — e.g. from `solve_with_drat_proof` — →
  hinted LRAT; RAT out of scope), `parse_lrat`/`write_lrat`. **3 negative
  (soundness) tests confirm rejection** (corrupted/dropped hint, non-entailed clause
  over a SAT formula, no-empty-clause ⇒ `Ok(false)`) + a **600-CNF random
  differential** (every UNSAT formula's CDCL DRAT proof elaborates and LRAT-checks,
  with text round-trip). First rung of the proof-checking ladder above DRAT.
- **P2.2 lazy arrays — first slice DONE (lazy select-congruence)** (2026-06-16):
  `check_qf_abv_lazy` — the array analogue of lazy Ackermann (a `select` is an
  application of a per-array read function). `eliminate_arrays` still does
  read-over-write eagerly, but the read-over-read consistency
  `i=j ⇒ select(a,i)=select(a,j)` is now added on demand (CEGAR) instead of the
  eager O(n²) per-array pairing. Sound (post-ROW abstraction is a relaxation ⇒ UNSAT
  transfers; consistent sat replays) + terminating. rewrite `ArrayElimination` now
  exposes `abstraction()` + `selects()` (eager `assertions()` byte-identical).
  **200-formula differential vs eager `check_with_array_elimination` — all jointly
  decided, all agreed (28 unsat)** + a select-congruence refutation and a
  store/select sat replay. Same regime caveat as lazy Ackermann: this defers the
  congruence pairing, not ROW; **full lazy ROW / on-demand store axioms / wide-index
  (>8-bit) arrays remain** (the eager path caps extensionality at 8-bit indices).
- **P1.5 online theory interface — DONE (theory side)** (2026-06-16): the online
  `TheorySolver` trait + `EufTheory` over one backtrackable keystone `EGraph` now
  exposes the full surface a CDCL(T) loop drives — `assert(atom,value)` (→ explained
  conflict core via `EGraph::explain`), `propagate()` (entailed equalities with
  reasons), `push`/`pop` (lockstep backtrack of merges, disequalities, and assigned
  state). 6 unit tests. This replaces the offline `prove_unsat_lazy` per-model
  e-graph rebuild with one incremental graph.
  - **Online DPLL(T) QF_UF decision procedure — DONE**: `prove_unsat_qf_uf_online`
    (refutation, 500-formula differential vs `prove_unsat_lazy`) + `solve_qf_uf_online`
    (full decider with replay-checked sat models, 400-formula differential vs
    `check_qf_uf`). The online *search* on one backtrackable e-graph now exists, not
    just the online theory.
  - **Online decider wired as the QF_UF fast path — DONE** (ahead of `check_qf_uf`,
    unknown-safe fall-through; full suite green).
- **P1.6 theory combination — first slice DONE (lazy Ackermann)** (2026-06-16):
  `check_qf_ufbv_lazy` — CEGAR/on-demand functional-consistency lemmas for QF_UFBV
  instead of the eager up-front Ackermann. Abstract apps → fresh vars, solve, add
  the lemma `(⋀ args_i=args_j) ⇒ fresh_i=fresh_j` only for a pair a candidate model
  violates, re-solve to fixpoint. Sound (abstraction is a relaxation ⇒ UNSAT
  transfers; consistent sat replays), terminating (each pair once). rewrite
  `FunctionElimination` now exposes `abstraction()` + `applications()` (eager
  `assertions()` byte-identical). **300-formula differential vs the eager
  `check_with_all_theories` — all jointly decided, all agreed (21 unsat).**
  - **Nested-application coverage added** (2026-06-16): two targeted lazy-QF_UFBV
    tests where an application's *argument is itself an abstracted application*
    (`f(f(a))`) — a refutation by nested congruence and a SAT involution that must
    project to a coherent function interpretation and replay. (The random
    differential grows its term pool with `f`/`g` apps so it nests too, but these
    pin it deterministically.)
  - **Design finding — model-based combination ≡ lazy Ackermann (important):** a
    full *online Nelson–Oppen* between the e-graph and BV would only add power over
    lazy Ackermann in a **non-model-based** regime. In the **model-based** regime
    (read a concrete BV model, check the shared-term arrangement) the model assigns
    *concrete values*, so congruence over them collapses to value-equality —
    including transitive chains — which the lazy path's raw model-eval already
    detects. The e-graph's *abstract* congruence only pays off when the BV theory
    participates in a shared CDCL(T) trail **without committing to a full model**,
    i.e. as an **online BV theory solver** (the P2.1 "BV theory-checker"), which does
    not exist yet. **Conclusion:** lazy Ackermann *is* the QF_UFBV combination for the
    model-based regime, and is arguably higher-assurance than eager (explicit,
    individually-valid functional-consistency lemmas added on demand vs a bulk
    syntactic reduction). The fuller online N-O is genuinely **gated on P2.1**; do not
    build a redundant model-based "combination" module.
  - **Dispatch wiring of `check_qf_ufbv_lazy` — deliberately deferred (methodology):**
    routing lazy-before-eager is a *performance* optimization (fewer up-front
    lemmas), not a correctness/capability gain — the eager `check_with_all_theories`
    already decides QF_UFBV completely. Per the project's benchmarking-first rule
    (encodings/perfwork gated on measured corpora) and the array-fragment interaction
    risk (lazy abstracts functions but not arrays), it stays an available, validated
    API until a real UFBV corpus shows eager-Ackermann lemma count is the
    bottleneck. The function is exported and ready.
  - **Next action (precise resume point):** the full online N-O is **gated on an
    online BV theory** (per the finding above), so the productive next step is to
    **start P2.1's BV theory-checker** — an incremental BV theory solver
    (`assert`/`propagate`/`explain`/`push`/`pop`, mirroring the `TheorySolver` trait
    `EufTheory` implements) that can participate in a shared CDCL(T) trail without
    materializing a full model. With both an online BV theory and the online
    `EufTheory`, the interface-equality combination (equality sharing over shared
    BV-sorted terms, split on undetermined interface equalities) becomes
    implementable and removes the Ackermann trust hole. That is a substantial new
    track — begin with fresh context. *Alternatively*, if pivoting tracks: P2.2 lazy
    arrays (ROW axioms on the e-graph) or P2.9 lazy datatypes (e-graph splitting)
    also build directly on the now-complete keystone. Secondary: migrate
    `axeyum_rewrite`'s bespoke trigger closure onto the keystone.
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
| P1.1 | SAT inprocessing (subsumption → BVE → vivification → glue tiers) | WIP — subsumption+BVE landed (T1.1.1/2), wired into the solve pipeline (T1.1.3), made occurrence-list near-linear + time-bounded (T1.1.4): safe, no regression, but the curated unknowns are SAT-search-bound (→ P1.3) or BVE-resistant. **CDCL(XOR) foundation landed** (`gf2`/`xor_extract`/`xor_propagate` in `axeyum-cnf`) — the path-2 multiplier-wall attack: a sound GF(2) Gaussian engine + exact XOR-gate extraction + an entailment-checked propagation pass; slice 4 wires it into the live preprocess pipeline (measured). Vivification / glue tiers remain |
| P1.2 | Preprocessing (word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite) | WIP — T1.2.1 trail + T1.2.2 propagate_values + T1.2.3 solve_eqs landed (model-sound, unit-tested, 36 tests). **T1.2.4 elim_unconstrained landed** (`axeyum-rewrite::elim_unconstrained`): a variable occurring once under an invertible BV op (`bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg`) makes that subterm unconstrained → replaced by a fresh var, operator dropped (Z3's `elim_unconstr`); peels nested layers, terminates. Model-sound via the trail (`x := op⁻¹(u,w…)`; orphaned operands defaulted, sound by the inverse identity); wired into `check_with_preprocessing` after solve_eqs (opt-in, default-off per ADR-0034). 6 unit (incl. 300-trial randomized reconstruction) + 2 solver end-to-end. Next: measure on the public p4dfa slice; then max_bv_sharing / bv_slice / AIG 2-level (T1.2.5–T1.2.9) |
| P1.3 | SAT-core modernization (VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT) | WIP — the proof-producing core `solve_with_drat_proof` (`proof_sat.rs`) modernized: **VSIDS activity branching** (bump conflict-side vars, MiniSat-style decay, rescale-on-overflow; highest-activity unassigned var, ties to lowest index), **phase saving**, and **Luby restarts**. Sound by construction — every emitted clause is RUP and the proof is DRAT-checked, so a heuristic bug only slows search. All 231 cnf tests pass (incl. the 400-CNF differential vs BatSat + a new pigeonhole-4→3). NB the modern CDCL(XOR) core in `xor_cdcl.rs` already has VSIDS/Luby/LBD. Remaining: arena + packed watches, chronological backtracking; wire a modern core into the default path |
| P1.4 | Incremental e-graph (congruence + explanation + checker) **[keystone]** | **DONE** — `axeyum-egraph` (ADR-0032): hash-cons + union-find + congruence cascade (T1.4.1/2), proof-forest `explain` (T1.4.3), backtrackable push/pop (T1.4.4), independent `check_congruence` (T1.4.5), per-class theory-var lists (T1.4.6). 17 tests incl. brute-force + backtracking property tests |
| P1.5 | CDCL(T) loop (theory-as-extension, final-check, theory propagation) **[keystone]** | WIP — EUF on the e-graph: `prove_unsat_by_congruence` (conjunctive), `prove_unsat_lazy` (offline DPLL(T)), and `check_qf_uf` (full decision with **replay-checked sat models** from e-graph classes + function interps). Conflicts independently checked; **differentially validated vs Ackermann**. T1.5.5 met for the equality/UF fragment. **Online `TheorySolver` trait + `EufTheory` landed** (one backtrackable e-graph, explained conflict cores, lockstep push/pop) — the online theory side of the loop. Remaining: drive it from an online CDCL search with theory propagation (T1.5.1–T1.5.4) + dispatch wiring; theory combination with BV (P1.6) for complete QF_UFBV |
| P1.6 | Theory combination (th_eq bus, interface equalities) | WIP — **EUF+LIA/LRA combination landed & dispatched (QF_UFLIA/UFLRA), complete for conjunctive UNSAT**: `declare_fun` admits Int/Real UF sorts, and `check_with_uf_arithmetic` (eager Ackermann → `check_auto`) decides the squeeze + `f(x+0)≠f(x)` + nested `f(g(a))≠f(g(b))∧a=b` UNSAT; `check_auto` routes arithmetic UF there. SAT model for arith UF degrades to sound Unknown (project_model scalar-keys). Plus the combination primitives `theory_combination` (shared/propose/classify/arrangement) + `th_eq` bus (`theory_var_classes`/`interface_th_eqs`). Earlier: **T1.6.1 shared-term discovery landed** (`theory_combination::shared_terms`): the BV-sorted EUF/BV interface terms (arg-or-result of `Op::Apply` ∩ operand-or-result of an interpreted BV op), deterministic, the foundation for the `th_eq` bus + interface-equality case-splitting. Plus the earlier **lazy/on-demand Ackermann for QF_UFBV** (`check_qf_ufbv_lazy`): CEGAR functional-consistency lemmas (abstract apps → fresh vars; add `(⋀ args=) ⇒ result=` only on a model-observed violation; re-solve to fixpoint). Sound (relaxation ⇒ UNSAT transfers; sat replays) + terminating; 300-formula differential vs eager `check_with_all_theories` (all agree). Remaining: wire into dispatch; then the full online interface-equality (Nelson–Oppen) combination of the e-graph + BV to drop the Ackermann reduction entirely |
| P1.7 | PBLS local-search BV engine (portfolio) | WIP — **word-level WalkSAT landed** (`solve_local_search` + `PblsBackend`, `pbls.rs`): keeps a concrete Bool/BitVec(≤128) assignment, scores by evaluator-falsified assertions, nudges a variable in an unsatisfied assertion (greedy + WalkSAT noise + random restarts) toward a model. One-sided + sound: `Sat` only with an evaluator-verified model, never `Unsat`, `Unknown` (incl. out-of-scope sorts) otherwise. Read-only on the arena (fits the trait); deterministic (fixed seed, explicit budgets). 4 unit + an ignored 150-formula differential vs the eager backend (never contradicts). Remaining: integrate as a portfolio strategy; tune moves/budgets; measure on satisfiable corpora |
| P1.8 | Strategy & tactics (combinators + probes + per-logic scripts) | TODO |

### Track 2 — Theories & Breadth
| Phase | Title | Status |
|---|---|---|
| P2.1 | BV lazy blasting + word-level slicing + BV theory-checker | WIP — **destination-2 lever measured & scoped** (commits beee599/9846349, `docs/research/05-algorithms/lazy-bitblasting-p21-findings.md`). KEY FACT: lazy abstraction-refinement bit-blasting (`solve_lazy_bv_abstraction`, ADR-0019) is **built but NOT wired into default `solve()`/bench** — so the "~2-3/113 public QF_BV" picture is the *eager* mountain-builder. Measured (`tests/lazy_bv_curated_measure.rs`): lazy decides **incidental-heavy-op** cases with 0 multiplier blasts (`x=1∧x=2∧r=p·q` → unsat ~0ms, 0 refined), cracks `calypto_9` (sat, 2 ops refined), is a safe no-op when `ops=0` (public files), no shortcut on essential multiplier-equivalence. Next (coordinate on shared bench): lazy-bv bench backend → measure public 113 (DISAGREE=0) → opt-in `SolverConfig::lazy_bv` strategy → default-on ADR after net benefit. The highest-ROI perf move is wiring+measuring a built CEGAR bit-blaster, not a new algorithm |
| P2.2 | Arrays: lazy ROW axioms + extensionality + func_interp models | WIP — **lazy select-congruence** (`check_qf_abv_lazy`): read-over-read consistency added on demand (CEGAR) vs the eager O(n²) per-array pairing; sound (post-ROW abstraction relaxation ⇒ UNSAT transfers; sat replays) + terminating; 200-formula differential vs eager `check_with_array_elimination` (all agree). `eliminate_arrays` exposes `abstraction()`/`selects()`. **Array-extensionality refutation via congruence** wired into dispatch (`has_array` flag): `a=b ∧ select(a,i)≠select(b,i)` (incl. **wide-index** array equality the eager 2^iw enumeration refuses) is `unsat` by `prove_unsat_by_congruence` (select/store as UF; congruence valid for arrays). Remaining: **lazy ROW (on-demand store axioms)** for the SAT side of wide-index arrays; func_interp model polish |
| P2.3 | EUF on the e-graph (from Ackermann to incremental) | TODO |
| P2.4 | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | WIP — **multi-equation Diophantine infeasibility** (`prove_lia_unsat_by_diophantine`, commit 96f07a3): a conjunction of integer equalities that is rational-feasible but **integer-infeasible** is UNSAT — fraction-free Hermite-style integer Gaussian elimination reports a contradiction row (`0=c` or per-row `gcd ∤ rhs`), deciding the case B&B can't terminate on for unbounded vars and the single-equation GCD misses (e.g. `x+y=0 ∧ x−y=1 → 2x=1`). **Strictly generalizes & replaced** the single-equation `prove_lia_unsat_by_gcd` in dispatch (no regression). Sound (only integer-preserving row ops; `checked_*` → "not refuted" on overflow, never a wrong unsat; SAT systems never refuted, negative-tested). 11+2 tests. Remaining: Gomory/cube cuts; inequality-integrated cuts |
| P2.5 | NRA: incremental linearization → nlsat/CAD | WIP — linear-abstraction + sign/zero lemmas + McCormick + spatial B&B + point-lemma refinement already shipped. **Added threshold-1 monotonicity lemmas** — growing (`a≥1 ∧ b≥0 ⇒ r≥b`, decides `x≥1 ∧ y≥1 ∧ x·y<1`) and shrinking (`0≤a≤1 ∧ b≥0 ⇒ r≤b`, decides `0≤x≤1 ∧ y≥0 ∧ x·y>y` where only one operand is bounded so McCormick can't apply); two-operand only — **plus a refinement overflow safety net** (`too_large_to_refine`: stop refining past a 2³¹ magnitude bound, → `unknown` not a panic; hardens the exact-rational simplex against escalating witnesses). **Sum-of-squares lemmas landed (2026-06-18)** — `sos_lemmas`: for a pair `a,b` with `a·a`/`b·b`/`a·b` all abstracted, add `(a±b)² ≥ 0` over the result vars (sound), restoring the cross-product correlation independent abstraction drops, so **`a²+b² ≥ 2ab` / AM–GM₂ is now PROVED** (the Spivak SOS-frontier test promoted prompt-`Unknown`→`Unsat`; negative test confirms `a²+b²=2ab` stays sat). 26 NRA + 5 Spivak tests. Remaining: higher-degree / multi-var SOS (Bernoulli, general Cauchy–Schwarz) + nlsat/CAD for completeness |
| P2.6 | Quantifiers (MAM e-matching, trigger inference, MBQI, QE/MBP) | WIP — full e-matching vertical slice on the keystone: `enumerate_apps` + `ematch` engine + `instantiate_forall_via_egraph` (congruence-aware, single/multi-var, nested/joint triggers) + `prove_quantified_unsat_via_egraph` (the **instantiation loop**: instantiate → re-solve via `check_auto` → fixpoint, sound UNSAT). trigger *inference* (single + multi-pattern set cover) landed; loop **wired into `solve`** (infinite/too-wide-domain fallback → keystone before MBQI). Next: MBQI on the keystone (model-guided instance selection over the congruence), then migrate `axeyum_rewrite`'s bespoke closure onto the keystone. (Verified: the multi-pattern join is already congruence-correct — `ematch` binds variables to canonical e-class roots and `trigger_to_pattern` never mutates the union-find, so raw `ENodeId` equality in `merge_substitutions` *is* root equality.) |
| P2.7 | Strings (unbounded, full `str.*`, regex) | TODO |
| P2.8 | FP polish (unspecified values, min/max ±0, lazy conversion) | WIP — the FP theory is broad already (classification, compare, abs/neg/min/max, add/sub/mul/div/fma/sqrt/rem/roundToIntegral, fp→fp resize, fp→real/ubv/sbv). min/max ±0 confirmed correct (deterministic allowed choice). **Added integer→float conversion** (`from_ubv`/`from_sbv`, 2026-06-18): rounds a w-bit unsigned/signed-two's-complement integer to a dst float under a rounding mode (reuses `pack_value`; exact 0→+0; |x| via two's-complement read unsigned, correct for INT_MIN). Differential-tested vs Rust's native `as f32`/`as f64` (i32/u32→F32, i64/u64→F64; edges + 3000-case sweep, exact). Completes the `to_fp` family on the builder side. Remaining: SMT-LIB parse wiring for `(_ to_fp …)`/`to_fp_unsigned` over bv sources (axeyum-smtlib, coordinate); `to_fp` from real constants; unspecified-value edge polish |
| P2.9 | Datatypes lazy (e-graph splitting + occurs-check) | WIP — **structural refutation** (`prove_datatype_unsat_structurally`): acyclicity + distinctness + injectivity **+ congruence** (equal args ⇒ equal apps, e.g. `x=cons(h,a) ∧ y=cons(h,b) ∧ a=b ∧ x≠y`) over a term-level union-find; sound, wired into dispatch ahead of the eager expansion. 8 tests. Remaining: e-graph constructor *splitting* (case-split `is-c` on the keystone) for SAT-side completeness; exact field guards to remove the relaxed `unknown` cases; non-variable `is`/`select` terms |

### Track 3 — Proofs & Lean
| Phase | Title | Status |
|---|---|---|
| P3.0 | Reduction trust ledger (TrustId + pedantic levels) | DONE |
| P3.1 | LRAT clausal upgrade (+ in-tree check_lrat) | WIP — **`check_lrat` (hint-based linear checker) + `elaborate_drat_to_lrat` + parse/write** landed in `axeyum-cnf`, sound (3 negative/rejection tests) + 600-CNF differential; **threaded into the evidence export**: every `UnsatProof` (QF_BV + reduced QF_ABV/AUFBV/UF/LIA/datatype) now carries a self-checked LRAT certificate, `recheck` cross-checks it, `recheck_lrat` re-checks it in linear time, tamper-detected. Remaining: emit LRAT hints directly from the proof-producing CDCL core (vs post-hoc elaboration); RAT-step elaboration (negative hints) |
| P3.2 | Alethe term/proof IR + emitter (`axeyum-alethe`) **[critical path]** | WIP — **resolution-layer IR + parser/printer + sound `check_alethe`** in `axeyum-cnf::alethe`: `resolution`/`th_resolution` steps verified by `{premises,¬concl}`-UNSAT via the proof-producing core + `check_drat` re-check (entailment itself independently checked); verify-before-record; 7 tests incl. 3 rejection. Remaining: typed-term IR (vs opaque atoms), more rules, emit Alethe from solver runs, Carcara CI cross-check; extract `axeyum-alethe` crate (ADR) when the term IR lands |
| P3.3 | Alethe for QF_BV (bitblast_* + CNF rules + resolution/drat; Carcara CI) | WIP — **arithmetic `la_generic` checking** (`check_alethe_lra`): a linear-arith tautology clause verified by `¬clause`-UNSAT via the Farkas-certified `check_with_lra`; pluggable `check_alethe_with` callback keeps `axeyum-cnf` arithmetic-free. 5 tests incl. soundness rejections. **`lia_generic` (integer) checking+emission** added via `check_with_lia_simplex` (honors integrality; integer/real distinction tested). **Carcara cross-check harness (T3.3.5)**: EUF (transitivity+congruence), **LRA `la_generic`** (Farkas `:args` incl. equalities), and **clausal resolution** (`lrat_to_alethe`, T3.3.3) proofs all externally `valid`; gated test skips without the binary. Remaining: BV `bitblast_*` rules (T3.3.1–2) for the full QF_BV proof; LRA >2-atom (`and`) assertions; `lia_generic` is a Carcara hole. **Integer-systems certificate added** (commit c19f3ce): the multi-equation Diophantine refutation (P2.4) now emits an "integer Farkas" `DiophantineCertificate` (multipliers λ s.t. `Σ λᵢ·Eᵢ` is a `gcd ∤ const` contradiction row) with an independent `check_diophantine_certificate` re-deriving it from the originals — self-validated, tamper-tested. This is the in-tree route for integer-systems infeasibility that `lia_generic`/Carcara can't check |
| P3.4 | Embedded Alethe checker subset (self-checking) | TODO |
| P3.5 | Alethe for reductions (arrays → Ackermann → int-blast) | TODO |
| P3.6 | In-tree Rust Lean kernel (`axeyum-lean-kernel`, from nanoda) | WIP — **crate started (ADR-0036, commit db18886)**: destination-3 (Lean parity) foundation. `Name`/`Level`/`Expr` + de Bruijn ops (instantiate/abstract/lift) ported from `references/nanoda_lib`, adapted to axeyum's **lifetime-free Copy-id interning** (no `'a` leaks). Faithful level `leq`/`is_equiv`/`simplify` + param subst; Expr with `BinderInfo`; cached `num_loose_bvars`/`has_fvars`. 27 tests incl. translated nanoda level tests + de Bruijn laws. **Type-theory core landed (slice 2, commit e37da7b)**: `whnf` (beta/zeta), `def_eq` (lazy structural + Pi/Lam congruence + eta + proof irrelevance), and checking-mode `infer` (Sort/FVar/App/Lam/Pi/Let, IMax impredicativity) over the **environment-free fragment** — the kernel now TYPE-CHECKS terms (polymorphic identity infers `Π(α:Sort 0),α→α`, etc.). Faithful nanoda port; the env boundary (`Const`/δ, inductives/ι, projections, literal typing) errors explicitly (`KernelError`), never a wrong accept. 52 kernel tests. **Environment + Const δ landed (slice 3, commit f0f6e0d)**: non-inductive declarations (Axiom/Definition/Theorem/Opaque) with `ReducibilityHint`; `Environment` (deterministic `BTreeMap`); `add_declaration` is the trusted gate (type-checks each decl's type-is-a-sort + value `def_eq` declared type); universe instantiation; `infer(Const)`; δ-unfolding in `whnf`; faithful `lazy_delta_step` (height-based side choice, same-const short-circuit, Opaque/Axiom non-unfolding). The kernel now type-checks terms referencing globals (`id := λαx,x` admits + δ+β-reduces under application). 68 kernel tests. **Inductive layer started (slice 4, commit 4457594)**: `Declaration::{Inductive,Constructor,Recursor}` + `RecRule`; `add_inductive` (trusted gate: type whnf's to a Sort, constructor telescopes type-check + end in `I` + **non-recursive** field restriction); **recursor generation** (`I.rec : Π {motive}(minors…)(major), motive major`, with the generated type infer-self-checked) + **ι-reduction** (`I.rec … (c_i flds) → m_i flds`). Scoped to **non-recursive, non-parametric, non-indexed** inductives — enums (`Bool.rec` ι picks the right minor) + structures (`P.rec C m (mk x y) → m x y`); param/indexed/mutual + Prop-subsingleton large-elim DEFERRED (reject explicitly). **Recursive inductives landed (slice 5, commit 24607a9)**: DIRECT recursive fields (field type exactly `I`, e.g. `Nat.succ : Nat→Nat`) now admitted; `mk_recursor` adds one IH binder `motive f_j` per recursive field to each minor (`Nat.succ`'s minor = `Π(n:Nat)(ih:motive n), motive (succ n)`); recursive ι appends a recursive `I.rec … f_j` call per recursive field (`Nat.rec C z s (succ k) → s k (Nat.rec C z s k)`). **The kernel checks AND computes with `Nat` and binary trees** (end-to-end recursive normalization verified; recursor type infer-self-checks). Higher-order/reflexive fields, params, indices still rejected. 82 kernel tests. **Parametric inductives landed (slice 6, commit bc95c21)**: `add_inductive(num_params)` — leading binders are params (fixed across the family), recursive field = `I params` (generalizing bare `I`); recursor abstracts params before the motive and threads them through minors/IH/ctor-apps + recursive ι calls. **`List`/`Option`/`Prod`/`Sum` check + compute** (`List.rec α C cnil ccons (cons α a l) → ccons a l (List.rec … l)`; a length recursion normalizes; recursor types infer-self-check). Indices (`Eq`/`Vector`, a binder between params and the `Sort`) → `IndicesNotSupported` (deferred). 92 kernel tests. **Indexed inductives landed (slice 7, commit 223e81c)**: indices after params; the dependent motive ranges over indices + major; each minor applies the motive to the constructor's OWN index exprs; index-matching ι. **`Eq.rec` (the dependent eliminator used in every equality proof) generates, infer-self-checks, and ι-reduces on `refl`** (`Eq.rec α a motive m a (refl α a) → m`); an end-to-end transport/symmetry normalizes; a 2-ctor indexed family picks the right minor by index. Recursive-indexed (`Vector.cons`) → `RecursiveIndexedNotSupported` (deferred). 97 kernel tests. **The inductive layer now covers non-recursive + recursive + parametric + indexed — essentially all of Lean's inductive families** (bar recursive-indexed/nested/mutual + projections + literal typing + Prop-subsingleton elim). Next: **P3.7 Alethe→Lean reconstruction** (where this kernel finally checks reconstructed solver proofs — the destination-3 payoff) + the remaining minor inductive cases. |
| P3.7 | Alethe→Lean reconstruction (proof terms) | WIP — **foundation laid (commit ab2e615)**: `axeyum_lean_kernel::build_logic_prelude` declares the standard Lean logical foundation (`True`/`False`/`And`/`Or`/`Iff`/`Eq`/`Not`) through the trusted gates, and the kernel **type-checks real proof terms** — And.intro, and-elim (via And.rec), Or case analysis, Eq symmetry transport (checks + ι-reduces on refl), modus ponens, ex-falso (False.rec), and a composite `And A B → And B A`. 15 proof tests. The kernel is a Lean-grade checker of real proofs. **Reconstruction started — Eq fragment (slice 1, commit 56709ef)**: `axeyum-solver` gained a dep on the leaf `axeyum-lean-kernel`; the new `reconstruct` module translates Alethe equality terms to Lean `Expr` (`(= a b)` → `Eq.{1} α a b`) and the **`eq_reflexive`/`eq_symmetric`/`eq_transitive`** Alethe rules into `Eq.rec` proof terms the **kernel type-checks** (`def_eq` against the translated conclusion — the kernel is the checker; a wrong term is rejected). End-to-end transitivity chain reconstructs + kernel-checks; 2 negative soundness tests (wrong conclusion rejected). 11 tests. **End-to-end EUF refutation reconstructed (slice 2, commit 7267b2d):** `reconstruct_qf_uf_proof` walks a REAL `prove_qf_uf_unsat_alethe` proof — `assume` (eq → `h:Eq`, diseq → `h:Not(Eq)`), `eq_transitive`/`eq_symmetric` (n-ary fold + reversed-edge flip), `eq_congruent` (unary, congrArg via `Eq.rec`), and the closing resolution to the empty clause → `h_ne h_eq : False` — into a Lean term the **kernel checks to `False`**. 7 end-to-end instances (transitivity `a=b∧b=c∧a≠c`, longer chain, reversed edge, depth-1 congruence `f(a)≠f(b)`) + 2 negative tests. 17 tests. **Propositional resolution reconstructed (slice 3, commit fc23d4c):** the clausal layer — atom → opaque `Prop`, `(cl l…)` → right-nested `Or`, `(cl)` → `False`; `reconstruct_resolution_proof` builds the resolvent via iterated `Or.rec` (constructive case-split; `em` declared for the classical commitment but unconsumed), pivot-scheduled for the emitter's arbitrary-order RUP hints. **A REAL emitted clausal proof reconstructs end-to-end** (UNSAT CNF → `solve_with_drat_proof` → LRAT → Alethe → kernel-checked `False`). 26 tests. **Both the EUF and the clausal-resolution fragments now close to kernel-checked `False`.** **Tseitin CNF-intro rules reconstructed (slice 4, commit 237d13b):** `reconstruct_cnf_intro_rule` builds all 12 gate-definitional tautologies (`and_pos/neg`, `or_pos/neg`, `equiv_pos1/2`+`neg1/2`, `xor_pos1/2`+`neg1/2`; `xor a b := Not(Iff a b)`) as kernel-checked classical-tautology proofs (em + Or.rec case-split + prelude eliminators); a composite feeds a reconstructed `and_neg` clause through the slice-3 resolution to `False`. 43 reconstruct tests. **P3.7 now covers EUF + clausal resolution + the Tseitin Boolean-gate layer.** **Bitwise QF_BV bitblast reconstructed (slice 5, commit 4b356b3):** bit model — each bit a Lean Prop, variable bit → opaque `((_ @bit_of i) x)`, const → `True`/`False`, `bvnot/and/or/xor` pointwise (`xor` = `Not(Iff)`), `@bit_of i (@bbterm bs)` → `bs[i]`. `reconstruct_bitblast_step` kernel-checks all 7 bitwise rules (`var`/`const`/`not`/`and`/`or`/`xor`/`equal`; the bit-iffs are reflexive under the pointwise model); non-bitwise → `UnsupportedRule`. `reconstruct_qf_bv_proof` walks a REAL `prove_qf_bv_unsat_alethe` bitwise proof → **kernel-checked `False`** (1-bit bvand w/ full cong/trans/`@bbterm` plumbing + width-2 eq). 55 reconstruct tests. **HONEST soundness boundary:** the bit-level Boolean refutation + each bitblast step's bit-iffs are GENUINELY kernel-checked, but the term-level `cong`/`trans`/`equiv` bridge (`(= bvterm @bbterm)` transport) enters resolution as out-of-band-verified clause hypotheses, not yet fused into the single `False` term. **Eq-transport bridge FUSED (slice 6, commit 8c19e23):** the bitwise QF_BV reconstruction is now a CLOSED proof — `False` derived from ONLY the input assumptions + prelude + `em`, **no bridge axioms** (asserted via `declared_axiom_roles()` = `[assume,assume,em]`). Input `(= s t)` → hypothesis `h:⟦B⟧` directly; equiv1/2 → genuine `¬B∨B` tautologies (not assumed); term-level cong/trans deferred (never load-bearing); bit-iffs kernel-checked up front. 58 reconstruct tests. **The bitwise QF_BV unsat fragment reconstructs to a fully-kernel-checked, axiom-free Lean `False` proof.** Remaining for full QF_BV: arithmetic bitblast (`bvadd`/`bvmul` carries). **LRA arithmetic prelude built (commit 6869e49):** `axeyum_lean_kernel::build_arith_prelude` declares an axiomatized linear ordered field (carrier `R`, `add/mul/neg/zero/one`, `le/lt`, order+additive+scaling axioms) through the trusted gate; a **baby-Farkas refutation kernel-checks to `False`** (`le a 0 ∧ le 1 a` → `lt 1 1` → `lt_irrefl` → False). 119 kernel tests. Next: reconstruct `la_generic` — chain these axioms over a Farkas certificate (needs linear-combination/ring-normalization in the reconstructor). |

### Track 4 — Use Cases & Frontend
| Phase | Title | Status |
|---|---|---|
| P4.1 | Warm lazy arrays / symbolic memory (ADR-0030 deferred half) | TODO |
| P4.2 | Symbolic-execution CFG frontend (angr/unicorn-class) | TODO |
| P4.3 | Optimization: OMT lexicographic/Pareto + MILP hardening | WIP — single-objective `maximize/minimize_lia` + `_bv`/`_bv_signed` already shipped (exponential+binary bound search, Boolean-structured oracle). **Lexicographic multi-objective landed** (`optimize_lia_lexicographic`, 2026-06-18): optimize objectives in order, pinning each at its optimum (`obj≥v`/`obj≤v`) before the next so later ones range over the optimal face — z3's default lex combination. Sound + terminating (bounded composition of the checked single-objective optimizer); `LexOutcome::Stopped` at the first unbounded/infeasible/unknown objective. **BV lexicographic also landed** (`optimize_bv_lexicographic`, signed/unsigned, `bv_uge/ule/sge/sle` pinning) — lexicographic OMT now covers both LIA and BV. **Box** (`optimize_lia_box`, independent) **and Pareto** (`optimize_lia_pareto`, guided-improvement front enumeration, deterministic point/push caps, each point verified Pareto-optimal) modes also landed — **axeyum now has all 3 of z3's OMT modes (box, lexicographic, pareto)**. 23 OMT tests (incl. the {(1,3),(2,2),(3,1)} front). **BV box** (`optimize_bv_box`) also landed — box + lexicographic now span LIA+BV; Pareto is LIA. MaxSAT returns the witnessing model (`max_satisfiable_model`). Remaining: BV Pareto; MILP hardening |
| P4.4 | SMT-LIB command-surface completeness (declare-sort, reset, get-proof, …) | WIP — broad command surface already parsed (declare-const/fun/datatype(s), define-fun/sort, push/pop, reset(-assertions), check-sat(-assuming), get-proof/model/value/unsat-core/assignment, set-option/info, echo/exit); term forms let/forall/exists/`!`/`as` handled. **`match` datatype pattern-matching added** (commit d404794, P4.4): parse-time desugaring to nested `ite`/`DtTest`/`DtSelect`, exhaustiveness + arity checked, 11 tests. Remaining: `declare-sort` (needs first-class uninterpreted sorts the IR lacks — deep), `define-fun-rec`, full `match` for parametric datatypes |
| P4.5 | Benchmarking & the performance gate (measured Z3 head-to-head) | DONE — committed slice + baseline (32/43 decided, agree=32, DISAGREE=0) |

## Changelog

- **2026-06-19** — **P2.6: vacuous-`∀` elimination — a first sound cut into `∃∀`.**
  `∃y.∀x. x+y≥x` returned `Unknown` (after skolemizing `∃y→c`, `∀x. x+c≥x` is valid only
  when `c≥0`, so the valid-universal pass can't decide it; instantiation only refutes). New
  `quant_vacuous_universal.rs` (`eliminate_vacuous_universals`), hooked in `solve` after
  `eliminate_valid_universals`: for a top-level `∀x. body` (QF body, `x:Int`/`Real`), a Boolean
  descent (`not`/`and`/`or`/`implies`/`xor`/`ite`) reaches the atoms, and a self-contained
  affine collector (over `Rational`; handles `+`/`-`/neg/`*`-by-const + the `to_real` embed)
  declares `x` **vacuous** iff *every* arithmetic atom's net `x`-coefficient of `lhs−rhs` is 0
  **and** `x` occurs in no non-linear / UF-arg / array / BV / `div`/`mod`/`abs` position
  (any such occurrence bails). Then `∀x. body ⟺ body[x:=0]` (the bound var can't change any
  atom's truth), substituted via `replace_subterms` → the QF dispatch decides. Sound +
  conservative (any doubt ⇒ untouched). Decides `∃y.∀x. x+y≥x` → Sat, `∀x. x*0+y=y` → Sat;
  **soundness-negatives verified** — `∃y.∀x. x≤y`, `∀x. x≥0`, mixed-dependent bodies, and
  `∀x. f(x)=f(x)` (UF arg) are NOT wrongly Sat (the last still decides via the valid-universal
  pass). New `tests/quant_vacuous.rs` (8, incl. 4 soundness-negatives); full suite + clippy +
  fmt green (OS-timeout guarded). Strictly additive. A first slice of the `∃∀` keystone (full
  `∃∀` still needs LIA/LRA quantifier elimination); sub-agent + soundness review.

- **2026-06-19** — **P3.3: QF_LIA `unsat` now carries a checkable certificate in
  `produce_evidence` (gap E).** A pure-integer `unsat` (`x>0 ∧ x<0`) reached the `Other`
  evidence route and ended as a bare `Evidence::Unsat(None)` (`is_certified()==false`), even
  though `prove_lia_unsat_alethe` emits a checkable `lia_generic` Alethe proof (used on the
  SMT-LIB get-proof path). Fix: new `Evidence::UnsatArithAletheProof(Vec<AletheCommand>)`
  variant whose `Evidence::check` re-validates via the **arithmetic-aware**
  `check_alethe_lra` (= `axeyum_cnf::check_alethe_with` + the `la_generic` callback, which
  re-derives the integer/linear Farkas refutation — plain `check_alethe` can't decide
  `lia_generic`). A new `arith_alethe_certificate` helper tries `prove_lia_unsat_alethe` then
  `prove_lra_unsat_alethe` (each self-validating) in `produce_evidence`'s `Other`/`Unsat` arm,
  **after** `zero_trust_alethe_certificate` and **before** the bare/DRAT fallback (the arith
  emitters return `None` for UF/array/datatype, so ordering is safe). `trusted_steps =
  [(Farkas, certified)]` (the reduction is re-derived, not a trust hole). **Tamper test**
  (`tampered_lia_arith_evidence_fails_its_own_check`: drop the closing step → `check` rejects)
  proves the verification is real. Now certifies `x>0 ∧ x<0` and `x+y≥3 ∧ x≤1 ∧ y≤1`; QF_BV /
  QF_UFBV evidence paths unchanged (asserted). Strictly additive (only bare LIA `unsat` →
  certified). New `tests/evidence_lia_cert.rs` (5); full suite (977) + clippy + fmt green.
  From the 4th capability-gap pass; sub-agent + soundness review.

- **2026-06-19** — **P4.3 OMT robustness + completeness: optimizer honors timeout, decides
  div/mod, never errors (gaps A/B/D).** The optimizer's feasibility probes called
  `check_with_lia_dpll` directly and no path threaded `config.timeout`. Three fixes in
  `optimize.rs`: (B, completeness) reroute the LIA bound-search + Pareto probes
  (`decide_with_objective`, `pareto_probe`) through the full `check_auto` dispatcher, so
  objectives/constraints with `mod`/`div`-by-constant now optimize (`x∈[0,10] ∧ x mod 2=0`,
  max x → **10**; `x/3≤5`, max x → 17 — were hard `Err`); (D, hard rule "unknown is never an
  error") `probe_unsupported_to_unknown` maps a fragment-`Unsupported` (objective over a
  UF/`bv2nat`/nonlinear term) to a graceful `OptOutcome::Unknown` / `LexOutcome::Stopped{Unknown}`
  / `ParetoOutcome::Unknown` instead of propagating the error (min `x*x` → Optimal(0) via NRA;
  max `f(x)` → Unknown, no Err); (A, resource-limit promise) new `*_with_config` variants
  (`maximize_lia_with_config`, …, `optimize_lia_pareto_with_config`) thread a wall-clock
  deadline (Instant + `past_deadline`, wasm-shimmed) into the bound-doubling/binary-search and
  the Pareto/box/lex point loops, returning best-so-far as `Truncated`/`Unknown` on expiry
  (a 101-point Pareto front with a 2 s budget now returns in ~2 s, was minutes); the original
  no-config functions delegate with `SolverConfig::default()`, so all ~54 existing call sites
  and optima are unchanged. New `tests/optimize_robustness.rs` (6); 24 existing optimize tests
  + full suite + clippy + fmt green. From the 4th capability-gap pass (solver surfaces); sub-agent.

- **2026-06-19** — **ROBUSTNESS: integer-NIA solve HANG fixed (regression from the width
  ladder).** `a*b ≠ b*a` (ground integer nonlinear, UNSAT by commutativity) **livelocked**,
  ignoring `config.timeout` — a "never hang" contract violation caught by the 3rd capability
  pass. Root cause: pure-Int nonlinear never reaches the deadline-honoring `check_with_nra`
  (gated on `has_real`), so it fell to `dispatch_int_blast_width_ladder`, which ran ~31
  bit-blast+SAT solves over a hard multiplier-equivalence **with no timeout check between
  widths**; the real relaxation ran only after and abstracted `a*b`/`b*a` as distinct vars.
  Three fixes in `auto.rs`/`int_real_relax.rs`: (1) **deadline** — the ladder now threads
  `config.timeout` (Instant + `past_deadline`, wasm-shimmed) and bails to `Unknown(ResourceLimit)`
  before each width; (2) **trimmed ladder** — dense `4..=16` (where small witnesses live) +
  a sparse coarse tail to `DEFAULT_INT_WIDTH=32` (dropped the 36/40 tail + thinned 17..=31),
  so the no-timeout case is fast and `nia_ground_consistency` (x*x=4/9/25) still passes; (3)
  **commutative canonicalization + reorder** — `int_real_relax` sorts `mul`/`add` operands so
  `a*b` and `b*a` translate to the SAME real term (sound — real `*`/`+` commute), and the
  relaxation now runs **before** the ladder (it only ever returns `Unsat`, so reordering is
  sound and SAT cases like `x*x=4` still reach the ladder). Result: `a*b≠b*a` → **Unsat fast**
  (was a >100s hang), `∀x. x*k=k*x` → Sat, timeout honored. New `tests/nia_commutativity.rs`
  (4, incl. a 500ms-timeout-returns check); fmt + clippy + full suite green under an OS-timeout
  guard. Sub-agent + careful soundness/termination review.

- **2026-06-19** — **P2.5: integer nonlinear UNSAT via real relaxation (gap G3).**
  Sign-based integer-NIA goals (`x*x<0`, `x*x+1≤0` over Int) returned `Unknown`, and
  consequently `∀x:Int. x*x≥0` stayed `Unknown` (the valid-universal pass's `c*c<0` witness is
  integer-NIA). Fix: new `int_real_relax.rs` (`refute_int_via_real_relaxation`) + a fallback at
  the tail of the `has_int` dispatch branch, *after* the exact LIA refuters and the int-blast
  width ladder, fired only when the ladder is `Unknown`. On an isolated arena clone it builds
  the **faithful real reinterpretation** of the query — each `Int` var→a fresh memoized `Real`
  var (same int symbol ⇒ same real var), `int_const`→`real_const`, `IntAdd/Sub/Mul/Neg/Lt/Le/
  Gt/Ge`→the `Real*` counterparts, Bool/`Ite`/`Eq` rebuilt — and runs `check_with_nra`. Since
  integer solutions ⊆ real solutions, **real-`Unsat` ⇒ integer-`Unsat`** (sound); it returns
  *only* `Unsat` (a real model need not be integral), so strictly additive. **Conservative
  allow-list:** any `div`/`mod`/`abs`/coercion/`bv2nat`/BV/array/UF/datatype/quantifier subterm
  aborts the whole relaxation (→ unchanged) — never a guessed translation. One bounded NRA call,
  clone-scoped (no leakage/OOM). Decides `x*x<0`/`x*x+1≤0` → Unsat and **`∀x:Int. x*x≥0` → Sat**
  (the valid-universal sub-check now refutes `c*c<0`); `x*x==2` stays `Unknown` (real-sat √2, no
  wrong unsat), `x*x==4 ∧ x>0` stays `Sat` (width ladder). New `tests/nia_real_relaxation.rs`
  (5); fmt + clippy + full suite green. Final tractable gap from the 2nd capability-gap pass;
  sub-agent + soundness review.

- **2026-06-19** — **P2.4: `bv2nat` out-of-range now refuted UNSAT (gap G2).** `bv2nat(b)` of
  a W-bit `b` is provably in `[0, 2^W-1]`, but `bv2nat(4-bit) >= 16` / `== 20` returned
  `Unknown`: the exact LIA refuters reject a raw `Op::Bv2Nat` (`lra.rs` `Collector::linearize`
  catch-all), so the query fell to the bounded int-blast which returns `Unknown` (never
  `Unsat`) for an in-range integer no-model. Fix: new `bv2nat_bound.rs`
  (`abstract_bv2nat_for_refutation`) + a `refute_bv2nat_out_of_range` hook at the top of the
  `has_int` dispatch branch. On an **isolated arena clone**, each distinct `bv2nat(b)` term is
  replaced by a fresh Int var `n` with the true bound `0 ≤ n ≤ 2^W-1` (hash-consing ⇒ the same
  `bv2nat(b)` ⇒ one var; distinct `b` ⇒ independent), and the exact refuters
  (Diophantine/simplex/DPLL) decide the **relaxation** — `unsat` of the relaxation transfers
  (sound). Returns `Unsat` only on a refutation; otherwise falls through to the original (SAT
  decided by the native int-blast `Bv2Nat` handling, `bv2nat` intact). Width guard
  `MAX_BOUND_WIDTH=62` keeps `2^W-1` exact in `i128` (wider ⇒ unabstracted, graceful). No
  leakage/OOM (clone-scoped). Decides `bv2nat(4-bit)≥16`/`==20`/same-`b` `==5 ∧ ==6` → Unsat;
  preserves `≥8` → Sat and distinct-vector `==5 ∧ ==6` → Sat. New `tests/bv2nat_bound.rs` (6);
  fmt + clippy + full suite green. From the 2nd capability-gap pass; sub-agent + soundness review.

- **2026-06-19** — **P1.6: EUF over the reals (QF_UFLRA) — hard `Err` fixed, now routed
  through the combination (gap G1).** A real-sorted UF application `f(x):Real` returned
  `Err Unsupported("QF_LRA: non-linear or non-real subterm …")` — the pure-real linearizer
  rejects the `Apply` and the dispatch's `has_real` branch *unconditionally returned*
  `check_with_nra`, so it never reached the function handling. The **integer** branch already
  catches `Unsupported` and falls through to `check_with_uf_arithmetic` (that asymmetry is why
  QF_UFLIA worked but QF_UFLRA didn't). Fix (`check_auto_dispatch`): when a function is present,
  the `has_real` branch now falls through on `Unsupported` to the EUF + linear-arithmetic
  combination (`check_with_uf_arithmetic` decides QF_UFLRA the same way as QF_UFLIA). A second
  fix: a Real arith-UF query whose combination result is `Unknown` (the QF_UFLRA *sat-model
  projection* for an arithmetic-sorted UF is not yet built) now **returns that `Unknown`**
  instead of falling through to the eager bit-blast fallback, which errors on `Real` (an Int
  arith-UF can still fall through to int-blast). Upholds "`unknown` is never an error" and
  unlocks EUF+LRA. Now: `f(x)=1 ∧ f(y)=2 ∧ x=y` → **Unsat** (congruence), the Nelson-Oppen
  squeeze `f(a)≤b ∧ b≤f(a) ∧ a=c ∧ f(c)≠b` → **Unsat**, and `f(x)=1.0` → graceful **Unknown**
  (was a hard `Err`; sat-model projection for an arithmetic UF is the remaining follow-up).
  Surgical (only the function-present Real case changes). New `tests/euf_real.rs` (3); fmt +
  clippy + full suite green. From the 2nd capability-gap pass (highest-value finding).

- **2026-06-19** — **P2.6: valid-universal elimination handles NESTED `∀` prefixes (gap G4).**
  `eliminate_valid_universals` previously bailed when a `∀x. body` had a quantifier in its
  body, so `∀x.∀y. x+y==y+x` (valid) stayed `Unknown`. `try_eliminate` now **peels the entire
  leading `∀` prefix** (`∀x.∀y.…` ⇒ vars `[x,y]`, innermost body), substitutes *all* bound
  vars with fresh `!vu_*` constants at once, and checks the negated innermost (QF) body unsat
  — sound by the same closure argument (`∀x.∀y. b` valid iff `¬b[x:=cx,y:=cy]` unsat). Now
  decides `∀x.∀y. x+y==y+x` and `∀x.∀y. x=y ⇒ f(x)=f(y)` (Sat); a non-valid nested universal
  (`∀x.∀y. x=y`) is not mis-proven valid (verified — never wrongly Sat). 3 new tests; fmt +
  clippy + full suite green. (Remaining from the 2nd gap pass: G1 EUF-over-Real hard `Err`,
  G2 `bv2nat` width bound, G3 nonlinear-body validity, G5 `∃∀` skolem-then-validity.)

- **2026-06-19** — **P2.6: sat-side universal-validity elimination — valid `∀` now decided
  (were `Unknown`).** A standalone `∀x. body` with a quantifier-free body is **valid** (hence
  the assertion is satisfiable — true in every model) **iff** `¬body[x:=c]` is UNSAT for a
  fresh constant `c`. New `quant_valid_universal.rs` (`eliminate_valid_universals`), hooked in
  `solve` before `check_with_quantifiers`: for each top-level `∀x. body` (QF body; nested
  quantifiers skipped), mint a fresh `!vu_*` constant of `x`'s sort, substitute via
  `replace_subterms`, and decide `¬body[x:=c]` with the **quantifier-free** `check_auto`
  (no re-entry → terminates in one bounded QF solve). `Unsat` ⇒ the universal is valid ⇒
  replace with `true` (exact); `Sat`/`Unknown` ⇒ leave it for the existing instantiation/MBQI
  path. Sound + strictly additive (only `Unknown`→decided; a proven-valid universal is `true`
  everywhere, an unprovable one is never dropped). Leverages the existing exact deciders:
  `c+0≠c`/`c·0≠0` (LIA), `f(c)≠f(c)` (EUF), `c·c<0` (NRA sign rule). Now decides
  `∀x:Int. x+0=x`, `x·0=0`, `x≥0 ∨ x<0`, `∀x. f(x)=f(x)`, `∀x:Real. x²≥0`. UNSAT-by-
  instantiation (`∀x. f(x)=0 ∧ f(a)=1`) and non-valid universals unaffected (verified). New
  `tests/quant_valid_universal.rs` (8); one guarded-int test relaxed (its formula is validly
  `Sat` now — a sound improvement). fmt + clippy + full suite green. Capability-gap pass;
  sub-agent + independent soundness review (the alarming compile diagnostics were a stale
  analyzer cache — the code builds and the suite is green).

- **2026-06-19** — **QF_NIA: ground-vs-`∃` inconsistency fixed (small nonlinear-int SAT
  now decided).** `x*x==4 ∧ x>0` (ground) returned `Unknown` ("overflowed at width 32") while
  the equivalent `∃x. x*x==4` returned `Sat` (skolemize → bounded blast finds x=2) — same
  satisfiability, two answers. Root cause: the integer bit-blast fallback used a single fixed
  width (`DEFAULT_INT_WIDTH=32`), and at width 32 the SAT solver may pick a *wrapping* witness
  (`x` with `x*x ≡ 4 mod 2^32` but `x*x ≠ 4`) that fails the exact-integer replay → `Unknown`.
  Fix (`auto.rs::dispatch_int_blast_width_ladder`): for a pure-integer fallback query, iterate
  the blast width small→large (4..=32, then 36, 40 — a deterministic, finite ladder that
  still includes the old width 32) on an arena clone per width, returning the **first
  replay-checked `Sat`**. **Sound by construction:** `check_with_all_theories` returns `Sat`
  only after replaying the model against the originals, and returns `Unknown` (never `Unsat`)
  for an integer query with no model within a width (`combined.rs:88`), so the ladder never
  produces a wrong `unsat` and a too-narrow width simply climbs. Strictly additive (only
  `Unknown`→`Sat`); `x*x==2` (no integer root) stays soundly `Unknown` (out of scope —
  needs genuine NIA unsat reasoning). New `tests/nia_ground_consistency.rs` (6, replay-verified).
  **Follow-up:** the ladder runs up to ~31 solves for an integer query that is `Unknown` at
  every width — bounded and OOM-safe (one arena clone at a time, width cap 40) but worth a
  smarter width schedule / shared budget later. Driven by the capability-gap pass; sub-agent +
  independent soundness review.

- **2026-06-19** — **P2.6: guarded-finite Int universals now decided (were `Unknown`).**
  A universal `∀x:Int. (lo≤x≤hi) ⇒ body` is logically *equivalent* to the finite conjunction
  `⋀_{v=lo}^{hi} body[x:=v]` (outside `[lo,hi]` the implication is vacuously true), so it is an
  exact, sound rewrite — both sat and unsat transfer. New `quant_guarded_int.rs`
  (`expand_guarded_int_universals`), hooked into `check_with_quantifiers` as a pre-pass before
  `axeyum_rewrite::expand_quantifiers` (which rejects Int domains): detects `∀x:Int.(⇒ guard
  inner)` where `guard` is a conjunction of a lower- and upper-bound atom isolating the bare
  bound var against **literal** Int constants (all `≤`/`≥` orientations), substitutes each `v∈
  [lo,hi]` via `replace_subterms`, and decides the resulting QF conjunction. A deterministic
  `RANGE_SIZE_CAP = 4096` (checked arithmetic) means an inverted/unbounded/huge range never
  expands → graceful `Unknown` (never OOM); nested quantifiers / non-literal bounds / escaping
  var → passthrough. Sat replay anchors on the equivalence-preserving `guard_expanded` (the
  ground evaluator can't evaluate a raw Int `∀`). Strictly additive (only `Unknown`→decided).
  Decides `∀x.1≤x≤3⇒x²≤9` (Sat), `∀x.1≤x≤3⇒x≤2` (Unsat), `≥`-oriented, one-point range, and
  over-cap → Unknown. New `tests/quant_guarded_int.rs` (5); full solver suite + clippy + fmt
  green. Driven by the capability-gap pass; done via a focused sub-agent.

- **2026-06-19** — **P2.9/P1.6: datatypes with Int/Real fields now decided (were a hard
  `Err`).** The native datatype solver (`datatype_native.rs`) rejected any datatype carrying
  an `Int`/`Real` field with `SolverError::Unsupported` — blocking `List Int`, `Tree Int`,
  records with numeric fields, and the whole numeric-payload datatype space, even for pure
  congruence with no arithmetic. Fix: `register_datatype` admits `Int`/`Real` field sorts;
  `build_sym_vars` already declares a field var of the field's own sort with the
  well-founded-default guard (`well_founded_default` returns `Int(0)`/`Real(0)`);
  `value_to_term` renders `Int`/`Real` defaults. The datatype-free residual (tags as BV,
  field vars as Int/Real + the original arithmetic) re-dispatches through the existing
  `solve → check_auto` path, which routes Int/Real to the LIA/LRA deciders and BV to
  bit-blasting — no new wiring. Sound: `unsat` equisatisfiable, `sat` projects to
  `Value::Datatype` and **replays** (a projection bug ⇒ replay failure → Unknown, never a
  wrong sat). Now decides: `v(x)=1 ∧ v(y)=2 ∧ x=y` (UNSAT, congruence), `is-cons(l) ∧
  head(l)=5` (SAT), `v(x)+1=4` (SAT), recursive `List Int`, multi-ctor `Either Int`. New
  `tests/datatype_int_fields.rs` (5); existing datatype tests + full solver suite (926) +
  clippy + fmt green. Driven by a measured capability-gap pass; done via a focused sub-agent.
  Closes the P0 finding from that pass (also upholds "unknown is first-class, never an error"
  — the hard `Err` is gone).

- **2026-06-19** — **P3.5: Ackermann cert widened to congruence-closure arg-equalities
  (e-graph fallback).** `prove_qf_ufbv_unsat_alethe` now discharges an argument pair equal
  by **congruence** (not just transitive closure of asserted edges) — e.g.
  `f(g(a))=k ∧ a=b ∧ f(g(b))≠k`, where the args `g(a)`, `g(b)` are equal because `a=b`.
  A new `CongBridge` builds an `axeyum_egraph::EGraph` over the rewritten assertions + the
  abstraction defining equations `v_i=f(args_i)` (all nodes added before any merge, so
  congruence edges survive); when the asserted-edge BFS declines, `emit_arg_units` walks
  `EGraph::explain_steps` and converts `Input`→assume / `Congruence`→`eq_congruent`
  (recursing on args) threaded through `eq_transitive` — exactly the `prove_qf_uf_unsat_alethe`
  pattern. **Strictly additive**: the identical / direct-assert / transitive-BFS paths are
  byte-unchanged, and the whole emitter is self-validated by `check_alethe` (a bad fallback
  ⇒ `None`, never a wrong proof). Carcara accepts the nested-congruence proof
  (`ufbv_nested_congruence_is_accepted_by_carcara`; the EUF `eq_symmetric`+resolution flip
  was swapped for the `symm` rule which both `check_alethe` and Carcara accept). Done via a
  focused sub-agent; independently re-validated (clippy clean, qfufbv_proof 7, carcara 54,
  full solver suite 920). **Lean loop now CLOSED for the congruence fragment** (follow-on):
  `reconstruct.rs` gained `symm`-rule reconstruction (`reconstruct_symm`, mirroring
  `reconstruct_eq_symmetric`'s kernel-gated `Eq.rec` transport), so
  `end_to_end_qf_ufbv_congruence_derived_to_false` reconstructs `f(g(a))=k ∧ a=b ∧ f(g(b))≠k`
  to a kernel-checked Lean `False` — the congruence fragment is now validated at all three
  levels. **Remaining follow-up:** the array-elim index fragment
  (`term_to_alethe` renders only symbols/bv-consts) would need application-valued indices to
  benefit, left untouched to protect the validated array cert.

- **2026-06-19** — **Datatype evidence routing fixed + datatype zero-trust cert wired.**
  `evidence_route` (the `produce_evidence` classifier) ignored datatype sorts/ops, so a
  datatype query whose top-level terms are all Bool/BitVec (e.g. `select_0(mk(a,b))=#b00
  ∧ a≠#b00`) misrouted to `EvidenceRoute::QfBv` → `produce_qf_bv_evidence` → raw `DtSelect`
  to the BV backend → `Unsupported` error. Fixed: detect `Sort::Datatype` +
  `DtConstruct`/`DtSelect`/`DtTest` in `evidence_route` so datatype queries route through
  `solve` (which has the datatype dispatch). New `tests/datatype_solve_path.rs` (UNSAT via
  solve / via produce_evidence / SAT via solve). **With routing fixed, the datatype
  read-over-construct cert (`prove_qf_dt_unsat_alethe_via_simplification`) is now also wired
  into `zero_trust_alethe_certificate`** — so QF_DT unsat carries a zero-trust-hole Alethe
  proof too (projection folded by `eq_transitive`/ι-reduction). Found while wiring the
  evidence certs; fixed via a focused sub-agent. Full solver suite (917 tests) + clippy green.

- **2026-06-19** — **P3.5: zero-trust-hole Alethe certs WIRED into the evidence path.**
  `produce_evidence`'s `unsat` branch previously tried only the array
  read-over-write-same direct cert, then fell back to a *trusted* DRAT reduction
  certificate (recording `TrustId::Ackermann` / `ArrayElim` as trust holes). It now
  also tries the Ackermann (`prove_qf_ufbv_unsat_alethe`) and array-elimination
  (`prove_qf_abv_unsat_alethe_via_elimination`) certs via a new
  `zero_trust_alethe_certificate` helper — so a QF_UFBV / QF_ABV `unsat` in the
  covered fragment now carries a `check_alethe`-validated Alethe proof that *derives*
  the functional/read-consistency reduction by `eq_congruent` (`trusted_steps` empty —
  **no reduction trust hole**), instead of the trusted DRAT. The certs were previously
  only test-exercised; they are now actually USED on the evidence path, retiring the
  Ackermann/ArrayElim trust holes **in practice** for the covered fragment. Each emitter
  self-validates and returns `None` cheaply outside its fragment, so trying them in
  order is sound and changes nothing for other fragments. New test
  (`qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate`: `UnsatAletheProof` evidence,
  zero `trusted_steps`, self-`check`s). (Ledger stays "trust hole" — coverage is the
  derivable-equality fragment, not universal; ROW-distinct / non-derivable equalities
  still fall to trusted DRAT.)

- **2026-06-19** — **P3.5: array-elimination (read-consistency) Alethe certificate
  widened to transitive index-equalities.** Same generalization as the Ackermann cert,
  applied to `prove_qf_abv_unsat_alethe_via_elimination`: a read-consistency constraint
  `i=j ⇒ select(a,i)=select(a,j)` is now discharged when the index equality `i=j` holds
  by **transitive closure** of asserted equalities (`i=k ∧ k=j`), via an `eq_transitive`
  chain over the `!sel_a` unary select function — previously only direct index equalities
  were certified. Strictly additive (direct/identical indices unchanged), `check_alethe`
  self-validated, and externally **Carcara-validated**
  (`abv_select_consistency_transitive_is_accepted_by_carcara`). Index-unit derivation
  factored into `emit_index_equality_unit`. Widens the array-elim trust-hole certificate
  (Track 3, ADR-0010). New self-check + Carcara tests; solver clippy + qfabv_elim_proof +
  carcara crosscheck green (53 carcara tests). **Lean loop closed for the widened
  fragment:** the transitive Ackermann cert also reconstructs to a kernel-checked Lean
  `False` (`end_to_end_qf_ufbv_transitive_congruence_to_false`), so the transitive certs
  validate at all three levels (in-tree `check_alethe`, external Carcara, Lean kernel).
  Full solver suite green (77 results, 0 failures).

- **2026-06-19** — **P3.5: Ackermann Alethe certificate widened to transitive
  argument-equalities.** `prove_qf_ufbv_unsat_alethe` previously discharged a
  functional-consistency constraint's antecedent only when each argument pair was
  *directly* asserted equal (or identical). It now also discharges pairs equal by
  **transitive closure** of the asserted equalities (`a=b ∧ b=c ⊢ a=c`): a BFS over
  the asserted-equality graph finds the chain, each edge (an original assertion) is
  `assume`d, and one `eq_transitive` step + resolution derives the argument equality
  feeding `eq_congruent` — so `f(a)=k ∧ a=b ∧ b=c ∧ f(c)≠k` now emits a checkable
  certificate (previously declined → `None`). Strictly additive: directly-asserted
  and identical pairs keep their exact prior steps (no change to the existing
  Carcara-validated certs), and the new path is gated by `check_alethe`
  self-validation (a non-derivable chain ⇒ `None`, never a wrong proof). 2 new
  self-check tests (unary chain; binary with one direct + one chained arg) + a new
  **Carcara crosscheck** (`ufbv_transitive_congruence_is_accepted_by_carcara`) so the
  transitive fragment is externally validated. Widens the Ackermann trust-hole
  certificate coverage (Track 3, ADR-0013). Full solver clippy + qfufbv_proof +
  carcara crosscheck green.

- **2026-06-19** — **NRA OOM gap CLOSED: deterministic cross-product admission bound
  (graceful `unknown`, never OOM).** `check_with_nra` now refuses any query with > 2
  distinct-operand cross-products (`a·b`, `a ≠ b`) up front — *before* building lemmas or
  solving — returning `Unknown(ResourceLimit)`. Root cause (measured under the new 64 GiB
  `ulimit` cap): the 3-variable case `a²+b²+c² ⋈ ab+bc+ca` (three cross-products) blows up
  the DPLL(T)/exact-rational LRA relaxation *inside a single solve call* — so the per-round
  and per-node wall-clock checks never get a turn — and **bounds do not tame it** (the
  bounded variant `SIGABRT`ed at the memory cap; McCormick just adds more lemmas). The bound
  counts **only** cross-products: squares are cheap (no monotonicity/SOS lemmas) so
  square-only multi-variable instances (`x²+y²+z²+1=0`) and the 2-var SOS frontier
  (`a²+b²<2ab`, one cross) stay decidable — verified, no regression. 3 new tests (unbounded
  + bounded both degrade; square-only not gated); all 27 NRA + 5 Spivak tests green. Updates
  the standing `Graceful unknown` rule; multi-variable SOS / Cauchy–Schwarz is now explicitly
  gated on a future nlsat/CAD (or exact-rational work-budget) engine. Also landed
  `scripts/mem-run.sh` + `just test-guarded` (64 GiB `ulimit -v` wrapper) so build/test/bench
  can never OOM the host, and fixed a pre-existing `clippy::many_single_char_names` lint in
  the `theory_combination` test module (the P1.6 commits had left `clippy --all-targets` red).

- **2026-06-18** — **Crash-hardening sweep: never panic on arithmetic-sorted UF sat-model
  projection.** `Value::scalar_code` panics on Int/Real; all three solver callers of
  `project_model` (euf / combined / aufbv) now degrade to a sound `Unknown` for an
  arithmetic-sorted uninterpreted function instead of crashing. Found via `solve` on a
  quantified UF+LIA query (now decides UNSAT, was a panic). Upholds 'graceful unknown,
  never crash'. Full solver suite green (77 binaries).

- **2026-06-18** — **QF_UFLIA / QF_UFLRA complete (conjunctive UNSAT) via eager EUF+arith
  combination.** `check_with_uf_arithmetic` switched to eager Ackermann elimination →
  `check_auto`: all congruence constraints asserted up front, so nested `f(g(a))≠f(g(b))∧a=b`,
  `f(x+0)≠f(x)`, result-in-arithmetic `f(p)+1=f(q)∧p=q`, and the squeeze all decide UNSAT
  (the lazy CEGAR was incomplete — arithmetic solvers leave intermediate abstraction vars
  unconstrained). Also hardened the default-on preprocessing to be fully best-effort (any
  reduction/dispatch/reconstruction error → solve the original). 7 UF-arith tests; ledger +
  golden matrix updated; full solver suite green (77 binaries).

- **2026-06-18** — **P1.6: EUF + linear-arithmetic combination (QF_UFLIA / QF_UFLRA).**
  Widened `declare_fun` to admit Int/Real UF sorts; refactored the functional-consistency
  CEGAR (`check_with_function_consistency`) and added `check_with_uf_arithmetic` (solves the
  Ackermann abstraction with the arithmetic dispatcher, not bit-blasting) — the classic
  Nelson–Oppen case `f(a)≠f(b) ∧ a≤b ∧ b≤a` now decides **UNSAT** (LIA forces a=b →
  congruence forces f(a)=f(b)), in both LIA and LRA. Wired into `check_auto`. New theory
  coverage axeyum could not even *declare* before. Full solver suite green (77 binaries).

- **2026-06-18** — **P1.6 T1.6.2 th_eq bus** — `EGraph::theory_var_classes` (e-graph
  readout of classes carrying theory vars) + `interface_th_eqs` (solver-side: emit
  cross-theory interface equalities, spanning chains over classes spanning ≥2 theories).
  The bus a merge in one theory uses to propagate an equality to another. With the four
  combination primitives, P1.6's machinery (shared / propose / classify / arrangement /
  th_eq-bus) is in place; the remaining slice is the online multi-theory loop that drives it.

- **2026-06-18** — **P1.6 combination — arrangement-consistency check**
  (`combination_conflict`): one model-based-combination iteration — does a BV model's
  equal/distinct arrangement of the shared terms agree with the EUF congruence? Returns the
  first conflicting pair (model-distinct vs congruence-equal, or model-equal vs
  congruence-refuted), else `None`. Composes `shared_terms`+`classify` into the core
  combination step. Four P1.6 combination primitives now exist (shared / propose / classify
  / arrangement-check); the remaining slice is the online loop that blocks a conflicting
  arrangement and re-solves (P1.5 T1.5.1–4 online drive).

- **2026-06-18** — **P1.6 combination — interface-equality classification against
  congruence** (`classify_interface_equalities` + `InterfaceStatus`). Decides each
  proposed equality Entailed/Refuted/Undetermined via the e-graph congruence closure of
  the EUF assertions — Entailed covers congruence-derived equalities (`f(a)=f(b)` from
  `a=b`), Refuted uses asserted disequalities. With `shared_terms` (T1.6.1) +
  `propose_interface_equalities`, the model-based-combination core (shared → propose from
  a BV model → confirm/refute against EUF) is now in place; remaining is the online
  CDCL(T) drive that loops propose↔split↔re-solve (P1.5 T1.5.1–4).

- **2026-06-18** — **P1.6 combination — model-based interface-equality proposal**
  (`propose_interface_equalities`). Given a one-theory model, proposes equalities between
  equal-valued shared terms (spanning chain per value group, deterministic) — the
  *propose* half of Z3-style model-based combination, building on T1.6.1's `shared_terms`.
  Next: assert/confirm-or-split the proposed equalities against the congruence closure
  (T1.6.3), which needs the online CDCL(T) drive (P1.5 T1.5.1–4 — a substantial slice).

- **2026-06-18** — **P1.6 theory combination — T1.6.1 shared-term discovery**
  (`theory_combination::shared_terms`, the plan's named next task). Identifies the
  bit-vector-sorted Nelson–Oppen interface terms between the EUF and BV theories
  (arg/result of `Op::Apply` ∩ operand/result of an interpreted BV op) — pure,
  deterministic structural discovery, the foundation for T1.6.2 (`th_eq` bus) and T1.6.3
  (interface-equality case-splitting). 4 tests.

- **2026-06-18** — **Foundational QF_BV refutation checked by the real Lean kernel**
  (destination-3). Added a gated real-lean cross-check for the bit-blasting → resolution
  path (`a≤b ∧ b<a`); `#print axioms` shows no `sorryAx`. Independent-kernel validation now
  spans **7 fragments**: QF_BV / QF_UFBV / QF_ABV / datatypes / LRA / ∀ / ∃ — the core
  bit-level path plus the theory fragments.

- **2026-06-18** — **Datatype refutations checked by the real Lean kernel** (destination-3).
  Added a gated real-lean cross-check for algebraic datatypes (read-over-construct unsat,
  via datatype simplification → QF_UFBV); `#print axioms` shows no `sorryAx`. Real-kernel
  validation now spans **6 fragments**: QF_UFBV / LRA / ∀ / ∃ / QF_ABV / datatypes.

- **2026-06-18** — **QF_ABV refutations now checked by the real Lean kernel** (destination-3).
  Added a gated real-lean cross-check for arrays (read-consistency unsat, reconstructed via
  array elimination → QF_UFBV); `#print axioms` shows no `sorryAx`. The independent-kernel
  validation now spans QF_UFBV / LRA / ∀ / ∃ / **QF_ABV**. (Pure-QF_BV-value and direct ROW
  reconstruction to Lean remain frontier gaps — the Lean emitter is narrower than the Alethe one.)

- **2026-06-18** — **Bounded strings: `str.to_code` / `str.from_code`** (SMT-LIB 2.6
  char-code ops) added to the byte-string theory. `to_code` → (is_single, byte-as-BV8);
  `from_code` → the length-1 string for a byte. Bounded BV formulas; tested incl.
  round-trip. Narrows the string-theory gap vs z3 within the bounded fragment.

- **2026-06-18** — **FP `to_real` confirmed format-general** (F16/BF16/TF32/FP8 E5M2,
  not just F32/F64): corrected the stale doc and added small-format coverage (incl.
  subnormals and ∞/NaN→None). With `from_real` (all modes) and the int/bv→fp conversions,
  the FP↔Real/Int conversion surface is complete across the supported IEEE formats.

- **2026-06-18** — **FP `from_real`: all five rounding modes** (RNE/RNA/RTZ/RTP/RTN).
  `round_rational_rne` gained per-mode rounding (`round_up_decision`) and overflow
  (`overflow_bits`, ±inf vs max-finite, direction-aware). Validated against
  `rustc_apfloat`'s correctly-rounded division for every mode and sign — an independent
  IEEE oracle. `to_fp` from real is now complete for all SMT-LIB rounding modes.

- **2026-06-18** — **FP `from_real` now rounds non-dyadic rationals** (exact-integer RNE,
  `round_rational_rne`): 1/3, 1/10, 22/7 → correctly-rounded F32/F64, no f64
  double-rounding. `round_rational_to_format` kept dyadic-only (smtlib parser depends on
  its contract); `from_real` falls back to the integer path. Cross-checked vs the f64
  path on dyadic (incl. F16 subnormal/tie) and vs native casts on non-dyadic. The `to_fp`
  source set (int→fp, bv→fp, real→fp) is complete for NearestEven.

- **2026-06-18** — **FP `from_real`** (`axeyum_fp::from_real`): `to_fp` from a rational
  constant. Dyadic rationals (power-of-two denominator, <2^53 numerator) round soundly via
  the validated `round_rational_to_format` (exact f64 → `round_to_format`); non-dyadic
  (1/3, 1/10) return `Ok(None)` (decline — exact rational rounding needs >i128, a planned
  follow-up). Completes the `to_fp` source set for the dyadic case (int→fp, bv→fp, real→fp).

- **2026-06-18** — **Optimization/constraint API feature-complete + full Solver façade.**
  Session run (all green, committed): FP integer→float (`from_ubv`/`from_sbv`); all 3 z3
  OMT modes (box, lexicographic, Pareto) across **LIA + BV**; model-returning MaxSAT;
  strict PB (`pb_lt`/`pb_gt`); cardinality `between`/`at_most_one`/`exactly_one`; BV
  `repeat`; and `Solver` façade methods for the whole optimization/MaxSAT/unsat-core
  surface. `preprocess` flipped default-on (guarded, validated). **Next frontiers** (all
  larger / coordination-gated): deeper word-level reduction (other agent's `axeyum-rewrite`
  lane); a kissat-class SAT core (long game, the search-bound Timeout band); unbounded
  strings / uninterpreted sorts / full MBQI / NRA-CAD; and `to_fp`-from-real (needs exact
  rational rounding — f64 bridge is unsound for sub-f64 formats).

- **2026-06-18** — **Solver façade `unsat_core`**: `Solver::unsat_core(arena)` returns a
  deletion-minimized unsat core (assertion indices) — the z3 get-unsat-core API on the
  high-level façade. Test verifies the irrelevant assertion is excluded.

- **2026-06-18** — **Word-level preprocessing flipped default-ON** (commit `6cb2f1b`,
  ADR-0034/0037 staged step). `SolverConfig::default().preprocess == true`; the default
  `solve()`/`check_auto` path runs the model-sound reduction pipeline. Guarded so it is
  never a correctness dependency: skipped on quantified queries (QF transform), and
  best-effort (any reduction-pass error → solve the ORIGINAL). Validated by a
  full-workspace behaviour check (103 test binaries green) — the gate ADR-0037 required.
  Caught + fixed a real regression in the check: preprocessing errored on
  uninterpreted-function applications (canonicalize fold) → the best-effort fallback.

- **2026-06-18** — **BV `repeat`** (`bv_repeat`, z3 `(_ repeat n)`): derived concat fold,
  no new IR Op/lowering. Completes the common z3 BV op set (nand/nor/xnor/comp/rotate
  already present). Test incl. exhaustive BV4 symbolic duplication.

- **2026-06-18** — **BV Pareto** (`optimize_bv_pareto`): completes the OMT trio across
  both theories — box, lexicographic, and Pareto now all span LIA + BV. Test: BV8 front
  {(1,3),(2,2),(3,1)}. 24 OMT tests.

- **2026-06-18** — **Cardinality convenience**: `between(lo,hi)`, `at_most_one`,
  `exactly_one` (one-hot) — compose the existing at-most/at-least/exactly forms. 2 tests.

- **2026-06-18** — **Solver façade OMT/MaxSAT methods**: `Solver::{maximize_lia,
  minimize_lia, optimize_lexicographic, optimize_pareto, max_satisfiable}` optimize over
  the active assertions — the optimization work is now reachable via the high-level API.

- **2026-06-18** — **PB strict comparisons** (`pb_lt`/`pb_gt`, pseudo-Boolean `<`/`>`):
  compose the non-strict forms (≤k-1 / ≥k+1, with sound k-edge handling). 2 tests.

- **2026-06-18** — **MaxSAT model-returning variant** (`max_satisfiable_model` /
  `_weighted_model`, commit `daced10`). Returns `MaxSatOutcome::Optimal { weight, model,
  satisfied }` — the witnessing assignment + which soft constraints hold, the actual
  solution z3's MaxSAT yields (previously only the optimal weight). Sound: pins the
  weight-sum at the optimum, witnesses a model via `check_auto`, re-evaluates each soft
  constraint; surprise unsat/unknown folds to `Unknown`. Test cross-checks `satisfied`
  flags against the model. Working-agreement loop increment 7.
- **2026-06-18** — **P4.3 OMT: Pareto + box modes complete the z3 OMT trio.**
  `optimize_lia_pareto` (commit `75205b7`) enumerates the Pareto front by guided
  improvement, each point *verified* Pareto-optimal (confirmed-unsat domination query),
  with deterministic point (256) / push (64) caps → `Truncated`/`Unknown` rather than
  unbounded enumeration. With `optimize_lia_box` (`ecabf53`) and the lexicographic modes
  below, **axeyum now has all three z3 OMT modes (box, lexicographic, pareto)**. 22 OMT
  tests incl. the {(1,3),(2,2),(3,1)} front. Working-agreement loop increments 4–6.
- **2026-06-18** — **P4.3 OMT breadth: lexicographic multi-objective optimization**
  (`optimize_lia_lexicographic`, commit `b852ddf`). Optimizes integer-linear objectives
  in order, pinning each at its optimum before the next (z3's default lexicographic
  combination); sound + terminating (bounded composition of the checked
  `maximize/minimize_lia`); `LexOutcome::Stopped` at the first non-finite objective.
  4 API-level tests (order-dependence, mixed max/min, stop-on-unbounded). Reachable via
  the solver API. **Extended to BV** (`optimize_bv_lexicographic`, signed/unsigned, commit
  `f57e5f3`, +2 tests) — lexicographic OMT now spans LIA and BV. Second/third breadth
  increments of the new working-agreement loop.
- **2026-06-18** — **Plan revised from measured learnings + breadth pivot.** Per a
  strategy check-in: revised PLAN.md (front #1 reframed to word-level *reduction* as
  the destination-2 lever with the EncodingBudget/search-bound/large-CNF partition;
  both-in-parallel on the SAT core; new standing rule *graceful `unknown`, never
  OOM/crash*; multi-agent coordination rule — `axeyum-rewrite`/`axeyum-smtlib` are the
  other agent's reduction lane). Active focus set to **breadth toward feature-parity**.
  First breadth increment: **FP integer→float conversion** (`from_ubv`/`from_sbv`,
  commit `f7b43db`) — see P2.8 row; differential-tested vs native `as f32`/`as f64`.
- **2026-06-18** — **Known robustness gap found (NRA can OOM on unbounded multi-product
  nonlinear queries).** Probing whether the SOS lemmas generalize to 3 variables
  (`a²+b²+c² ≥ ab+bc+ca`) revealed that `check_with_nra` on an **unbounded** 3-variable
  nonlinear query **OOMs** rather than degrading to `Unknown`. Diagnosis: unbounded vars
  can't be box-split (`widest_split` → `None`), so it never branches — the blowup is in
  the **root refinement loop**, where the ~6-product case generates a much larger boolean
  product-lemma set and/or escalating exact-rational witnesses that the existing
  wall-clock deadline + `too_large_to_refine` (2³¹) guards don't bound *as memory*. The
  2-variable SOS win is unaffected (committed, green). A correct fix needs a deterministic
  memory/work bound that does **not** regress currently-working *bounded* multi-product
  cases (those terminate via McCormick) — scoped as future work, to be developed against a
  controlled small repro (NOT the 123 GB-OOMing 3-var case). Multi-variable SOS is gated on
  this. **Do not run unbounded ≥3-variable nonlinear NRA queries without a memory bound.**
- **2026-06-18** — **P2.5 NRA breadth: sum-of-squares lemmas prove AM–GM₂**
  (commit `8a7d31f`). `nra::sos_lemmas` adds `(a±b)² ≥ 0` (= `r_aa+r_bb∓2·r_ab ≥ 0`)
  over the abstracted products of each variable pair — sound (true in every real
  model), restoring the cross-product correlation the independent product abstraction
  drops. **`a²+b² ≥ 2ab` / AM–GM₂ is now proved** (`a²+b²<2ab` → `Unsat`); the Spivak
  SOS-frontier test is promoted from prompt-`Unknown` to proved. A negative test pins
  soundness (`a²+b²=2ab` stays satisfiable, `x=y`). Closes a documented NRA frontier
  gap; higher-degree/multi-var SOS (Bernoulli, general Cauchy–Schwarz) + nlsat/CAD
  remain. Built on the incremental-eval primitive landed earlier this session.
- **2026-06-18** — **P1.8 tactics: or-else portfolio combinator** (`solve_with_portfolio`
  + `recommended_portfolio`, commit `cda1f55`). Runs strategies in order, first to
  decide wins, falls through `Unknown`/errors (Z3's `or-else`; sound — a later strategy
  runs only when earlier ones returned `Unknown`). `recommended_portfolio` routes by
  query shape (heavy-arith → `[LazyBvAbstraction, EagerPureRust]`; structural → `[Auto]`),
  composing the destination-2 levers with fallback power over a single `Auto` pick.
  Pure-Rust, collision-free, 3 tests. Full workspace suite green (103 test binaries, 0
  failures).
- **2026-06-18** — **Destination-2 lever found & measured: word-level preprocessing
  doubles the eager decided count (2 → 4 of 113), after fixing the unbounded
  preprocessor.** Acting on the lazy-bv null result below, profiled the preprocessing
  passes on the 17.6 MB / 340 k-node giant: `solve_eqs` was the sole hog (**>150 s**
  there; every other pass <0.5 s). Added a **deterministic node-fuel budget**
  (`axeyum_rewrite::solve_eqs_bounded` / `DEFAULT_SOLVE_EQS_FUEL`, commit `96e55b6`) —
  charges per-round rebuild work (shared-memo node count, never wall-clock), bails to
  a **sound partial reduction** (un-eliminated equalities stay assertions; trail
  reconstructs). Giant now clears the whole pipeline in ~1.5 s. Wired into
  `check_with_preprocessing` + the bench. **Fair `--preprocess` measurement** (sat-bv,
  same budgets as the eager baselines, Z3 oracle, DISAGREE=0, 0 replay failures
  throughout): **3 s → 4 sat vs eager 2; 20 s → 7 sat vs eager 3** — more than doubling
  eager at both tiers, the gain *growing* with budget. The newly-decided instances drop
  out of `EncodingBudget` (13 → 11 at 3 s), i.e. preprocessing shrinks them below the
  bit-blast-size ceiling. First (and decisive) destination-2 gain on this corpus from
  *reduction* (the "not-building-the-mountain" lever), not abstraction — ratified in
  **ADR-0037** (reduction is the destination-2 priority; batsat stays default; custom
  cores specialized). Baselines
  `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-vs-z3-{3s,20s}-*.json`,
  `just bench-public-qfbv-preprocess-fair-{3s,20s}`. Probe:
  `axeyum-bench/examples/preprocess_timing.rs`. **Wired into the product:** the full
  model-sound pipeline now runs on the default `solve()`/`check_auto` path when
  `preprocess` is set (`check_auto_preprocessed`, reconstructs + replays), and
  **`Strategy::Auto` composes both levers** — lazy-bv for arithmetic-heavy queries,
  eager-with-preprocessing for structural ones. Full solver suite green.
  **Timeout-boundedness measured (kissat probe):** the 99 Timeouts split by CNF size —
  **~9 (≤300k clauses) are SAT-search-bound** (kissat 4.0.4 cracks them 2–18 s where
  batsat times out @20s; `mobiledevice_paired` 2 s vs >20 s), the **~90 larger
  (≥~650k) defeat even kissat** (reduction-bound). So **both levers are data-justified,
  partitioned by size** (ADR-0037 trigger partially fired): a competitive default SAT
  core for the small-CNF Timeouts, word-level reduction for the large-CNF bulk +
  6 EncodingBudget. **But the core bar is kissat-class:** the in-tree `xor_cdcl` core
  *also* fails `string1x8.4` (>120 s vs kissat 8.3 s), so converting the search-bound
  band needs a kissat-class solver (major P1.3; out of scope as a pure-Rust *default*,
  kissat is only a benchmark oracle). **Practical upshot: reduction is the higher-ROI
  near-term lever even for the search-bound band** (shrinking the CNF brings it within
  reach of the core we ship). Probes: `axeyum-bench/examples/{dump_dimacs,xor_cdcl_probe}.rs`.
  **Next:** (a) deeper reduction — `axeyum-rewrite` P1.2, the **other agent's active
  area; do not edit `canonical.rs`**; (b) flip `preprocess` default-on after a
  full-suite check; (c) long-term, close the SAT-core gap to kissat-class. Track
  **Timeout→decided** as the destination-2 pulse.
- **2026-06-18** — **Destination-2 fair re-measurement: lazy-bv vs Z3 on the public
  p4dfa 113 at the standing budgets — confirmed a no-op on this corpus.** Ran the
  built-but-fair-unmeasured `LazyBvBackend` head-to-head vs Z3 4.13.3 on the
  committed 113-file `20221214-p4dfa` public QF_BV slice at **identical node/CNF
  budgets to the eager `qf-bv-p4dfa-fair` baselines**, both tiers, `--jobs 2`:
  - **3 s** (node 200k, cnf 2M/5M): **lazy 3 sat / 110 unknown, DISAGREE=0, 0 replay
    failures** (eager 2/111). **20 s** (node 300k, cnf 3M/8M): **lazy 4 sat / 109
    unknown, DISAGREE=0, 0 replay failures** (eager 3/110). Baselines committed:
    `bench-results/baselines/qf-bv-p4dfa-fair-lazy-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`;
    reproduce via `just bench-public-qfbv-lazy-fair-{3s,20s}`.
  - **Honest finding:** `lazy_ops_total == 0` on **all 113** files (`grep` census:
    **0/113** contain any of `bvmul/bvudiv/bvsdiv/bvurem/bvsrem/bvsmod`); **0
    instances refined any op**; every decided instance was plain bit-blast. The
    consistent +1 over eager is a solve-path margin (the extra instances have
    `ops_total=0`), **not** a CEGAR win. lazy arithmetic-CEGAR is **structurally
    inert** on this arithmetic-free DFA/protocol slice. The 109–110 unknowns are
    87–98 Timeout (huge CNFs batsat can't crack) + 10–13 EncodingBudget + 1–10
    NodeBudget — the **eager-CNF-size wall**, not the multiplier wall.
  - **The number says:** the destination-2 lever for this corpus is **word-level
    reduction before blasting** (P1.2), which is blocked on the **unbounded
    preprocessor** (`solve_eqs`/canonicalize blow-up on the 17.6 MB / 215k-`ite`
    giants). NEXT: give the preprocessing passes a deterministic work budget so
    `--preprocess` bails instead of hanging → then measure `--preprocess` on the 113
    (the second committed measurement) → then the batsat-vs-custom-core ADR. See
    [lazy-bitblasting-p21-findings.md](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md).
- **2026-06-18** — **P3.7 destination-3 milestone: reconstructed refutations checked
  by a REAL Lean 4 kernel.** Installed a real Lean toolchain (elan + `leanprover/lean4`
  stable 4.31; the gold-standard checker, analogue of the Z3 oracle — a CI/cross-check
  tool, not a build dependency) and made the in-tree reconstruction externally
  verifiable end-to-end:
  - **`Kernel::render_lean_module`** (`axeyum-lean-kernel::lean_pp`): renders a
    self-contained `prelude`-mode Lean 4 module — every environment declaration
    reachable from goal+proof (transitive const-closure + topological sort;
    inductive/ctor/recursor emitted as `axiom`s carrying their kernel types), then
    `theorem axeyum_refutation : False := <proof>` + `#print axioms`. Numeric name
    components sanitized (`atom.0`→`atom._0`); `Succ` chains collapsed to numerals.
  - **`prove_unsat_to_lean_module`** (solver + façade): like `prove_unsat_to_lean`
    but also returns the Lean source. Same soundness gate (kernel-checks to `False`).
  - **Gated cross-check** (`tests/lean_crosscheck.rs`, skips without `lean`): the
    QF_UFBV (congruence), LRA (Farkas), ∀ (instantiation), and ∃ (skolemization)
    refutations each **type-check in real Lean 4** with `#print axioms` showing only
    the axeyum-declared logical/carrier/uninterpreted/`em`/hypothesis axioms — **no
    `sorryAx`**. The real Lean kernel independently corroborates the in-tree check.
    Honest boundary: inductive recursors are rendered as axioms (their generation is
    trusted, same as in-tree); a later slice can render real `inductive` commands to
    let Lean *derive* the recursors.
- **2026-06-17** — **Track-1 complement sweep (four lanes, alongside the proof/Lean
  agent).** Non-colliding Track-1 increments, each its own sound + tested + pedantic-
  clippy-clean commit:
  - **Differential soundness net** (`tests/differential_qfbv_backends.rs`): seeded
    random QF_BV cross-check across eager `SatBvBackend`, the new `LazyBvBackend`,
    and (feature `z3`) the oracle — DISAGREE=0 + every-`sat`-replays, 200 always-on +
    1500 ignored, 3-way clean. Guards both agents' solver churn.
  - **P1.2 / T1.2.4 `elim_unconstrained`** (`axeyum-rewrite`): unconstrained single-
    use invertible-op elimination, trail-reconstructed, wired into the opt-in
    `check_with_preprocessing`.
  - **P1.7 PBLS** (`pbls.rs`): word-level WalkSAT portfolio engine, one-sided sound
    (`Sat`/`Unknown`, never `Unsat`), deterministic.
  - **P1.3 SAT-core modernization** (`proof_sat.rs`): VSIDS + phase saving + Luby
    restarts on the proof-producing CDCL core (DRAT-checked ⇒ sound regardless).
  - **Round 2** (one more increment per lane): `elim_unconstrained` now peels
    `bvmul` by an odd constant (2-adic inverse); the CDCL core gained local
    learned-clause minimization (self-subsumption); PBLS switched to incremental
    scoring (re-eval only the moved variable's incidence set); and the soundness
    net's larger sweep now includes `PblsBackend` (one-sided `Sat` verdicts
    replayed + cross-checked at scale). All DRAT/replay-guarded, clippy clean.
- **2026-06-17** — **Fair public-QF_BV measurement + graceful oversized-encoding
  refusal (the "1/113" gap, diagnosed)**. The headline "sat-bv decides ~1/113 on
  public QF_BV" was an artifact of `--node-budget 1000` (refusing 112/113 at the
  DAG gate, all 1.3k–340k nodes), itself forced by a robustness bug.
  - **Fix (sat_bv_backend, P1.2 robustness):** a pre-lowering bit-blast-size
    *estimate* (per-op cost in result width: mul ~`w²`, div/rem ~`4w²`, shifts
    ~`w·log w`, else linear; `~3×` for Tseitin) now refuses oversized queries as
    `Unknown(EncodingBudget)` **before `lower_terms` allocates** — so a wide
    multiply degrades cleanly instead of OOMing. Absolute 64M-clause ceiling for
    the no-budget case. Regression test `oversized_multiply_is_refused_gracefully_not_oom`.
  - **Fetched the real 113-file public slice** (SMT-LIB 2024 QF_BV, Zenodo 11061097,
    `20221214-p4dfa-XiaoqiChen`) and ran the fair head-to-head vs Z3 4.13.3.
  - **Result (node 200k, 5M-clause cap, 3s):** **2 sat decided, 0 disagreements,
    0 replay failures, 111 unknown** = 88 **Timeout** (admitted + bit-blasted to
    140k–4.6M-clause CNFs, BatSat can't solve in 3s), 13 EncodingBudget, 10
    NodeBudget. **101/113 lowered without OOM** (RSS ~1.5GB — fix works).
  - **Ceiling (node 300k, 8M-clause cap, 20s):** **3 sat decided**, 110 unknown
    (99 Timeout, 10 EncodingBudget, 1 NodeBudget). 6.7× more time + bigger budgets
    moved decided only 2→3.
  - **Diagnosis:** the gap is **architectural, not robustness (fixed) and not a
    timeout/budget knob.** Eager bit-blasting these word-level instances yields
    ~million-clause CNFs our SAT path can't crack in seconds, while Z3 reasons at
    the word level (~1s each). The honest fair number is **2–3 / 113**, with the
    bottleneck precisely located → Track 1: word-level preprocessing (P1.2), lazy/
    word-level bit-blasting (P2.1), SAT-core modernization (P1.3). Baselines:
    `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`.
- **2026-06-17** — **Curriculum backlog Tier A–D built (19 items): NT/poly/algebra/LA
  families + 2 sound NRA engine fixes**. Worked the curriculum
  [BACKLOG.md](docs/curriculum/BACKLOG.md) end to end; drawn from Stein/Shoup/VMLS
  (see [foundational-books/source-tocs.md](docs/curriculum/foundational-books/source-tocs.md)).
  - **Tier A (decidable, #1–8):** `Family::NumberTheory` += CRT-witness, quadratic
    residue (SAT) / non-residue (UNSAT), sum-of-two-squares (SAT + `n≡3 mod 4`
    UNSAT), Pythagorean triple; `Family::Polynomial` += factor-theorem identity;
    `Family::Algebra` += 𝔽ₚ-all-invertible (UNSAT) / composite-modulus
    non-invertible (SAT, via a `∀b` finite-domain quantifier). Solver/LRA tests:
    **linear algebra over ℚ** (`Ax=b` solvability + Farkas-refuted inconsistency,
    `tests/linear_algebra_rational.rs`); **rationals node** (density/antisymmetry/
    transitivity, Farkas-certified, `tests/rationals.rs`); **proofs node via
    pigeonhole** (`PHP(5,4)` UNSAT with a re-checked certificate + permutation SAT,
    `tests/pigeonhole_proof.rs`).
  - **Tier B (#9–13):** `Family::Predicate` += Fermat's little theorem at fixed
    `p∈{3,5}` (`∀a`); `Family::Polynomial` += division-with-remainder identity;
    `Family::NumberTheory` += RSA round-trip (`(mᵉ)ᵈ≡m mod 33`, modular-exp with
    per-step reduction); `Family::LinearAlgebra` += 3×3 `det(AB)=detA·detB` over 𝔽₂;
    #13 ("watch a formula become CNF→SAT") realized by the existing
    `scenario_pipeline_report`/`curriculum_demo`/`BvLayerStats` observability.
  - **Tier C — NRA/prove engine (#14–16), measured & sound:** **#14** the
    `prove`/`produce_evidence` front door now **dispatches nonlinear real goals to
    NRA** (`produce_nra_evidence`) instead of hard-erroring `Unsupported`;
    soundness-probed (NRA does not claim `x²<0` Sat). **#15** NRA now honors a
    **wall-clock deadline** threaded through `branch_and_bound` + the refinement
    loop (the `a²+b²≥2ab` case returns `Unknown` in ~5s instead of hanging 60s+;
    the Spivak SOS-frontier test is now active, not `#[ignore]`d). **#16** a real
    SOS/positivstellensatz that *proves* the SOS inequalities is genuine P2.5/L
    work — **designed and deferred** (sketch in spivak.md), not faked.
  - **Tier D (#17–19):** decidable-geometry node — the *linear* slice (midpoint
    equidistance/betweenness, LRA Farkas, `tests/decidable_geometry.rs`; polynomial
    geometry is #16-gated); Peano-induction **reconstruction-target stubs**
    (`docs/curriculum/reconstruction-targets/`: `.smt2` + Lean, *targets not
    benchmarks*); **"fill the proof step" grader** — `check_alethe` accepts a
    complete proof and rejects one missing its closing step
    (`tests/proof_step_grading.rs`).
  - **Verified:** 57 `axeyum-scenarios` tests + new solver tests (decidable_geometry
    2, proof_step_grading 2, linear_algebra_rational 3, rationals 3, pigeonhole_proof
    3, spivak 5) all green; fmt/clippy/doc/link-check clean. (Transient: the
    concurrent CDCL(XOR) WIP in `axeyum-cnf` intermittently blocked the solver build;
    re-ran green once fixed.)
  - **References noted:** Software Foundations being translated to Lean + Verso
    (`docs/curriculum/foundational-books/proof-assistants.md`) — the Lean-horizon
    curriculum to align with.
- **2026-06-17** — **Spivak *Calculus* Ch.1 benchmark + the "decidability-ceiling"
  curriculum docs**. Engaged Spivak (and foundational texts) honestly: most of the
  book is ε-δ (Lean-horizon), but **Chapter 1 — the ordered-field axioms P1–P12 and
  the foundational inequalities — is the decidable shadow** where axeyum's LRA/NRA
  live. New (Opus-research-driven):
  - **`crates/axeyum-solver/tests/spivak_inequalities.rs`** — a certificate-bearing
    benchmark. **Order transitivity** proved via the `prove` front door (Farkas,
    re-checked); a **monotonicity inequality** (`x≥1 ∧ y≥1 ⇒ xy≥1`) proved by NRA.
    The **sum-of-squares inequalities** (`a²+b²≥2ab`, AM–GM₂, Cauchy–Schwarz) are
    the **NRA frontier** — kept `#[ignore]`d (they don't terminate promptly). 3
    active tests pass, 1 ignored.
  - **Two measured engine findings** (recorded in
    [formal-mathematics-tour.md](docs/research/08-planning/formal-mathematics-tour.md)):
    (1) `prove` has **no LRA→NRA dispatch** (rejects nonlinear real goals as
    `Unsupported`); (2) the linearization NRA (ADR-0024) **cannot prove SOS
    inequalities — even `a²+b²≥2ab`** — because it abstracts the squares to
    independent variables; sharp motivation for an SOS/positivstellensatz/CAD path
    in P2.5. (The initial assumption that NRA proves these was *wrong*; the probe
    corrected it — what a benchmark is for.)
  - **Curriculum honesty docs**: `docs/curriculum/DEPTH.md` (the map-vs-territory
    scope ceiling — `covered` ≠ textbook depth; the decidability ceiling) and
    `docs/curriculum/foundational-books/` (README + `spivak.md`: how canonical texts
    project onto the LRA/NRA/Lean-horizon split).
  - **`Family::NumberTheory` extended**: `pythagorean_triple` (`a²+b²=c²`, witness
    (3,4,5)) — number theory meets geometry, SAT-by-witness.
  - 57 scenarios tests green; Spivak suite green; clippy/doc/link-check clean in
    isolation.
- **2026-06-17** — **CDCL(XOR) foundation — path 2 of the multiplier wall, 3 sound
  slices + design record** (commits b745772, 8a3415a, 8b21359, 3099964). The
  diagnosed perf lever for the curated unknowns (var*var multiplier-equivalence with
  exponential resolution lower bounds — no path-1 rewrite cracks them) is now an
  *engine*, built in `axeyum-cnf` as three independently-tested slices:
  - **`gf2.rs`** — GF(2) linear (XOR) system solver: `Gf2System` Gaussian-eliminates
    `(⊕ of a var set) = parity` constraints (bit-packed `Vec<u64>` rows, duplicates
    cancel by parity) to RREF; `0=1` row ⇒ `Unsat`, else a satisfying assignment +
    `implied_units` (single-var rows) + `implied_equalities` (two-var rows). 16 tests,
    backbone invariant "the assignment satisfies every input constraint."
  - **`xor_extract.rs`** — sound XOR-gate extraction: `extract_xors(cnf)` recognizes a
    width-`k` gate **only** when a variable-set group is the exact `2^(k-1)`-clause
    complete one-parity encoding (rhs derived from that parity; `k≤8`). Exact ⇒ false
    positives impossible (missing/extra/dup/mixed-parity/over-cap ⇒ not recognized).
    19 tests incl. a brute-force truth-table parity check + the no-false-positive set.
  - **`xor_propagate.rs`** — preprocessing pass in the `simplify`/`eliminate_variables`
    idiom: `xor_propagate(cnf) -> { Unsat, Propagated { formula, stats } }`. A
    contradictory entailed XOR subsystem proves the formula UNSAT; the solver's implied
    units (entailed ⇒ model-preserving) are appended. Brute-forced over all `2^n`
    assignments: model-set preservation, UNSAT soundness **and its converse** (a sat
    formula is never reported unsat), no-op. `implied_equalities` substitution deferred.
  - **Slice 4 DONE & measured** (commits edf65b8, 160408c): `xor_propagate` wired into
    `sat_bv_backend`'s `inprocess` (behind `cnf_inprocessing`, off by default; sound
    Propagated branch only, 20k-clause Gaussian cap). Curated slice (`--inprocess`, 2 s):
    **33 decided, DISAGREE=0, 0 replay failures, PAR-2 0.968 vs 0.963 plain** — sound, no
    regression. **Extraction fired on 20/43 files → 12 908 XOR gates but only 1 implied
    unit** ⇒ on-corpus proof that multiplier parity forces ~no units at preprocessing.
    **Slice 5 (equality substitution) measured & deprioritized** (commit 2a6190d): the
    gates expose **351 equalities** but they concentrate on the AC-structured commute/
    distrib/bit-counting instances (commute08=101, distrib04=40), **~0 on the genuine
    multiplier unknowns** (mulhs16=1, stp_samples=0, calypto_9=1) — they'd only help
    instances the AC canonicalizer already targets. **Static-preprocessing path 2 is
    closed: neither units nor equalities crack the curated multiplier unknowns.**
    **Slice 6 (the real lever):** full CDCL(XOR) — in-search Gaussian on the CDCL trail
    (CryptoMiniSat `gaussian.cpp`), the only form that sees the nonlinear AND-gate
    partial-product structure static preprocessing can't; reuses the validated `gf2`/
    `xor_extract` foundation. Design note has the full measurement.
  - **Slice 6 primitive DONE** (commit 9b449b7): `xor_search::xor_implications(constraints,
    num_vars, assignment: &[Option<bool>]) -> { Conflict{reason}, Implied{lits+reasons} }`
    — the pure propagation primitive the in-search Gaussian calls at each CDCL node. Folds
    the partial assignment into the system and reuses `gf2.rs` (Unsat ⇒ Conflict; reduced
    `implied_units` ⇒ forced literals); reasons are a sound (non-minimal) component
    over-approximation. 18 brute-force tests (conflict/implication soundness over all
    completions, completeness on small systems, reason soundness, 3^n exhaustive
    cross-check, empty-assignment vs `Gf2System::solve`). 187 cnf tests green.
  - **Slice 6 integration validated** (commits 858a644 design, d7a8cd0 decider): the
    proof/trust crux is resolved in
    [cdcl-xor-integration-design.md](docs/research/05-algorithms/cdcl-xor-integration-design.md)
    — XOR reasoning isn't resolution, so XOR-assisted `unsat` becomes a ledgered
    **`TrustId::XorGaussian`** hole (no false DRAT), demotable via an algebraic/PAC
    certificate (path 3); `sat` is already free (model replays). First integration landed:
    `xor_dpll::solve_with_xor` — a correctness-first XOR-aware DPLL (clause-UP ⇄
    `xor_implications` fixpoint, chronological backtrack, no learning/proof yet, step-budget
    → Unknown). **400 brute-force-oracle + 300 batsat differential checks, zero
    disagreement**; every `Sat` model satisfies clauses AND XOR constraints. 196 cnf tests.
  - **Decision ratified — ADR-0035 accepted** (commit 2ea892e): CDCL(XOR) search
    acceleration with a ledgered `XorGaussian` trust hole (no false DRAT; `sat` free;
    demotable via path-3 PAC certificate). The protocol gate is cleared.
  - **Competitive CDCL(XOR) solver DONE** (commit 024596b): `xor_cdcl::solve_with_xor_cdcl`
    — conflict-driven search with clause learning + **watched-literal XOR propagation**
    (CMS `gausswatched` style: a constraint forces its last unassigned var with a minimal,
    **antecedent-valid** reason — the other vars of that constraint, all pre-assigned — which
    is what 1-UIP needs; the Gaussian `xor_implications` component-reasons are not
    antecedent-valid, so the watched scheme is used in-search). XOR antecedents enter 1-UIP as
    synthesized reason clauses. Search-only (no DRAT); isolated (models on `proof_sat`, does
    not touch it). **1,500-formula differential (brute oracle + batsat + `xor_dpll`), zero
    disagreement**; parity-chain UNSAT cases confirm learning fires. 209 cnf tests. Complete
    Gaussian-on-trail (row-provenance reasons) for the parities the watched scheme misses is
    the deferred enhancement.
  - **PATH-2 THESIS CONFIRMED + sped up — CDCL(XOR) cracks the small multiplier wall**
    (commits 577c973 harness, b863d1c note, fea810a VSIDS, aadd0da correction). Robust win on
    `mulhs08` (655 v/2716 cl): **batsat `unknown`@2s (reproducibly) → `solve_with_xor_cdcl`
    UNSAT** — a multiplier-equivalence instance plain CDCL provably cannot crack. Adding the
    P1.3 modernization (**VSIDS + phase saving + Luby restarts**) cut it **20.1 s → ~5.0 s
    (~4×)**, verdict + all ~1,500-formula soundness differentials unchanged. So the
    decomposition is confirmed AND acted on: XOR propagation = the capability, competitive
    heuristics = the speed. (Correction: `calypto_9` is *borderline* for batsat — ~1.1 s some
    runs — so not a clean separator; `mulhs08` is the solid one.) **Honest ceiling:** `mulhs16`
    / larger `stp_samples` still don't decide in minutes even with VSIDS — the next size class
    needs the **complete Gaussian-on-trail propagator** (watched-literal XOR is sound but
    incomplete) and/or more SAT-core work. 212 cnf tests; clippy/fmt clean.
  - **Wired into the product `solve()` path** (commit 6505441, ADR-0035): new
    `SolverConfig::xor_cdcl_fallback` (default OFF) — on a batsat `Unknown` over an
    XOR-structured formula (≤50k clauses), runs `solve_with_xor_cdcl`; **`unsat` = the new
    `TrustId::XorGaussian` ledgered hole** (no DRAT — XOR isn't RUP; backed by the differential
    validation), **`sat` replays** through the existing AIG/model/term path (no trust cost).
    Default-off ⇒ zero baseline change. **`mulhs08` now returns UNSAT through `SatBvBackend`
    with the flag on** — the breakthrough is reachable through the product, not just a test.
    Trust ledger now has 6 holes (added `xor-gaussian`); 8 new tests; full solver suite green.
  - **Measured negative — complete backstop must be incremental** (commit ca19a5f): calling
    the complete `xor_implications` Gaussian as a fixpoint backstop is sound (differentials
    green) but a net regression — from-scratch Gaussian per decision level makes `mulhs08`
    2.3× and `calypto_9` 19× slower and still doesn't crack `mulhs16`/`stp_samples`. Reverted.
    The next size class needs a **true incremental GF(2) matrix** (row-reduce-on-assign /
    restore-on-backtrack, CMS `gausswatched.h`/`packedmatrix.h`), not repeated rebuilds.
  - **Incremental matrix built + 2nd measured negative** (commits 83b99b2 matrix, 6c4407a
    note): `IncrementalXorMatrix` (RREF over free columns, per-assign column-substitution,
    backtrackable, **bit-for-bit oracle-validated** vs `xor_implications` over 100s of random
    systems×sequences; 14 tests) is built and committed as the foundation. But wiring it into
    `xor_cdcl` (sound — all differentials green) made `mulhs08` go 5 s → **>280 s**: it's
    called on every trail assignment and still scans all rows mentioning the var
    (`O(rows·words)`). Reverted. **Twice-confirmed sharp requirement: the propagator must be
    the watched-echelon-row scheme** (CMS `gausswatched.h` — each echelon row watches two free
    vars, so an assign touches only `O(1)` rows). The validated matrix is the foundation; the
    two-watch index over its rows is the remaining decisive optimization. `xor_cdcl` keeps the
    cheap incomplete watched-literal XOR prop until then.
  - **Watched-echelon-row index DONE + 3rd result = course correction** (commits 3ca0340
    matrix watch index, 9c49437 note): the watch index landed (**~25× fewer rows examined per
    assign**, full RREF for completeness, all oracle differentials green). Re-integrated into
    `xor_cdcl` — **sound** (every differential green; parity chains close at level 0) but
    `mulhs08` **still** regressed past 300 s. Decisive cause: **`mulhs08` has ~1 XOR gate among
    655 vars** — the matrix adds no propagation power while replacing the near-free
    watched-literal scheme with overhead. **`mulhs08` was cracked by `xor_cdcl`'s competitive
    CDCL core (VSIDS/restarts/1-UIP), NOT by XOR reasoning.** The curated unknowns are *not
    XOR-dense*, so in-search Gaussian is the wrong lever for them. Integration reverted; the
    watched-row matrix stays a **validated, unwired component** for an XOR-dense corpus (behind
    a density guard + incremental journal). **For the curated next size class the lever is
    P1.3 SAT-core modernization, not more XOR machinery.**
  - **P1.3 clause deletion DONE + localizes the next blocker** (commit 839518e): LBD-based
    learned-clause deletion added to `xor_cdcl` (the standard missing piece — clause DB grew
    unboundedly before). Sound (differentials green), `mulhs08` 5.3 s **no regression**, DB now
    memory-bounded. Honest measurement: `mulhs16`/`stp_samples` still UNKNOWN — they exhaust the
    **2M-conflict budget** (182 s/433 s), i.e. hit the conflict CEILING, not a clause-DB wall.
    So the curated next-size-class blocker is **branching/restart strength / the conflict
    ceiling**, not clause management.
  - **Next options (fresh context):** (a) more P1.3 — stronger branching/restarts (the now-
    localized curated blocker), though Kissat-class is a long road with diminishing per-step
    returns; (b) **Lean kernel inductive layer** (deepest open destination-3 slice — studied,
    soundness-careful port of nanoda's 1677-LOC inductive.rs); (c) broaden Track 2/3/4 (e.g.
    wire the integer-systems Diophantine certificate into evidence/get-proof).
  - **Next (fresh context, ADR-cleared):** wire `xor_implications` into the *production*
    proof-producing CDCL core (`proof_sat`, which has 1-UIP + watched literals) as a
    search-only theory propagator — DRAT suppressed when an XOR reason participates, the
    `unsat` carrying the new `XorGaussian` trust id (land `trust.rs` + golden ledger +
    trust-ledger.md **with** this producer, not before it). Then dispatch wiring +
    curated-multiplier measurement (`DISAGREE=0`) — the first technique that *can* reach
    `mulhs*`/`stp_samples`/`calypto`. The naive `xor_dpll` decider validates soundness; the
    production core (learned clauses) is what makes it competitive. Soundness-critical
    proof-core surgery ⇒ fresh context.
  - All verified **per-crate** (`axeyum-cnf`: 168 tests; `axeyum-solver`: full suite
    green; clippy `-D warnings` + fmt clean) — and now the **full workspace builds +
    test-compiles** (the concurrent math-tour errors resolved). std only, no new deps.
- **2026-06-17** — **Math-tour curriculum — Predicate logic + Number systems;
  coverage now 14/23 nodes**. Two more research→build cycles, oracle-free (ADR-0008):
  - **`Family::Predicate`** (`predicate`): closed quantified theorems the evaluator
    decides by finite-domain expansion — `forall_additive_identity` (∀x. x+0=x),
    `forall_exists_inverse` (∀x ∃y. x+y=0, genuine **quantifier alternation**),
    `exists_square_root` (∃x. x²=4, SAT). Exercises the finite-domain quantifier
    path. → mathtour `predicate-logic` Covered.
  - **`Family::NumberSystem`** (`number_system`): order + Peano structure —
    `signed_trichotomy`, `order_transitivity` (→ `integers`), `unsigned_non_negative`,
    `successor_injective` (→ `naturals`). Exhaustive UNSAT-of-negation over signed/
    unsigned BV. → mathtour `integers` + `naturals` Covered.
  - mathtour.rs ↔ curriculum.toml ↔ node markdown synced (invariant test enforces).
    Curriculum coverage **11 → 14 of 23 nodes** (added predicate-logic, naturals,
    integers). 57 `axeyum-scenarios` tests green; fmt/clippy/doc/link-check clean in
    isolation.
  - Remaining gaps: SAT/CNF, bit-blasting, proofs, decidable-geometry, calculus,
    sequences-limits, cardinality, complex, rationals, reals (number-systems upper
    rungs + lean-horizon analysis). NEXT high-value: ℚ/NRA (linear algebra solving,
    calculus RCF inequalities) → the corpus P2.5 lacks; proofs via a DRAT/Alethe demo.
- **2026-06-17** — **Math-tour curriculum — 3 more families (Polynomials,
  Verification, Sets) + ring/field structure; coverage now 11/23 nodes**. Continued
  the research→build cycles; all oracle-free (ADR-0008), inside the BV subset:
  - **`Family::Polynomial`** (`polynomial`): `binomial_square` ((x+y)²=x²+2xy+y²),
    `difference_of_squares`, `quadratic_root` (x²−5x+6=0, root `x=2` witness). →
    mathtour `polynomials` Covered.
  - **`Family::Verification`** (`verification`, Opus-research-driven): the
    "Hello, World" of program safety — `abs_non_negative_bug` (SAT, `INT_MIN`
    counterexample), `midpoint_overflow_bug` (SAT, the Bloch binary-search bug,
    witness `lo=hi=2^(w−2)`), `max_is_an_upper_bound`, `unsigned_overflow_idiom`,
    `saturating_add_safe` (UNSAT-of-negation theorems). → flips the **solver-capability
    concept `SoftwareVerification`** from gap to Covered (concept.rs).
  - **`Family::Sets`** (`sets`): set-algebra laws over subset bitmasks —
    `distributivity`, `absorption`, `complement_union_is_universe` (set algebra IS
    Boolean algebra). → mathtour `sets` Covered.
  - **`Family::Algebra` extended**: `zero_divisor` (SAT — ℤ/2ʷ is a ring but not an
    integral domain) and `field_failure_even` (UNSAT — even elements have no inverse,
    so ℤ/2ʷ is not a field). → mathtour `rings` + `fields` Covered.
  - **mathtour.rs ↔ curriculum.toml ↔ node markdown synced** (the
    `covered_nodes_have_a_family_realized` invariant test enforces it). Curriculum
    coverage **7 → 11 of 23 nodes** (now: propositional-logic, sets, divisibility,
    modular-arithmetic, groups, rings, fields, polynomials, counting, number-theory,
    linear-algebra).
  - **54 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean in
    isolation.** Each family doubles as theory coverage (BV bitwise/arith, signed/
    unsigned comparisons, div/mul, ite) on structured, scalable, oracle-free instances.
  - NEXT (still gaps): SAT/CNF, bit-blasting, proofs, decidable-geometry, calculus,
    sequences-limits — plus ℚ/NRA variants (the corpus P2.5 lacks).
- **2026-06-17** — **Math-tour curriculum advanced — 3 more families built (Opus
  sub-agent + web research)**. Three Opus research sub-agents (pigeonhole/proof
  complexity, finite-algebra/quasigroup encodings, linear-algebra-over-finite-fields)
  informed three new self-checking families, all oracle-free (ADR-0008) and inside
  the BV subset:
  - **`Family::LinearAlgebra`** (`linear_algebra` module): `2×2` matrix identities
    over `BitVec` — `det_product_2x2` (det(AB)=detA·detB), `transpose_product_2x2`
    ((AB)ᵀ=BᵀAᵀ), `mult_associative_2x2` (over 𝔽₂), exhaustive UNSAT of the negation;
    `linear_solve_2x2` (Ax=b, solution as witness). Covers mathtour `linear-algebra`.
  - **`Family::Counting`** (`counting` module): the **pigeonhole principle**
    (`pigeonhole`, n+1 pigeons → distinct hole indices is UNSAT, PHP(5,4)=1024 cases
    exhaustive) + `permutation_exists` (n→n distinct is SAT, identity witness). A
    proof-complexity landmark (Haken 1985; Beame–Pitassi–Impagliazzo 1993). Covers
    mathtour `counting`.
  - **`Family::Algebra`** (`algebra` module): group axioms over ℤ/2ʷ —
    `addition_associative`, `additive_inverse` (exhaustive UNSAT of negation) +
    `subtraction_not_associative` (SAT counterexample, witness `(0,1,1)` — shows
    subtraction is not a group operation). Covers mathtour `groups`.
  - **mathtour/TOML/markdown synced:** `groups`, `counting`, `linear-algebra` flipped
    to `covered` in both `curriculum.toml` and `mathtour.rs` (the invariant test
    `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` enforces the
    sync). Curriculum coverage now **7 of 23 nodes** with a self-checking exercise.
  - **48 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean in
    isolation.** (Full `just check` still blocked only by the other agent's in-progress
    `axeyum-smtlib`/`axeyum-rewrite` WIP — transient.)
  - **Each family doubles as theory test coverage:** number theory + counting + algebra
    + linear algebra stress BV multiply/add/sub and the bit-blast→SAT path on
    structured, scalable, oracle-free instances. NEXT: ℚ/NRA linear algebra
    (Farkas-certified solving, det identities) and calculus RCF inequalities → the
    NRA corpus P2.5 lacks.
- **2026-06-17** — **Formal Mathematics Tour — curriculum knowledge graph + first
  destination built**. A structured, machine-readable curriculum derived by working
  *backward* from calculus / number theory / linear algebra to foundations, with
  axeyum's decidable/computable fragment per node.
  - **Knowledge graph** at [`docs/curriculum/`](docs/curriculum/README.md): an
    authoritative `curriculum.toml` (23 nodes, prerequisite edges, decidability +
    family + status metadata) + a README index (DAG, decidability/status legends)
    + **one markdown file per node** across `00-foundations/` (7), `01-number-systems/`
    (5), `02-structures/` (8), `03-destinations/` (3), each with summary · role ·
    prerequisites/unlocks · *testable in axeyum* (with example exercises) ·
    Lean-horizon · references. Grounded in Lean Mathlib, Metamath set.mm, and
    bridge-course canon.
  - **Decidability lens (the load-bearing filter):** each node's testable slice maps
    to an axeyum theory (number theory → BV/LIA, linear algebra → LRA/NRA, calculus
    → NRA); ∀-general theorems (infinitude of primes, ℝ-completeness, ε–δ) are
    flagged `lean-horizon`, never benchmarks. So building math-tour exercises *also*
    grows the arithmetic-theory corpora axeyum lacks (esp. NRA / P2.5).
  - **Code mirror:** `axeyum-scenarios::mathtour` — a queryable `MathNode` table
    mirroring the TOML, with topological teaching order and invariant tests (acyclic,
    prerequisites exist, every `Covered` node's family is realized by a self-checking
    scenario). 6 tests.
  - **First destination built:** `Family::NumberTheory` (`number_theory` module) —
    Bézout's identity (witness from extended Euclid), modular inverse (Hensel-lifted),
    "product of consecutive integers is even", "x² ≡ x (mod 2)". Oracle-free
    (SAT-by-witness / UNSAT-by-exhaustive), inside the BV subset. 4 tests; wired into
    the coverage aggregator and the mathtour `Covered` mapping.
  - Research note: [formal-mathematics-tour.md](docs/research/08-planning/formal-mathematics-tour.md).
  - **41 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc/link-check clean
    in isolation.** (Full `just check` still blocked only by the other agent's
    in-progress `axeyum-smtlib` parse.rs — transient.)
- **2026-06-17** — **Double-duty educational layer — FIRST CUT BUILT (ADR-0033)**.
  The self-checking scenarios now double as curriculum, built bottom-up across
  ADR + 5 modules + an integration demo, all within `axeyum-scenarios`' existing
  deps (no new solver surface, no DAG change):
  - **ADR-0033** ratifies the double-duty artifact contract (concept-DAG node +
    statement/solution renderers + *measured* difficulty; grading via the trusted
    checker, never the search) and the crate boundary (extend `axeyum-scenarios`;
    extract `axeyum-edu` later per ADR-0001).
  - **`concept`** — a 15-node curriculum DAG derived from `foundational-dag.md`:
    acyclicity-checked `prerequisites`, deterministic `topological_order`,
    `frontier(mastered)`. 6 tests.
  - **`render`** — `Renderable` (problem statement + worked solution from the
    witness/UNSAT evidence). 2 tests.
  - **`exercise`** — `Exercise` with curriculum placement, measured `Difficulty`,
    and a **sound auto-grader**: a candidate is judged by `Scenario::is_satisfied_by`
    (the evaluator), so a wrong/empty witness is *rejected by evaluation*, never
    silently accepted. 5 tests.
  - **`coverage`** — the concept DAG as a test-coverage map; the key test
    (`every_declared_family_is_realized_by_a_self_checking_scenario`) fails if a
    concept claims coverage no self-checking scenario provides. 8/15 concepts
    covered; 7 gaps tracked honestly. 5 tests.
  - **`logic`** — propositional `Family::Logic` (modus ponens, excluded middle,
    De Morgan, contradiction, a SAT clause) proven by exhaustive truth tables —
    closes the bottom-rung `PropositionalLogic` concept. 2 tests.
  - **`axeyum-bench` `curriculum_demo` example** — ties it together end to end and,
    for the De Morgan BV identity, emits a **136-command Alethe proof re-checked
    VALID in-tree by `check_alethe`** (proof as worked solution; length as a
    proof-level difficulty signal). Demonstrates the whole thesis in one run.
  - **31 `axeyum-scenarios` tests green; fmt/clippy(pedantic)/doc clean in
    isolation.** Full `just check` is red only on the *other agent's* in-progress
    `axeyum-smtlib` parse.rs (concurrent PLAN build) — transient, not from this work.
  - Docs: rev-2 example-suites note (educational lens), ADR-0033, and a new
    "Curriculum / Educational Layer" section in consumer-scenario-models.md.
- **2026-06-17** — **P1.2: opt-in `preprocess` flag on the `solve`/`check_auto`
  façade**. New `SolverConfig::preprocess` (+ `with_preprocess`), default **off** —
  mirrors the existing `cnf_inprocessing` lever. When set, `check_auto` runs the
  denotation- and symbol-preserving canonicalizer over the assertions before its
  existing coercion-rewrite chain and dispatch; the returned `sat` model is
  unchanged (no variables eliminated) and still satisfies the originals. Makes
  word-level preprocessing reachable through the main `solve()` entry point, not
  just `check_with_preprocessing`: a 32-bit `(not (= (a*b) (b*a)))` via
  `solve(..with_preprocess(true))` returns unsat **instantly, no multiplier blast**
  (new `solve` test). Default-off ⇒ zero change to existing behavior/baselines; full
  gate green. Flipping the default remains a separate measured decision (ADR).
- **2026-06-17** — **P1.2: canonicalizer wired into `check_with_preprocessing`**.
  The denotation-preserving canonicalizer (`canonicalize_terms`) is now the FIRST
  pass in `check_with_preprocessing`, ahead of `propagate_values` + `solve_eqs`. It
  eliminates no variables (symbol-preserving), so it needs no reconstruction trail —
  the model still replays against the original assertions. This activates the prior
  commit's commutative-operand ordering in an actual solver path: a 32-bit
  `(not (= (a*b) (b*a)))` is now refuted **instantly by canonicalization, with zero
  multiplier bit-blasting** (new test returns in 0.00 s where a genuine 32×32 blast
  would be slow). Closes the "canonicalizer dormant in the product" gap for the
  opt-in preprocessing path. 6 preprocess tests green. (Default `solve()` still does
  not preprocess — making it the default is a separate decision, likely an ADR.)
- **2026-06-17** — **Research note: foundational example & benchmark suites**
  ([docs/research/08-planning/foundational-example-suites.md](docs/research/08-planning/foundational-example-suites.md)).
  Research-first, no code. Scopes the next wave of example suites by
  *decidability*, not appetite: (A) a self-checking software-verification
  "Hello, World" tier (SV-COMP `ReachSafety`/`NoOverflows` shape, hand-ported,
  reusing BMC/k-induction/symexec — **recommended first**, satisfies the open
  Phase 7 verification-audience criterion); (B) decidable geometry / real-closed
  fields as the QF_NRA/P2.5 corpus that's currently missing (witness-checked
  `sat`; `unsat` exposes the NRA-certificate evidence gap); (C) a low-cost
  finite/modular "math 101" extension of `Family::Identity`. The prompt's
  "Peano 101 / real analysis 101" is split out: induction-bearing arithmetic and
  the ε–δ layer are **undecidable → Lean-horizon proof-reconstruction targets
  (P3.6/P3.7), not benchmarks**; only the RCF-reducible fragment (geometry,
  MetiTarski-style inequalities) is reachable now. Surveys SV-COMP, SMT-LIB
  QF_NRA/meti-tarski, GeoCoq/Tarski, TPTP as yardsticks (mine for shape; do not
  ingest/sweep). Proposes **ADR-0033** to ratify the A/B/C-build, D-target tier
  split. Next: design suite A's first cut.
- **2026-06-17** — **Educational/double-duty lens added (rev 2 of the example-suites
  note)**. Thesis: the architecture that makes an artifact a good *test* is the same
  that makes it good *educational content* — a self-checking, seeded,
  evidence-exhibiting scenario placed in a concept DAG **is** a homework problem
  with a sound auto-grader and a worked solution. axeyum has the four otherwise-hard
  assets: (1) **sound auto-grading for free** because grading is *trusted checking*
  (`eval`/`evidence.check`/`check_alethe`), not search; (2) **certified procedural
  generation** (ADR-0008's SAT-by-execution / UNSAT-by-identity are the two
  procedural-content patterns, with machine-checked answer keys); (3) **measured
  difficulty** (CDCL conflicts, CNF size, Alethe/LRAT proof length); (4) **the
  concept DAG already exists** as the engineering gate (`foundational-dag.md`) —
  formalizing it gives curriculum order + a test-coverage audit + the gate (triple
  duty). Angle 1 (generate): homework banks from generators, a `check_alethe`-graded
  "fill the proof step" tutor, DAG-frontier sequencing — solver
  generates/grades/certifies/sequences *formal* exercises only, narrative stays
  human/LLM. Angle 2 (teach about): glass-box pipeline → a course map keyed to
  axeyum's own layers, with suite D reframed as a *lesson on undecidability*. Adds
  three thin, ADR-gated, no-solver-surface capabilities (rendering layer,
  machine-usable concept-DAG, concrete-execution trace = worked solution). Hard
  rules recorded: education is a consumer/lens that must not starve a foundation
  phase; grading must route through the trusted checker, never the search. ADR-0033
  scope extended to ratify the double-duty artifact contract.
- **2026-06-17** — **P1.2: commutative-operand canonicalization (word-level
  preprocessing)**. The denotation-preserving canonicalizer now sorts the operands
  of commutative ops (`and`/`or`/`xor`/`=`, `bvadd`/`bvmul`/`bvand`/`bvor`/`bvxor`/
  `bvnand`/`bvnor`/`bvxnor`) by ascending `TermId`, so `(bvmul a b)` and `(bvmul b a)`
  hash-cons to the **same** term — composing with the existing
  `=`-structurally-identical rule to fold `(= (bvmul a b) (bvmul b a))` → `true` with
  no bit-blasting. Strictly excludes non-commutative ops (`bvsub`, div/rem, shifts,
  comparisons, `concat`, and crucially `apply` — UF arg order is meaningful).
  Denotation verified by exhaustive 3-bit evaluator equivalence. **Curated slice with
  `--rewrite default`: 33/43 decided (was 32), 10 unknown (was 11), PAR-2 1.010 (was
  1.062), DISAGREE=0** — a real, sound +1 (cracks `calypto_problem_9`). **Honest
  caveat:** the targeted `wienand commute08/16` stay unknown — they are
  associativity+commutativity over multiplier *trees* with intermediate `var`
  bindings, not flat `a*b==b*a`; cracking them needs multiplier-tree AC-normalization
  + intermediate-equality inlining (a larger, separate task). Also: the bench default
  is `--rewrite Off`, so this only helps when rewriting is enabled — wiring the
  canonicalizer into the default `sat-bv` path is a follow-up.
- **2026-06-17** — **Benchmarking checkpoint: no regression + the perf ceiling
  diagnosed**. Re-ran axeyum (`sat-bv`, 2 s) over the committed 43-file curated QF_BV
  slice after the session's 21 proof-track commits: **32/43 decided (8 sat + 24
  unsat), 11 unknown, PAR-2 = 1.062 s** — matches the committed baseline (32/43,
  PAR-2 ≈1.07 s) exactly, so the proof work caused **zero performance regression**.
  All 11 unknowns are **`rustsat-batsat` SAT-solver timeouts** on multiplier-heavy
  instances (`brummayerbiere3 mulhs08/16/32/64`, `calypto`, `wienand-cav2008
  commute08/16`, `stp_samples`), with small-to-mid CNFs (2.7k–200k clauses) —
  i.e. **SAT time, not encoding, dominates**. Crucially, CNF preprocessing
  (subsumption T1.1.1 + bounded variable elimination T1.1.2) is **already wired**
  into the `sat-bv` path (`sat_bv_backend.rs`), and these still time out — so the
  next real perf lever is **SAT-solving power** (the custom CDCL core, ADR-0002, +
  multiplier-aware inprocessing), whose priority the methodology gates on exactly
  this "SAT time dominates" measurement. That gate is now met on the curated slice.
- **2026-06-17** — **`(get-proof)` now serves THREE theories (QF_BV + EUF + LRA)**.
  `solve_smtlib_get_proof` tries, in order, the `QF_BV` bitblast driver, the EUF
  congruence emitter (`prove_qf_uf_unsat_alethe`), and the LRA Farkas emitter
  (`prove_lra_unsat_alethe`), returning the first that yields a proof its
  fragment-appropriate checker re-validates (`check_alethe` for BV/EUF,
  `check_alethe_lra` for LRA). So a standard SMT-LIB `(get-proof)` now returns a
  checkable Alethe certificate for bit-vector, uninterpreted-function, AND
  linear-real-arithmetic `unsat`s — the three externally-Carcara-validated proof
  families, unified behind one front-door call. `Ok(None)` only when no supported
  fragment can prove it (e.g. an unsat needing shift semantics: `a=1 ∧ a≪1=0`).
  5 tests (BV/EUF/LRA proofs + sat→None + shift-semantics→None).
- **2026-06-17** — **`(get-proof)` in the SMT-LIB front door (P4.4 + proof surface)**.
  New `solve_smtlib_get_proof(input, config) -> Result<Option<String>, SolverError>`:
  parses a script, and when the assertions are `unsat` in the QF_BV Alethe fragment,
  returns the textual Alethe proof (`bitblast_*` → CNF-intro → resolution to `(cl)`),
  re-validated by `check_alethe` before return; `Ok(None)` for sat/unknown or
  out-of-fragment (shifts/div/rem, non-QF_BV). The parser now recognizes-and-ignores
  the `(get-proof)` command (was rejected). This is the user-facing z3-parity entry
  point for the whole session's proof machinery — a standard SMT-LIB `(get-proof)`
  now yields a Carcara-and-self-checkable certificate. 3 tests (checkable proof, sat
  → None, shift → None). Next: shift/div-rem `hole`+miter; then P3.5/P3.6.
- **2026-06-17** — **QF_BV Alethe proof wired into the evidence pipeline (first-class
  self-checking output)**. New `Evidence::UnsatAletheProof(Vec<AletheCommand>)` whose
  `check` route is `check_alethe` (internal re-validation). `produce_qf_bv_evidence`
  now, on the `>20`-bit `unsat` path that previously emitted plain DRAT (bit-blast
  *trusted*, `BitBlast=false`), first tries `prove_qf_bv_unsat_alethe` and — if it
  returns a proof that re-checks — emits the Alethe certificate with **`BitBlast`,
  `Tseitin`, `SatRefutation` all CERTIFIED** (the `bitblast_*` steps check the
  reduction itself, closing the bit-blast trust hole on that route). Precedence:
  term-level enumeration (≤20 bits, trusts only the evaluator) > Alethe proof >
  plain DRAT (out-of-fragment fallback unchanged). A 24-bit in-fragment `unsat`
  (`(bvult a b)∧(bvult b c)∧(bvult c a)`) now carries an Alethe proof that re-checks
  `Ok(true)`; a `bvshl` instance still falls back to DRAT. 20 evidence tests green.
  **The whole session's QF_BV proof machinery is now a product output**, dual-checkable
  (Carcara external + `check_alethe` internal). Next: shift/div-rem `hole`+miter;
  then the P3.5 reductions (arrays/functions/int-blasting) and P3.6 Lean kernel.
- **2026-06-17** — **axeyum SELF-CHECKS its own full QF_BV proofs (internal checker
  complete)**. Ported the `bitblast_*` reconstructions (all 17: var/const/not/
  and/or/xor/xnor/add/neg/**mult**/ult/slt/equal/comp/extract/concat/sign_extend) and
  the `and` clausification into `check_alethe`, mirroring `bitblast_alethe.rs` /
  Carcara's `bitvectors.rs` (`build_term_vec` over `AletheTerm`, width recovered from
  `@bbterm` arity / max `@bit_of` index). **`check_alethe(prove_qf_bv_unsat_alethe(…))
  == Ok(true)` for ALL 9 driver instances** (eq+ult, eq+neq, ult-cycle, slt, +
  bitwise/arith/nested compound) — new `qfbv_self_check.rs`. So a QF_BV `unsat` proof
  is now validated by **both** the external Carcara binary AND axeyum's own in-tree
  checker (no external dependency). One soundness-critical refinement: the resolution
  entailment mapping (`cnf_lit`/`register_atom`) now parity-folds leading syntactic
  `(not …)` so `(not φ)`-as-atom and `φ`-negated normalize identically (a genuine
  logical equivalence, still anchored by the DRAT re-check; all rejection tests hold).
  116 cnf-alethe tests + 9 self-check tests green. **The QF_BV proof system is now
  dual-checkable end-to-end.** Next: shift/div-rem via `hole`+miter for full QF_BV;
  wire the driver into the evidence pipeline (now that an internal checker exists).
- **2026-06-17** — **`check_alethe` gains the Boolean CNF-introduction rules**
  (`equiv1`/`equiv2`/`not_equiv1`/`not_equiv2`, `equiv_pos1/2`, `equiv_neg1/2`,
  `xor_pos1/2`, `xor_neg1/2`) — the Tseitin tautologies axeyum's QF_BV driver emits,
  transcribed literal-for-literal from Carcara's `tautology.rs` (polarities/order
  strict). With the `refl`/`symm`/`trans`/`cong` family from the previous commit,
  axeyum's own checker now validates the **Boolean layer** of its QF_BV proofs
  internally; only `bitblast_*` (BV reconstructions) and the `and` clausification
  remain to port for full self-checking (the latter deferred: a structural `and`
  would flip an existing `UnsupportedRule` test, so it lands with that test update).
  12 new rules, each with positive + rejection tests, + 2 end-to-end Boolean
  refutations to `(cl)`. 105 cnf-alethe tests green. **Next: port `bitblast_*` (+ the
  `and` clausification) into `check_alethe` → axeyum self-checks full QF_BV proofs.**
- **2026-06-17** — **`check_alethe` gains the general equality rules
  `refl`/`symm`/`trans`/`cong`**. axeyum's OWN Alethe checker now structurally
  verifies reflexivity, symmetry, transitivity chains, and congruence (matching
  Carcara's `reflexivity`/`extras`/`transitivity`/`congruence` rules: `trans` by
  premise adjacency, `cong` by one-premise-per-differing-argument-position over a
  shared `App`/`Indexed` head + arity). This is the step toward axeyum checking its
  *own* QF_BV bitblast proofs internally (currently only Carcara can) — `cong`/`trans`
  are exactly the bridge's reduction rules — and it strengthens EUF proof checking
  too. Premises must be unit positive `(= a b)` clauses; rejects head/arity mismatch,
  broken chains, unjustified positions. Dispatch refactored into
  `check_structural_rule` (behavior-preserving, to stay under the clippy line cap).
  4 new tests + an end-to-end `cong`+`trans`→`(cl)` refutation; all 91 cnf-alethe
  tests green. **Remaining for internal QF_BV checking: the `bitblast_*` rules in
  `check_alethe` (port Carcara's reconstructions).**
- **2026-06-17** — **QF_BV proof driver extended to COMPOUND terms (Carcara-`valid`)**.
  `prove_qf_bv_unsat_alethe` now reduces predicates over compound bit-vector operands
  — bitwise, arithmetic (`bvadd`/`bvneg`/`bvmul`), `bvcomp`, structural
  (`extract`/`concat`/`sign_extend`) — **nested to arbitrary depth, shared-DAG
  subterms bit-blasted once**. The uniform front-end (`BbReducer`): bottom-up, every
  term gets an `@bbterm`-form equality via `cong` (over children's equalities) +
  `bitblast_<op>` (over the `@bbterm`-form children) + `trans`; predicates then
  `cong`→`bitblast_<pred>`→`trans` to the bit-level Boolean, feeding the unchanged v1
  Tseitin+LRAT refutation. Factored `bitblast_op_step` to emit a gadget over already-
  rendered operands; switched the bitwise/`bvnot`/`bvxnor`/`extract` arms to
  `build_term_vec` (correct for `@bbterm`-form children; no-op for the IR path). **5
  compound unsat instances Carcara-`valid`** incl. nested `(bvand (bvor a b) c)` and
  arithmetic `(bvadd a b)` conflicts; `None` for shift/div subterms (out of fragment).
  Now `None` only for shifts, div/rem, zero_extend, rotates, `bvsub`/`bvnand`/`bvnor`.
  **Next: shift/div-rem via `hole` + the in-house miter side-cert → full QF_BV.**
- **2026-06-17** — **`prove_qf_bv_unsat_alethe` driver — first AUTOMATED full QF_BV
  `unsat` proof, Carcara-`valid` (T3.3 capstone, v1 fragment)**. New
  `qfbv_alethe.rs`: given QF_BV assertions, confirms `unsat` (SAT-BV path) then emits
  a complete Alethe proof an external checker accepts — no hand-construction. v1
  fragment: predicates `=`/`bvult`/`bvslt` and their negations over bit-vector
  **variables/constants** (any width; compound subterms → `None`, a later increment
  via the validated `cong`/`trans` path). Pipeline: `bitblast_step` →
  `equiv1`/`equiv2`+`resolution` (Boolean form) → hand-rolled Tseitin CNF-introduction
  (each Boolean gate as its own variable, justified by `and_pos`/`and_neg`/`or_pos`/
  `or_neg`/`equiv_pos*`/`equiv_neg*`/`xor_*`) → the in-tree `solve_with_drat_proof` →
  LRAT replayed as Alethe `resolution` to `(cl)`. **4 distinct unsat instances are
  Carcara-`valid`** (incl. a 42-step `(bvult a b) ∧ (bvult b a)` nested-ladder
  refutation), + `None` for sat and for compound-term inputs. Deterministic
  (BTreeMap/insertion-ordered). **This is the first time axeyum AUTOMATICALLY produces
  a complete, externally-checkable QF_BV `unsat` certificate.** Next: extend to
  compound terms (`cong`/`trans`, mechanism already validated) + the
  shift/div-rem `hole`s backed by the miter cert. A predicate over a *compound* BV term (`(bvand a a)` inside
  `(= (bvand a a) a)`) does not project compound bits directly, and Carcara has NO
  `((_ @bit_of i) (@bbterm …))` reduction rule (`refl`/`all_simplify` both reject it).
  The mechanism, now validated end-to-end: bitblast each operand bottom-up, **`cong`**
  to substitute the `@bbterm` forms into the predicate, **`trans`** + `bitblast_equal`
  to the bit-level Boolean, then `equiv*`/`not_equiv*`/`and`/`and_pos`/`and_neg` +
  `resolution` to `(cl)`. Locked in as `full_qf_bv_compound_term_proof_is_accepted_by_carcara`
  (the `bitblast_and`/`bitblast_var` steps from the production emitter). **Every bridge
  rule pattern the general QF_BV driver needs is now empirically pinned against the
  binary** — both variable and compound cases. **Next: the general
  `prove_qf_bv_unsat_alethe` driver (bottom-up term bitblast + cong/trans reduction +
  Tseitin-of-B with CNF-intro + the SAT refutation).**
- **2026-06-17** — **First FULL QF_BV `unsat` proof is Carcara-`valid` end-to-end
  (T3.3 bridge validated)**. Hand-validated against the binary, then locked in as a
  committed regression test (`full_qf_bv_unsat_proof_is_accepted_by_carcara`): for
  `(= a b) ∧ (bvult a b)` (1-bit), the proof composes the **production
  `bitblast_step` emitter** (the `bitblast_equal`/`bitblast_ult` steps) with the
  bridge — `equiv1` + `resolution` to derive each assertion's Boolean form, then
  CNF-introduction (`and` with an `:args` conjunct index; `equiv2`) + `resolution`
  to the empty clause `(cl)`. **Carcara `valid`.** This resolves the last unknowns of
  the bridge (the exact rule inventory + that `and` needs `:args (i)`). Remaining to
  *automate* a general QF_BV proof: a Tseitin encoder turning an arbitrary
  bitblasted Boolean `B` into clauses with CNF-intro justifications, wired over the
  already-valid `lrat_to_alethe` resolution layer. **Next: the general
  `prove_qf_bv_unsat_alethe` driver (Tseitin-of-B + the SAT refutation bridge).**
- **2026-06-17** — **T3.3.1 step 2 complete: bitblast emitter covers Carcara's
  entire non-hole QF_BV operator set**. Added `bvmul` (shift-add multiplier,
  transcribed from Carcara's `shift_add_multiplier` — correct on the first run incl.
  width-1, width≥2, and n-ary left-fold), `bvextract`/`bvconcat`/`bvsign_extend`
  (the structural ops; extract/sign_extend use the `Indexed` LHS, concat is
  low-arg-bits-first). One oracle-forced fix: `sign_extend` with `i==0` is the plain
  `(= ((_ sign_extend 0) x) x)` (Carcara `assert_eq(x,res)`), not a `@bbterm`.
  32 cross-check cases, all Carcara rule-accepted. **Every QF_BV operator Carcara has
  a structural `bitblast_*` rule for is now emitted and empirically validated.** Still
  `None` (the Carcara *holes*): shifts (`bvshl`/`bvlshr`/`bvashr`), div/rem
  (`bvudiv`/`bvurem`/`bvsdiv`/…), zero_extend, rotates — these get `hole` + the
  in-house miter side-cert in a later increment. **Next: the predicate-bitblast +
  Tseitin-CNF bridge to compose these definitional steps into a full QF_BV `unsat`
  proof closing to `(cl)` via the Carcara-valid `lrat_to_alethe` resolution layer.**
- **2026-06-17** — **T3.3.1 step 2 (arithmetic + comparison): bitblast emitter
  extended**. `bitblast_step` now also emits Carcara-valid steps for `bvadd`
  (ripple-carry, n-ary left-fold), `bvneg` (two's-complement adder with verbatim
  `false`/`true` carry-ins), `bvult`/`bvslt` (the comparison ladders, slt with its
  sign-bit final step + width-1 special case), BV `=` (`bitblast_equal`), and
  `bvcomp`. This added the **two further output shapes** beyond the bitwise
  `(= t (@bbterm …))`: predicate ops conclude `(= <pred> <bool>)` (no `@bbterm`),
  and `bvcomp` wraps its single Bool in `@bbterm`. **All six Carcara rule-accepted
  on the first run** (gated per-operator tests; shapes transcribed directly from
  `bitvectors.rs`). 25 cross-check cases total. Still `None` (next increments):
  `bvmul` (shift-add multiplier), structural ops (extract/concat/sign_extend),
  shifts, div/rem. **Next: `bvmul`, then the predicate-bitblast + Tseitin-CNF bridge
  to close a full QF_BV refutation to `(cl)`.**
- **2026-06-16** — **T3.3.1 step 2 (first slice): per-operator bitblast emitter
  (bitwise fragment)**. New `axeyum_solver::bitblast_step(arena, term, id)` emits the
  definitional `(= <T> (@bbterm b0…b_{n-1})) :rule bitblast_<op>` step for the
  bitwise QF_BV fragment — `var`, `const`, `bvnot`, `bvand`, `bvor`, `bvxor`,
  `bvxnor` — building each bit LSB-first via `(_ @bit_of i)` projections exactly as
  Carcara reconstructs (left-fold for n-ary and/or/xor; `(= a_i b_i)` for xnor;
  `true`/`false` per const bit). **All seven operators are Carcara rule-accepted**
  (gated tests: emitted step parses and the `bitblast_*` rule checks — only the
  empty-clause conclusion is absent, since a lone definitional step is not a
  refutation). Every shape matched the binary on the first run (derived from
  `bitvectors.rs`). `bv_term_to_alethe` renders BV terms to matching SMT-LIB syntax
  (`#b…` consts, `bvand`/… heads); anything outside the fragment → `None`. 6 unit
  tests + 7 gated carcara tests. **Next: arithmetic/comparison ops (`bvadd`/`bvmult`/
  `bvult`/`bitblast_equal`), then the predicate-bitblast + Tseitin-CNF bridge to
  close a full QF_BV refutation to `(cl)`.**
- **2026-06-16** — **T3.3.1 step 1: `AletheTerm` indexed-operator IR extension**.
  Added `AletheTerm::Indexed { op, indices: Vec<i128>, args }` so SMT-LIB indexed
  applications like `((_ @bit_of 0) x)` (and bare `(_ @bit_of 1)`) are first-class —
  the bounded prerequisite for the per-operator `bitblast_*` emitter (the old
  `App(String, …)` head + atom-only parser couldn't represent a list-headed
  application). `key`/`write`/`parse` handle applied vs bare forms with exact
  round-trip; an `Indexed` term is an opaque atom to the theory rules (the only
  match sites needing an arm were `real_term`/`int_term` in `alethe_lra.rs` →
  `None`). Purely additive: existing `Const`/`App` output byte-identical, all ~82
  cnf tests + EUF/LRA/resolution emission unchanged. **A gated Carcara test confirms
  the IR renders exactly the syntax Carcara accepts**: a `bitblast_var` step built
  via the IR + `write_alethe` parses and the rule checks (`!parser error` &&
  "does not conclude empty clause"). 4 new IR tests + 1 carcara test (10 cross-check
  total). **Next: T3.3.1 step 2 — per-operator bitblast emitter from `axeyum-bv`.**
- **2026-06-16** — **QF_BV bitblast→Carcara contract reverse-engineered & recorded
  (T3.3.1 design)**. Empirically confirmed against the built Carcara binary the
  exact shape it requires for per-operator `bitblast_*` steps: the `@bbterm`
  operator + indexed `(_ @bit_of i)` bit-extraction (**spelling is `@bit_of`, not
  `@bit`**), e.g. `bitblast_var` accepts
  `(= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))` — this **parses and checks
  valid** (a lone step only lacks the empty-clause conclusion). Recorded the full
  rule-name set and the L-sized implementation body in
  `docs/research/07-verification/scalable-bitblast-certification.md`: (1) extend
  `AletheTerm` to represent the indexed `(_ @bit_of i)` head (parse/write/`key`
  round-trip) — the current `App(String, …)` can't; (2) per-operator emitter from
  `axeyum-bv`'s lowering, div/rem/shift as `hole` + miter side-cert; (3) bridge via
  Tseitin CNF rules to the already-Carcara-valid `lrat_to_alethe` resolution layer.
  This is the external-checker analogue of the in-house miter certificate (path B);
  no code emitted this turn — deliberately scoped as design so the L-task starts
  correct. **Next action: T3.3.1 step 1 — the `AletheTerm` indexed-op IR extension.**
- **2026-06-16** — **Resolution/clausal layer now Carcara-`valid` (T3.3.3)** — the
  Boolean-refutation rung of a full QF_BV proof. A CNF UNSAT goes CDCL → DRAT →
  LRAT → Alethe (`lrat_to_alethe`) and is now accepted end-to-end by Carcara
  against the asserted input clauses. The cross-check surfaced **two latent bugs
  our lenient `check_alethe` masked**, now fixed in `lrat_to_alethe`: (1) command
  ids were bare numerals (`1`, `2`) — invalid Alethe symbols; now prefixed
  (`a{n}`/`t{n}`); (2) an `assume (or φ…)` introduces the disjunction as a *unit*
  clause, not the clause `(cl φ…)` — each multi-literal input clause now gets an
  explicit `:rule or` unpacking step before resolution consumes it. `check_alethe`
  learned the `or` rule (entailment-checked, like resolution). All `assume`s emit
  before steps (no checker warnings). 82 cnf tests + 9 cross-check cases green.
  This is the third externally-validated proof family (EUF, LRA, now clausal
  resolution) and the closing step a full QF_BV bitblast proof will reuse.
- **2026-06-16** — **LRA Carcara cross-check now covers equality assertions**.
  `FarkasCertificate` gained a `pub origins: Vec<usize>` field (`origins[i]` = the
  source assertion index of atom `i`; an equality contributes two atoms sharing one
  origin). `farkas_args` now groups multipliers by origin instead of assuming a 1:1
  atom↔assertion map: a single-atom assertion (inequality) keeps its multiplier
  (byte-identical output); a two-atom equality `a=b` emits the **signed** coefficient
  `m1−m0` (confirmed sign against Carcara — the mixed equality+inequality case
  disambiguates the global sign), rendered with negatives as `(- n)` / `(- (/ p.0
  q.0))`. Orientation is robust (`is_negation_of` verifies the two atoms are exact
  negatives before trusting push order, else bails to no-args). **Three new
  equality refutations pass Carcara** (`x=1∧x=2` → `((- 1) 1)`; mixed
  equality+inequality; coefficient-bearing equality). 8 cross-check cases total; the
  inequality-only fragment is unchanged. Remaining LRA gap: assertions splitting into
  >2 atoms (conjunctions) still emit no args.
- **2026-06-16** — **LRA `la_generic` proofs now Carcara-`valid` (Farkas `:args`)**.
  The Alethe `Step` IR gained an `args: Vec<AletheTerm>` field (parse + write
  round-trip; emitted after `:premises`, only when non-empty so all ~80 existing
  cnf-alethe tests and EUF/LIA emission stay byte-identical).
  `prove_lra_unsat_alethe` now attaches one Farkas coefficient per clause literal,
  derived from `lra_farkas_certificate` (mapped 1:1 to assertions; equality/`and`
  assertions that split into two bounds emit no args and stay axeyum-checked-only).
  Coefficients render as bare integer numerals or `(/ p.0 q.0)` reals (verified
  against Carcara's `as_fraction`). **Three diverse LRA refutations now pass Carcara
  end-to-end** (unit `(1 1)`, non-unit `(1 2)`, multi-variable `(1 1 1)`) — LRA
  joins EUF as an externally-validated proof family. Carcara re-derives the
  contradiction from the args, so `valid` is the soundness oracle, not the
  coefficients themselves.
- **2026-06-16** — **Carcara third-party cross-check harness landed**
  (`crates/axeyum-solver/tests/carcara_crosscheck.rs`, plan task T3.3.5). axeyum's
  emitted Alethe proofs are now validated by the **independent Rust Carcara
  checker** (shares none of our code), not just our own `check_alethe`: the proof
  is serialized via `write_alethe` + matching `.smt2` via `write_script`, handed to
  `carcara check`. **EUF transitivity and congruence proofs both return `valid`**
  end-to-end. The test runtime-skips (prints a note, passes) when the Carcara
  binary is absent, so CI stays green; build it via
  `cargo build --release -p carcara-cli` in `references/carcara` (override the
  pinned toolchain with `RUSTUP_TOOLCHAIN=…`) or set `AXEYUM_CARCARA_BIN`.
  **Cross-check findings recorded as the next P3.3 tasks:** (1) our `la_generic`
  (LRA) step is rejected by Carcara — it requires the Farkas coefficient `:args`
  (one rational per clause literal); we already compute these
  (`lra_farkas_certificate`) but the Alethe `Step` IR has no `:args` field yet, so
  adding it + emitting the multipliers is the next increment; (2) `lia_generic` is
  a *Carcara hole* (unimplemented there) — Carcara reports `holey`, so the integer
  arithmetic rung needs either an int→real reduction proof or to stay
  axeyum-checked-only. EUF is the first proof family externally validated.
- **2026-06-16** — **`lia_generic` integer Alethe checking + emission**
  (`prove_lia_unsat_alethe`, exported). Integer counterpart to `la_generic`:
  the `la_generic_check` dispatch gained a `lia_generic` arm decided by the
  integer-complete `check_with_lia_simplex` (honoring integrality), plus an int
  parser (constant-factor-guarded `*`, plain-`i128` numerals) and an emitter
  self-validated by `check_alethe_lra`. A dedicated test pins the integer/real
  distinction: `(cl (<= x 0) (>= x 1))` is accepted by `lia_generic`, rejected
  by `la_generic`. 4 new tests; `just check` green.
- **2026-06-16** — **P1.5 online decider wired as the QF_UF fast path** (pending
  commit). `auto::check_auto_dispatch` now tries `solve_qf_uf_online` (online
  DPLL(T) on the backtrackable e-graph) **before** the offline `check_qf_uf`; on
  `Unknown` it falls through to the offline enumeration, then bit-blasting — so the
  change is zero-risk (unknown-safe backstop) and only ever fast-paths a sound
  answer. Full solver suite (incl. functions/aufbv/function_scenarios) green: no
  regression.
- **2026-06-16** — **P1.5 online DPLL(T) decision procedure** (commit 8bbdb9d).
  `solve_qf_uf_online`: extends the refutation engine to a full decider —
  `Unsat`/`Sat(model)`/`Unknown`. On a theory-consistent total assignment it builds
  a model from the e-graph classes (`EufTheory::model`) and **replays it against the
  original assertions** (the soundness gate: a non-replaying model → `Unknown`, never
  a wrong `sat`); no equality atoms / un-encodable structure → `Unknown` (same
  conservative boundary as the offline `check_qf_uf`). `prove_unsat_qf_uf_online` now
  delegates to it. 3 tests incl. a **400-formula differential vs `check_qf_uf`**
  (no Sat/Unsat clash where both decide) + a replay-checked sat model. The online
  QF_UF *decision procedure* on one backtrackable e-graph is complete.
- **2026-06-16** — **P1.5 online DPLL(T) refutation engine** (commit 223230b).
  `prove_unsat_qf_uf_online`: a self-contained online DPLL(T) for QF_UF — Tseitin
  CNF of the Boolean skeleton (and/or/not/xor/implies/ite gates; un-encodable
  structure → sound give-up) driving the online `EufTheory`. Interleaves Boolean
  unit propagation with `EufTheory::propagate`, mirrors eq-atom assignments via
  `assert` (theory `push` per decision, `pop` per backtrack — lockstep), learns
  `¬⋀core` on theory conflicts, chronological backtracking. Returns `true` only at
  a root-level conflict (sound UNSAT). **Differentially validated vs the offline
  `prove_unsat_lazy` on 500 random QF_UF formulas (exact agreement) + 4 crafted
  cases** (disjunction, transitivity, congruence, a SAT case). This is the *online
  search* atop the online theory — the offline SAT-enumeration loop replaced by one
  incremental backtrackable e-graph. (Implemented by a sub-agent; reviewed in full —
  Tseitin gates are equivalence-correct, the UNSAT verdict is sound, push/pop stays
  balanced — and the differential count was raised 50→500.)
- **2026-06-16** — **P1.5 online theory propagation (`EufTheory::propagate`)**
  (commit a3cea13). Extends the online theory with sound EUF propagation: the
  unassigned equality atoms whose sides are already congruent, each entailed `true`
  with the asserted equalities that force it (`TheoryProp{lit, reason}`).
  Assigned-state is now tracked and backtracked in lockstep (per-`push`
  `(diseqs, assigned_log)` markers), so entailments retract on `pop`. 2 added tests
  (transitivity+congruence propagation with reasons; retraction on backtrack).
  The online theory now has the full assert/propagate/explain/backtrack surface a
  CDCL(T) loop drives.
- **2026-06-16** — **P1.5 online `TheorySolver` trait + `EufTheory`** (commit afec596).
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
