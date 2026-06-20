# Codex Review Diary - 2026-06-20

This is a chronological working log for the project review requested on
2026-06-20. It records what was inspected, what was learned, and what still
needed follow-up at each step.

## Step 1 - Session protocol and status files

- Read `PLAN.md` first, per repository protocol.
- `PLAN.md` now delegates mutable session state to `STATUS.md`; this differs
  from the older AGENTS note that says `PLAN.md` itself is the only mutable
  session-state file.
- The current project identity is still "untrusted fast search, trusted small
  checking", with explicit Z3-performance and Lean-grade proof-checking goals.
- `STATUS.md` records a very active codebase: broad arithmetic, quantifier,
  proof, benchmark, FP/string/datatype, Lean-kernel, and robustness work are
  already present. The status text is optimistic and very detailed, but it also
  names hard remaining keystones: stronger word-level reduction, competitive
  SAT/CDCL, general quantifiers/MBQI, NRA/CAD with algebraic witnesses, and
  certifying the remaining trusted reductions.

## Step 2 - Roadmap and decision context

- Read the older research roadmap, foundational DAG, research-question
  register, and ADR index.
- The older phase roadmap is still useful for contracts, but current work has
  advanced far past Phase 5 into many "horizon" areas.
- The ADR index contains 37 accepted ADRs, ending with ADR-0037 on prioritizing
  word-level reduction over a custom default SAT core for destination-2
  performance.
- The foundational DAG remains the right audit lens: every public operator,
  rewrite, encoding, backend result, and theory fragment needs semantics,
  lift/projection, replay/checking, and benchmark evidence.

## Step 3 - Workspace and artifact inventory

- The workspace has 13 crates: IR, query, rewrite, AIG, BV lowering, CNF/SAT,
  solver, SMT-LIB, benchmark harness, scenarios, FP, e-graph, and Lean kernel.
- The workspace hard constraints are encoded in `Cargo.toml`: edition 2024,
  MSRV 1.85, resolver 3, `unsafe_code = deny`, and Z3 only as an optional
  feature-gated dependency.
- Rust code under `crates/` is about 122k lines. The largest centers of gravity
  are `axeyum-solver`, `axeyum-cnf`, `axeyum-fp`, and proof reconstruction /
  Lean-kernel code.
- There are 107 integration test files under crate `tests/` directories, with
  most breadth concentrated in `axeyum-solver/tests`.
- `bench-results/baselines/` contains committed versioned artifacts for curated
  QF_BV, public p4dfa QF_BV, replay refinement, lazy BV diagnostics, and
  layer-attribution runs.
- `corpus/public` is absent in this checkout, so public benchmark artifacts can
  be inspected but full public reruns would require fetching the corpus. The
  committed curated and micro corpora are present.

## Step 4 - Core API and model representation

- `axeyum-ir` has grown from Bool/BV into arrays, Int, Real, datatypes, Float,
  quantifiers, UF declarations, and wide bit-vectors.
- Term handles remain lifetime-free dense IDs, as required by the design.
- The evaluator is iterative for ordinary terms and is the semantic replay
  anchor for `sat` results.
- Quantifier evaluation is finite-domain only: Bool, BV/Float bit patterns up
  to 16 bits. Int/Real quantified evaluation returns
  `UnsupportedQuantifierDomain`.
- Function interpretations are still keyed by encoded `u128` scalar codes.
  `Value::scalar_code`, `FuncValue::constant`, and `Value::from_scalar_code`
  panic or decline for Int, Real, datatype, arrays, and wide-BV values. The
  solver compensates by returning `Unknown` for arithmetic-sorted UF `sat`
  model projection. This is sound but a real parity blocker.
- Exact rational and integer arithmetic deliberately panic on `i128` overflow
  in the ground evaluator. That is a bounded-reference stance, but it conflicts
  with the current "unknown, never crash" rule for adversarial modern inputs
  unless every public path guards it before evaluation.

## Step 5 - Solver front door and pure Rust BV path

- `solve()` is now a broad dispatcher: top-level existential skolemization,
  optional lazy BV, quantifier-free dispatch, multiple quantified arithmetic
  simplifiers/QE slices, finite-domain expansion, e-matching, and MBQI-like
  fallback.
- `check_auto()` defaults `preprocess` on. It applies canonicalization,
  propagation, `solve_eqs_bounded`, `elim_unconstrained`, and post-canonicalize,
  then reconstructs `sat` models and replays the original assertions.
- `SatBvBackend` has the right safety skeleton: unsupported preflight,
  DAG-node budgets, pre-lowering oversized-encoding refusal, AIG lowering,
  Tseitin CNF, optional bounded inprocessing, CNF budgets, SAT solve, CNF/AIG
  model lifting, model completion, and original-term replay.
- CNF inprocessing now composes simplification, BVE, and variable compaction.
  The model lift order is explicitly `compaction.expand` then
  `Reconstruction::extend`.
- A concrete assurance mismatch exists: with `SolverConfig::prove_unsat = true`,
  `SatBvBackend` asks the proof-producing SAT core to re-derive and check an
  `unsat`, but if the proof core returns `ResourceOut`, `verify_unsat_proof`
  returns `Ok(())`. That means an adapter `unsat` may still be returned without
  proof despite the config documentation saying it is independently re-derived
  and checked.

## Step 6 - SMT-LIB and capability surface

- The SMT-LIB parser is much broader than the crate-level docs say: it accepts
  datatypes, Int/Real/Float sorts, quantifiers, define-sort, objectives, many
  query/output commands, and incremental push/pop/check-sat sequences.
- Some accepted SMT-LIB commands are semantic no-ops in the command stream:
  `reset` and `reset-assertions` parse as one-token no-ops and are not represented
  in `ScriptCommand`, so `solve_smtlib_incremental` cannot implement their
  effects.
- `solve_smtlib` intentionally solves the flat assertion list and ignores push/pop
  scoping; `solve_smtlib_incremental` is the scoped route.
- The capability matrix is generated from `axeyum_solver::capabilities` and
  golden-tested, which is a strong anti-drift mechanism. The entries are useful
  but still optimistic in wording for some broad areas, especially strings,
  optimization, QF_LIA, and "QF_BV arbitrary width" relative to current public
  corpus performance and proof coverage.

## Step 7 - Benchmark evidence

- Inspected committed benchmark artifacts with a small JSON summary script.
- Latest public p4dfa QF_BV evidence:
  - eager `sat-bv`, 3s, 200k nodes / 2M vars / 5M clauses: 2/113 `sat`, 111
    `unknown`, zero disagreements and replay failures.
  - `sat-bv --preprocess`, same 3s budgets: 4/113 `sat`, 109 `unknown`, zero
    disagreements and replay failures.
  - `sat-bv --preprocess --inprocess`, same 3s budgets: 4/113 `sat`, 109
    `unknown`, modest PAR-2 improvement, zero disagreements and replay failures.
  - `sat-bv --preprocess`, 20s, 300k nodes / 3M vars / 8M clauses: 7/113 `sat`,
    106 `unknown`, zero disagreements and replay failures.
- Layer attribution on the 20s preprocessed run says SAT dominates decided
  instance time: about 98% of the measured decided-instance pipeline time is
  SAT solve time. That supports the status conclusion that remaining easy
  preprocessing has been largely exhausted for this slice.
- The artifacts are honest about the current gap: they demonstrate soundness
  and measurement discipline, not Z3 parity.

## Step 8 - Proof and evidence surface

- Inspected the evidence API, Alethe checker, DRAT/LRAT checkers, and the
  Lean-kernel crate.
- Evidence is now much broader than the old plan implies: BV bit-blast proof
  reconstruction, EUF/Ackermann certificates, array/datatype certificates,
  LIA/LRA Farkas-style certificates, quantifier-instantiation certificates,
  k-induction proofs, and trust-ledger provenance are all represented.
- This is a serious strength of the project. The implementation is not merely
  returning solver statuses; it is building an audit trail and checking many
  of the claims internally.
- The proof stack is still mixed-assurance. Some routes are zero-trust or
  Lean-kernel checked, some remain trusted reductions or custom checked rules,
  and the XOR/CDCL fallback explicitly carries a trusted hole for UNSAT.
- The Lean-kernel crate has moved beyond its crate-level documentation: the
  top comment still says WHNF, definitional equality, and type checking are
  absent, while the tests exercise those features. Documentation needs to catch
  up so the proof roadmap is not undersold or confusing.

## Step 9 - Targeted validation

I kept validation bounded because the machine was already at 92% disk usage
and the public SMT-LIB corpus is not present under `corpus/public`.

- `cargo fmt --all --check`: passed.
- `./scripts/check-links.sh`: passed (`all links ok`).
- `timeout 180 cargo test -p axeyum-ir --lib`: passed, 9 tests.
- `timeout 240 cargo test -p axeyum-solver --test capabilities`: passed, 2 tests.
- `timeout 240 cargo test -p axeyum-solver --test evidence`: passed, 24 tests.
- `timeout 300 cargo test -p axeyum-solver --test sat_bv`: passed, 22 tests.
- `timeout 300 cargo test -p axeyum-solver --test smtlib`: passed, 44 tests.
- `timeout 300 cargo test -p axeyum-cnf --lib`: passed, 242 tests.
- `timeout 180 cargo test -p axeyum-lean-kernel --lib`: passed, 126 tests.
- `timeout 300 cargo test -p axeyum-solver --lib`: passed, 331 tests.
- `timeout 300 cargo run -p axeyum-bench -- corpus/micro --backend sat-bv
  --timeout-ms 1000 --out /tmp/axeyum-review-bench-micro-sat-bv.json`: passed,
  3 files, 2 sat, 1 unsat, 0 unknown, 0 disagreements, 0 replay failures.

Validation covered a substantial slice of the project, but not the full
workspace gate (`just check`) and not the public corpus reruns. The report
therefore treats the committed benchmark artifacts as evidence and calls out
the absent public corpus as a reproducibility gap for this checkout.

## Step 10 - Review synthesis before writing the report

- This is now a large solver/proof research codebase: 13 workspace crates and
  about 151k Rust source lines under `crates/`.
- The architecture is directionally coherent with the stated identity:
  untrusted search, replayed models, proof/certificate routes, explicit budgets,
  and deterministic artifacts.
- The strongest engineering practices I saw are the replay discipline for SAT
  models, explicit unknowns for many resource or support gaps, deterministic
  benchmark artifacts, and growing proof reconstruction.
- The largest risks are not cosmetic. They are exact-value representation
  limits, panic-on-overflow evaluator paths, a proof-assurance mismatch in
  `prove_unsat`, optimistic support wording, and the sheer breadth of the
  `solve()` dispatcher.
- The Z3/Lean parity goal is realistic only as a long-term program with
  fragment-by-fragment milestones. The current project is a promising research
  stack with good assurance instincts; it is not close to general Z3 parity or
  full Lean-level proof coverage yet.
