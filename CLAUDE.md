# CLAUDE.md

Guidance for Claude Code (and other agents) working in this repository.

## What This Project Is

Axeyum is a Rust-first automated reasoning stack: typed term IR → rewriting →
query planning → solver backends (native SMT oracles + a pure Rust
bit-blast-to-SAT path) → models, proofs, and checkable evidence. Identity in
one sentence: **untrusted fast search, trusted small checking.**

North star: a **complete framework for general reasoning, logic, and
proving** — the finite-domain core (SAT/QF_BV) is the foundation layer, and
the ladder continues through arithmetic, theory combination, quantifiers,
and proof production
([north-star note](docs/research/00-orientation/north-star.md)). Design
choices should not paint the IR, solver trait, or evidence formats into a
quantifier-free corner.

## The Flywheel — what the increments are for

Every task in this repository is one turn of a single cycle. Know which arrow
you are standing on:

```
        library (proved ℕ, ℤ, …)
             │  gives the solver facts to reason with
             ▼
        solver (30 logics, CAS, quantifiers)
             │  decides goals the library needs
             ▼
        reconstruction  →  kernel term  →  admitted, axiom-free
             │  becomes a library theorem
             └──────────────────────────────┐
                                            │
        the concept DAG and the fact ledger ┘  say what to prove next
```

A proof library is normally a one-way pipeline: people write proofs, a kernel
checks them. This one is a cycle, and that is the whole architectural bet.
**Every arrow already exists, and the cycle has closed end to end.** What it has
never been is *automatic*. Making it automatic is the point of the work — not
theorem count, not benchmark position. The argument, the measured production
rate, and the constraints on it are in
[`docs/formalized-math-2026-08/05-throughput.md`](docs/formalized-math-2026-08/05-throughput.md);
the three parallel roadmap strands live beside it.

The strategy layer above the flywheel is now decided and documented — read
these before framing any "how do we compare to Mathlib / Mathematica" work:

- [ADR-0601](docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)
  — autogenesis, the CAS, and the importer are producers behind ONE trust
  anchor (`Kernel::add_declaration`); CAS evidence must reconstruct or be
  visibly `cas-internal`; imports are labeled scaffolding, never headline.
- [ADR-0602](docs/research/09-decisions/adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md)
  — operations are retrospective receipts; dispatch requires a separate
  prospective producer contract with no `proved` field at all.
- [ADR-0603](docs/research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
  — a classical theorem lands as a graded statement family (general
  constructive form + boundary refutation + decidable-fragment exact form +
  labeled import), one fact per statement.
- [2026-08-27 architecture review](docs/research/11-design-review/2026-08-27-architecture-review.md)
  — the measured root causes: `creal.rs` fuses name registry, field
  struct, build ORDER and dispatch (441 fields, 364 linear `declare_*`
  calls) which is why phase-order bugs and helper duplication recur;
  the integral's mesh is INTERVAL-RELATIVE, which is why additivity was
  hard and why `riemannSum_split_exact` is free at mesh points; and the
  two design patterns lanes rediscover every time — **computed, not
  extracted** and the **two congruence regimes**. Read it before
  proposing a refactor or fighting a congruence obligation.
- [07-the-cost-model-and-pareto-position.md](docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  — tokens are capex, not opex: encoded strategies (producers) drive marginal
  cost per theorem toward CPU; the three gates (contracts, retrieval,
  sharding) each carry a running metric. Do not price future work at today's
  tokens-per-theorem constant, and do not claim coverage parity — the
  Pareto claim is per-statement dominance plus uncontested axes.

Two consequences that change how you work, not just how you feel about it:

- **The metric is the trusted base, not the output volume.** Assumptions
  remaining per prelude, and results the system established with nobody writing
  the proof. A referee checks both in one command; a competitor can inflate
  neither. Read them from the kernel, never from source text or a doc — see the
  inventory examples under Gotchas.
- **At N lanes the ledger IS the product, so a checker that cannot fail is worse
  than no checker.** It does not slow the flywheel; it makes it manufacture
  unfalsifiable claims at full speed. Audited 2026-08-15: **40 of 162 checker
  runs across 36 settled facts exit 0 on completion alone** — nothing in the
  command makes the exit status depend on what the run found — and that set
  included the inventory asserting axiom-freedom, this project's headline claim.
  So: when you attach evidence, make the exit status depend on the finding; when
  you touch a checker, delete one guard and require that **exactly one** test
  dies. Six of seven guards in one suite were removable with everything still
  green, because they all rejected through one shared check.

  **Re-measured 2026-08-25 over the whole ledger, and the picture is better —
  but check the METHOD before quoting either number, because the two
  measurements do not share a denominator.** Across 488 facts and 590
  `checker_command`s: 464 carry an explicitly discriminating shape (`grep -c`
  consuming the pipe and a tested count, `--require-axiom-free`,
  `--expect-axioms`, `--check`, `diff`), and the remaining 126 are
  `cargo test` / `cargo run` whose status depends on the suite passing.

  **Those 126 are NOT the failure mode**, and I nearly reported them as such.
  A `cargo test --test X` exits nonzero when a test fails, so it does depend on
  the finding — the real vacuity risk is a suite that compiles to ZERO tests
  behind a feature gate and prints `running 0 tests ... ok`. All 5 distinct
  `(crate, --test suite)` pairs the ledger names are UNGATED, verified by
  reading each file's head for `#![cfg(feature`, so none can pass vacuously
  that way. The lesson is the one this section already teaches, aimed at
  myself: a crude classifier that flags a whole shape is not a measurement.

## Working Stance — we ship toward Z3 + Lean parity

This is an ambitious, **achievable** build, and the job is to *complete it* — one
verifiable increment at a time, relentlessly. Adopt a builder's mentality:

- **There is always a next concrete task.** PLAN.md and `docs/plan/` decompose the
  whole goal into tracks → phases → tasks with paths, sizing, and exit criteria.
  When you finish one, pick the next and go. PLAN.md's standing rule is literal:
  **"We do not stop and we do not hand-wave; we advance the next task and record it."**
- **Big tasks get broken down, not deferred.** A "keystone" is not a reason to wait
  for "a future session" or "fresh context" — it's a signal to slice it into sound,
  bounded, testable pieces and land them one by one. Each slice that compiles, passes
  the gates, and adds real capability is progress. Ship it, then take the next slice.
- **Soundness is a method, not an excuse.** We never ship a wrong sat/unsat — and we
  achieve that by *conservative slicing + soundness-negative tests + independent
  re-validation + self-checking evidence*, NOT by avoiding hard work. "This is
  soundness-critical" means "test it harder," not "punt it."
- **Don't whine, don't stall, don't write essays about why something is hard.** Spend
  the words on the diff. Launch sub-agents for parallel/large work; review and
  re-validate what they produce; commit; continue.
- **Measure what matters.** Z3 parity is a *measured* claim — keep the head-to-head
  honest (Track 1, the public corpora). Lean parity is *every unsat/valid carries a
  machine-checkable proof*. Drive both fronts; record the pulse in **your lane's**
  `docs/plan/status/<lane>.md` and regenerate — PLAN.md is a generated view and
  you never edit it (Session Protocol, below).

Keep the queue framed as **active work**, never as an "exhausted frontier." If you
catch yourself concluding the work is done for now, you're wrong — re-read PLAN.md
and the strand that matches your work, and pick the next task.

## Session Protocol

1. Read [PLAN.md](PLAN.md) **first** — it carries current status, the next
   actions, and the resume protocol. It is the only file with mutable session
   state. **It is generated** (`python3 scripts/gen-plan.py`, gated by
   `--check`): you never edit it. Your lane's state lives in
   [`docs/plan/status/<lane>.md`](docs/plan/status/README.md); project-wide
   sections are in [`docs/plan/global/`](docs/plan/global/README.md).
2. Work against the current roadmap phase and its exit criteria:
   [docs/research/08-planning/roadmap.md](docs/research/08-planning/roadmap.md).
3. Before adding public operators, rewrites, encodings, backends, evidence
   artifacts, or logic fragments, check the foundational dependency DAG:
   [docs/research/08-planning/foundational-dag.md](docs/research/08-planning/foundational-dag.md).
4. Decisions are not made silently in code. Check
   [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md)
   and [docs/research/09-decisions/](docs/research/09-decisions/README.md);
   close questions with ADRs (template in the decisions README). The ADR
   **index is generated** (`python3 scripts/gen-adr-index.py`): write the ADR
   file, including its optional `Index-summary:` / `Index-status:` front
   matter, and regenerate. Never append an index row by hand.
5. Before ending a session: update **your lane's** `docs/plan/status/<lane>.md`
   — its status block and any landed-changes rows — then run
   `python3 scripts/gen-plan.py` and commit both it and `PLAN.md`. Touch
   `docs/plan/global/` only for a genuinely project-wide change (the ordered
   queue, the rules, the workstream table).

   These two files are generated because they were the repository's shared
   append points: `PLAN.md` was touched 67 times and the ADR index 60 times in
   24 hours by concurrent lanes on 2026-08-13/14, and four separate clobbering
   incidents lost real content in one day. Pathspec discipline does not help —
   it stops you sweeping a file you did not touch, not two lanes legitimately
   touching the same one. The general rule this instance teaches: **per-lane
   state and per-lane identity belong in per-lane paths or per-process
   environment, never in one file or one config key that every lane writes.**
   (Lane identity is `AXEYUM_AGENT` in your environment for exactly this
   reason — see `hooks/commit-msg`.)

## Commands

**These commands assume a gate-capable host.** They are not equally runnable
everywhere: measured 2026-08-16, `lean` and `just` existed on one fleet host of
five and `cargo-deny` on none, so an agent that runs `just check` on a host
lacking `just` silently falls back to the narrower `check.sh` and reports it as
the gate. The capability baseline, the provisioning script, and the map of which
gate needs which toolchain are in
[docs/contributor-guide/fleet-hosts.md](docs/contributor-guide/fleet-hosts.md).
Confirm the host before believing the gate.

```sh
just check          # the fullest aggregate gate (preferred)
just foundational-resources  # validates foundational atlas/example packs + generated dashboards
# NOT the same gate as `just check`, despite both files claiming to mirror each
# other. Measured 2026-08-14: `just check` ran 112 script steps, check.sh ran 61,
# and EACH was missing something the other had -- check.sh skipped the Lean axiom
# ledger (the SHA-256 binding of every prelude axiom type; axiom-freedom is the
# headline metric), while `just check` skipped check-gate-liveness.sh, the ratchet
# that detects gates which run zero tests. Both are narrower now but still differ.
# Treat `just check` as the gate and check.sh as the no-`just` fallback that may
# lag it; when a claim depends on a specific gate, run that gate by name.
# Full measurement: docs/refactor-2026-08/gate-divergence-2026-08-14.md
./scripts/check.sh  # fresh-machine fallback, NOT equivalent -- see above
python3 scripts/validate-facts.py  # the fact ledger: formal statement + status + evidence
just bench-micro    # committed SMT-LIB micro corpus through axeyum-bench
just bench-public-qfbv-sat-bv-compare  # Phase 5 public sat-bv vs Z3 slice
just bench-public-qfbv-sat-bv-guarded  # Phase 5 node/CNF guarded run
just bench-public-qfbv-sat-bv-replay-refine  # replay-checked query refinement
scripts/check-aggregate-scope.sh  # how far apart those two gates are, pinned
cargo fmt --all --check
# BOTH LINES BELOW CAN PASS OVER CODE THEY NEVER COMPILED. Cargo decides
# freshness by MTIME, so a source file OLDER than the cached artifact is
# invisible -- and `git archive HEAD | tar -x` (the snapshot build every lane is
# told to use) stamps every file with the COMMIT time, so re-extracting an
# EARLIER commit into a warm target dir (an A/B, a bisect) puts the content's
# clock behind the cache. Measured 2026-08-14:
#   touch -d 2020-01-01 examples/warny.rs  -> clippy -D warnings exits 0
#   touch -d 2020-01-01 src/lib.rs         -> `cargo test` prints "1 passed" for
#                                             a test that MUST fail
# Use the wrappers instead; they touch changed content first and then report how
# many targets/tests they actually examined:
#   scripts/check-clippy-complete.sh    scripts/check-workspace-tests.sh
# If you must run the bare form from a `git archive` snapshot, run
# `scripts/check-source-freshness.sh --gate <name> --touch` first, or extract
# with `tar --touch`. Controls: scripts/tests/test-gate-scope-controls.sh.
#
# DO NOT hand-roll the snapshot. `W=$(scripts/lane-snapshot.sh <ref>)` extracts to
# /data0 with `--touch` and an owner stamp, and prints only the path.
# `mktemp -d` + `git archive | tar -x` gets BOTH halves wrong: /tmp here is a 62 G
# **tmpfs (RAM)** -- measured 2026-08-15 at 81% full, Shmem 45.1 G of 123 G, with
# 9.3 GB of it abandoned axeyum snapshots, a standing contributor to OOM kills on
# this box -- and without `--touch` you get the stale-mtime trap above. Prose did
# not fix this: of ~60 `git archive` recipes in tracked files, ONE used --touch.
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
# PRE-MERGE GATE for any string-route change: the oracle-free :status corpus
# sweep (~6s). CI's copy of this caught a vacuous-sat harness hole two oracle
# fuzzes missed (f5b00c72) — after the SHA was already public. Related rule:
# string fuzz GENERATORS must cover the full SMT-LIB literal grammar,
# including \u{…}/\uXXXX escapes and >0xFF code points — every generator
# omitted escapes and a wrong-verdict class (ba0d9149) hid for weeks.
# `--features full` IS MANDATORY HERE. The suite is `#![cfg(feature = "full")]`
# (since 4464dae2, 2026-07-17), so WITHOUT it this command compiles an empty
# binary, prints "running 0 tests ... ok", and exits 0 — a green-looking gate
# that checks nothing. It was inert in `hooks/pre-push` for 15 days before this
# was noticed on 2026-08-01. Same trap on `--test online_string_front_door`,
# `--test word_first_fallback`, `--test qf_slia_fixed_splice`,
# `--test stoi_len_abstraction`. Always confirm a NONZERO test count.
cargo test -p axeyum-solver --features full --test corpus_regression
# PRE-MERGE GATE for any solver change: the FULL solver unit sweep (~30s). A
# wrong-unsat unit test shipped to main (52f3b1d1) because a lane ran targeted
# `--test <file>` + differential fuzzes but not `--lib` — the corpus sweep and
# fuzzes both miss soundness holes on shapes that are neither in the committed
# corpus nor generated by a fuzz. Both this and corpus_regression now run in
# the pre-push hook (hooks/pre-push).
cargo test --workspace --lib   # NOT -p axeyum-solver: the P0 defect lived in axeyum-rewrite
# ...but on DEFAULT features this runs 23 of axeyum-solver's 968 unit tests
# (measured 2026-08-01) — everything behind `#[cfg(feature = "full")]` is not
# compiled. Pair it with the `full` sweep, which is pure Rust (the C/C++ z3
# backend is a separate feature, so this keeps the no-C-dependency promise):
cargo test -p axeyum-solver --lib --features full
# ...BUT `--lib` IS NOT A SUFFICIENT PRE-MERGE GATE ON ITS OWN: it runs only unit
# tests compiled into lib targets and SKIPS every integration suite in tests/*.rs.
# Two front-door string tests stayed broken across several merges because every
# lane gated on `--lib` alone (2026-08-01); the aggregate gate caught them. For a
# parser / front-door / string-route change, add the affected suites explicitly
# (`--test online_string_front_door`, `--test word_first_fallback`,
# `--test qf_slia_fixed_splice`, `--test stoi_len_abstraction`) or just run
# `./scripts/check.sh`, which has now caught three classes of defect the
# per-crate gates missed.
# PRE-MERGE GATE for any LINEAR-ARITHMETIC change (simplex, LRA/LIA theory,
# difference logic): the differential fuzzes against the z3 oracle. These are the
# ONLY checks that compare our verdicts against an independent solver, and they
# compile to ZERO tests without `--features z3` — the same silent-inertness trap
# as the corpus sweep. Confirmed 2026-08-03: 0 tests without the feature, 5+1+1
# with it. `z3` is a C/C++ leaf dependency so it cannot be a default gate
# (ADR-0002), which is exactly why it has to be run deliberately.
cargo test -p axeyum-solver --features z3 --test qf_lra_differential_fuzz
cargo test -p axeyum-solver --features z3 --test simplex_lra_fallback_differential
cargo test -p axeyum-solver --features z3 --test qf_uflra_differential_fuzz
# PRE-MERGE GATE for any solver/decider/dispatch change: the capability
# ratchets (~60s when healthy). A 17-point nia_unsat frontier regression once
# shipped and needed an 829-commit bisect because only full sweeps ran this.
#
# `--features full` IS MANDATORY HERE TOO — and this very line lacked it until
# 2026-08-04, so the documented form of our capability ratchet printed
# "running 0 tests ... ok" and exited 0. `tests/progress_frontier.rs:75` is
# `#![cfg(feature = "full")]`. `scripts/check.sh` and the `justfile` always had
# the flag; only the copy agents are pointed at did not, and a NIA probe lane
# ran the inert form as its "gate passed" evidence. Confirm a NONZERO count (10).
#
# `--test-threads=1` serializes the suite against ITSELF and does nothing about
# the other lanes on the box, which is the contention that actually moves these
# numbers: same commit, same machine, 35 (load 34) / 39 (load 5.4) / 40 (idle).
# Each family now calibrates the machine before and after its sweep and scales
# the per-instance budget, prints `reference frame [family]: ...`, and marks a
# run NOT COMPARABLE (ratchet not enforced) or ADVISORY ONLY (do not raise a
# baseline from it). Read those two lines before believing a REGRESSION or
# committing a PROGRESS. Pinning to one core class helps a lot on a hybrid CPU
# (`taskset -c 0-7` here); unpinned, this sweep is 1.84x slower on the E-cores
# and the old fixed-budget gate reported a REGRESSION that never happened.
# docs/research/08-planning/frontier-ratchet-reference-frame.md
cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1
cargo doc --workspace --all-features --no-deps    # RUSTDOCFLAGS="-D warnings" in CI
cargo deny check                                  # needs cargo-deny installed
./scripts/check-links.sh                          # docs relative-link check (CI job)
# WebAssembly is a supported target (ADR-0017); the default library stack builds
# for browser and WASI. Native builds are unaffected (clock shim is wasm-only).
cargo build --target wasm32-unknown-unknown -p axeyum-solver
```

Local default toolchain may be nightly; CI runs stable plus an MSRV (1.88 —
let-chains are used workspace-wide) check. Edition 2024, resolver 3.

## Layout

- `crates/axeyum-ir` — sorts, terms, arena/interning, ground evaluator,
  LSB-first value/bit conversion helpers.
- `crates/axeyum-aig` — AIG circuit graph with deterministic structural
  hashing, evaluation, and ASCII AIGER debug export.
- `crates/axeyum-bv` — term-to-AIG bit lowering with explicit term-bit and
  symbol-input maps for the full scalar QF_BV operator set (bitwise, arithmetic
  incl. mul and signed/unsigned div/rem, shifts, comparisons, structural ops);
  one-shot `lower_terms` plus persistent `IncrementalLowering` (ADR-0009 st.2).
- `crates/axeyum-cnf` — simple Tseitin encoding from AIG, DIMACS I/O, CNF
  evaluation, BatSat-backed solving, CNF-variable-to-AIG replay maps, a warm
  `IncrementalSat` adapter (monotone clauses + native assumptions),
  `IncrementalCnf` (per-node Tseitin over the warm solver, ADR-0009), an
  independent DRAT UNSAT proof checker `check_drat` (RUP+RAT, ADR-0011), and a
  proof-producing CDCL SAT core `solve_with_drat_proof` (1-UIP conflict
  analysis + two-watched-literal propagation, emits DRAT, ADR-0012).
- `crates/axeyum-fp` — floating-point (IEEE 754) bit-vector formula builders
  (classification, comparison, abs/neg/min/max, arithmetic incl. rem/fma/sub,
  and int/real conversions) over the typed IR; the GPU/ML precisions are free
  from the generic `(exp_bits, sig_bits)` design (ADR-0023). Extracted from
  `axeyum-solver` so the SMT-LIB front-end can share it (depends only on
  `axeyum-ir`).
- `crates/axeyum-query` — query object: assertions, assumptions, scopes,
  stable labels.
- `crates/axeyum-rewrite` — rewrite manifest contracts, the first
  denotation-preserving canonicalizer, and `eliminate_arrays` (QF_ABV →
  QF_BV by read-over-write + Ackermann, ADR-0010).
- `crates/axeyum-solver` — backend trait, results, models, capabilities;
  default pure Rust SAT-backed BV backend (one-shot `SatBvBackend`, plus the
  warm `IncrementalBvSolver` with push/pop/assume, ADR-0009 st.2); the high-level
  `Solver` façade; `check_with_array_elimination` for QF_ABV (ADR-0010); native
  backends behind feature flags (`z3` is the oracle).
- `crates/axeyum-smtlib` — SMT-LIB benchmark-slice parser and
  sharing-preserving writer.
- `crates/axeyum-bench` — corpus benchmark harness with backend selection,
  PAR-2 scoring, model replay, and JSON artifacts; also the
  `scenario_pipeline_report` and `scenario_scaling` examples.
- `crates/axeyum-scenarios` — self-checking, oracle-free consumer workloads
  (SAT by concrete execution, UNSAT by bounded-verified identities) for testing
  and optimization (ADR-0008).
- `artifacts/facts/` — **the fact ledger**: one JSON file per mathematical
  proposition, schema in `artifacts/ontology/fact.schema.json`, gated by
  `scripts/validate-facts.py`. A fact is the only resource here that holds a
  formal statement **and** a status: a `claim`'s `statement` is prose and its
  `formal` is a CNF generator recipe, a kernel declaration exists only once
  proved, a curriculum node is a topic. So it is what the self-extension loop
  consumes — pick an `open` fact whose `depends_on` are established, dispatch
  `formal.statement`, reconstruct, attach evidence, flip the status, record the
  axiom footprint. Two status axes, deliberately: `epistemic_status` is what
  **we** established, `external_status` what mathematics knows. Their
  disagreement in our favour is a new result and the validator prints it.
  Semantic rules are enforced, not just structure (a `proved` fact with nothing
  `checked`, or an `open` one carrying evidence, fails).
- `docs/refactor-2026-08/`, `docs/mathematics-2026-08/`,
  `docs/formalized-math-2026-08/` — the three parallel roadmap strands
  (engineering architecture / mathematical capability / collecting and
  integrating formalized mathematics). Read the strand that matches your work
  before starting; they carry the reasoning PLAN.md's queue only summarizes.
- `docs/research/` — research notes; the design rationale for everything.
  Folder map in [docs/research/README.md](docs/research/README.md).
- `references/` — gitignored shallow clones of reference solvers/checkers;
  repopulate with `scripts/fetch-references.sh`. Read these when implementing
  (e.g. CaDiCaL for clause arenas, varisat for Rust CDCL + proof output).
- Crate split is deliberately minimal (ADR-0001): add crates only after a
  boundary is proven by use (`axeyum-smtlib` and `axeyum-bench` are such
  exercised boundaries; `axeyum-query` and `axeyum-rewrite` are the Phase 3
  contract boundaries accepted in ADR-0005; `axeyum-aig`, `axeyum-bv`, and
  `axeyum-cnf` are the Phase 4 circuit/lowering/CNF boundaries accepted in
  ADR-0006; `rustsat-batsat` is the first pure-Rust SAT adapter accepted in
  ADR-0007; `axeyum-scenarios` is the self-checking consumer-workload boundary
  accepted in ADR-0008).
- The pure Rust stack including a custom CDCL SAT core is the product; the
  Z3 oracle is bootstrap scaffolding with a planned demotion path
  (ADR-0002). Never expand reliance on linked solvers beyond
  backend/differential-oracle/CI-cross-check roles without a new ADR.

## Multi-agent hygiene (multiple agents share this checkout)

- **Pathspec-only commits, always:** `git add <files>` then
  `git commit -m … -- <files>`. A bare `git commit` sweeps OTHER agents'
  staged files from the shared index (it has happened; recovery cost real
  work). Verify every commit with `git show --stat`.
- **Pathspec is necessary, NOT sufficient — it does not protect a file two
  lanes are both editing.** `git add <file>` stages that file's entire
  *worktree* content, including another lane's uncommitted hunks in it. On
  2026-08-14 a correctly-pathspec'd commit swept another lane's in-progress
  `justfile` edit into itself: the fifth clobbering incident, and the first
  where the committer followed this rule exactly. Consequences were real —
  a step was attributed to the wrong lane, and `main` referenced a script
  three minutes before that script existed. So: before `git add`, run
  `git diff <file>` and confirm every hunk is yours. If it is not, you are
  sharing a file, which is the actual problem — say so and coordinate rather
  than committing around it.
- **A pathspec NARROWER than your change silently drops your own hunks —
  the opposite failure, and equally unguarded.** On 2026-08-14 a lane doing a
  staged refactor ran `clippy -D warnings` immediately before each commit and
  still shipped `ae589be97`, which **does not compile**: the gate ran against the
  *worktree* while the commit used a hand-written pathspec that omitted a
  one-line import fix in an already-committed file. Green gate, broken commit.
  Derive the pathspec from `git status`, never by hand, and if you must hand-write
  it, verify with `git stash -u && cargo check` — or simply accept that
  `git show --stat` tells you what you committed, not what you needed to commit.
  (That commit is still in history, repaired by the next one rather than rewritten:
  **a bisect crossing `ae589be97` will report a build failure unrelated to what it
  is bisecting.**)
- **NO FORM OF `git commit` IS SAFE FOR TWO LANES SHARING ONE INDEX — use a
  per-process index.** Measured 2026-08-15, when two lanes swept each other
  within twelve minutes using the two *mutually exclusive* remedies:
  `git commit -- <pathspec>` reads the **worktree** and discards your staged
  hunks; bare `git commit` reads the **index** and is defeated by a concurrent
  `git add`. Both lose, in opposite directions. Pathspec discipline is not a fix
  for this, and the rules above cannot make it one.
  The remedy is the repository's own rule one level down — per-lane state in
  per-process environment, the same reason lane identity is `AXEYUM_AGENT`:

      export GIT_INDEX_FILE="$PWD/.git/index-$AXEYUM_AGENT"
      git read-tree HEAD          # REFRESH FIRST, EVERY TIME
      git add <your files>
      git commit -m "…"

  `git read-tree HEAD` before every stage is not optional: a stale private index
  **reverts** whatever other lanes committed since you created it. Verified both
  ways — without the refresh, one lane's commit shows `a.txt | 2 --` and undoes
  the other's landed change; with it, both edits survive and each commit carries
  only its own file. Do not use a bare `git commit` even with a private index if
  you have not refreshed it.
- **AND THEN RESYNC THE SHARED INDEX — the private-index remedy leaves a staged
  revert of your own commit behind it.** This is the seventh incident and the
  second one *caused by the fix*. The mechanism: you commit from a private index,
  so `HEAD` advances, but the **shared** `.git/index` still holds the pre-commit
  blobs for those paths. Relative to the new `HEAD` that reads as a staged
  revert — and for a file you newly added, a staged **deletion**. The next lane
  to run a bare `git commit` applies it, and your work disappears in a commit
  that looks like someone else's.

  Measured twice within one hour on 2026-08-15. One lane found a staged `−138`
  revert of the golden-pin fix it had just landed, plus a staged deletion of its
  new status file. The coordinator's was a staged **−430** revert across ten
  files, including deleting a 130-line script that had been committed minutes
  earlier. In both cases every file was byte-identical to `HEAD` **on disk** —
  the content was never at risk, only the index was, which is exactly why nobody
  noticed: `ls` and `git show` both look fine.

  So after committing, from the shared index:

      unset GIT_INDEX_FILE
      git add -- <the paths you just committed>   # worktree == HEAD, so this is
                                                  # a content no-op; it only
                                                  # clears the staged revert
      git diff --cached --stat HEAD               # MUST be empty

  Do **not** `git read-tree HEAD` the shared index to fix this: another lane may
  have legitimately staged work there, and you would drop their staging. Resync
  only your own paths, and only after confirming the worktree content matches
  `HEAD` for each.

  **`git diff HEAD -- <path>` is the WRONG test for a file you newly added**, and
  it fails in the direction that loses work. A new file has no entry in the
  shared index, so `git diff HEAD` reports it as a *deletion* — the check says
  "differs", you decline to restage, and the staged deletion of your own new
  file is exactly what stays behind for the next lane to commit. Two lanes hit
  this on 2026-08-18, one of them nearly leaving a staged −525-line deletion of
  two files it had just added. Compare the objects instead, which is defined for
  a path the index has never seen:

      for f in <paths>; do
        [ "$(git hash-object "$f")" = "$(git rev-parse "HEAD:$f")" ] \
          || echo "DIFFERS: $f"
      done
- **`read-tree` AND `commit` MUST BE THE SAME SHELL INVOCATION — a refresh in an
  earlier command is already stale.** Eighth and ninth incidents, 2026-08-17,
  both by agents that had read the rule above and believed they were following
  it. `agent-reals-design` deleted 1,623 lines of `rat_prelude`; an hour later
  `agent-characterization` deleted 1,514 lines of the same file the same way.
  Each repaired it, but only after the fact.

  The mechanism is that "refresh first" reads as setup rather than as part of
  the commit. Between one Bash call running `git read-tree HEAD` and a later one
  running `git commit`, **another lane commits and HEAD moves**; the private
  index still holds the old blobs, so committing writes them back and reverts
  the other lane. Nothing in the diff you were looking at hints at it.

      # WRONG -- two invocations, HEAD can move between them
      git read-tree HEAD
      … think, edit, run a test …
      git add -- a.rs && git commit -m "…"

      # RIGHT -- one invocation, nothing between
      git read-tree HEAD && git add -- a.rs && git commit -m "…"

  Two checks catch it, and the obvious one does not. `git diff --cached --stat`
  compares against the index's own stale base and looks clean; **`git diff
  --cached --stat HEAD` is the one that fires.** And after committing, read the
  FILE COUNT in `git show --stat`, not whether your own hunks look right: the
  only symptom in the second incident was 15 files where 11 were staged.

  **One invocation is still not enough — VERIFY THE STAGED SET.** Tenth incident,
  2026-08-18, by a lane that did put `read-tree`, `add` and `commit` in a single
  Bash call: another lane committed during the `git add`, and the commit reverted
  six of its files (−302 lines). The window is real work, not a race you can win
  by typing faster. Amended within a minute, nothing lost, but the rule above
  does not prevent it.

  So do not trust the sequence — assert the outcome. The staged set must equal
  your pathspec, checked between `add` and `commit` in the same invocation:

      P="a.rs b.rs"
      git read-tree HEAD && git add -- $P && \
        test -z "$(git diff --cached --name-only HEAD | grep -vxF "$(printf '%s\n' $P)")" && \
        git commit -F - <<'MSG'
      …
      MSG

  If that `test` fails, HEAD moved: re-run `read-tree`/`add` and check again. The
  diff-against-HEAD is what sees it; the index's own base cannot.
- **`git commit -m "…"` SILENTLY DELETES anything in backticks.** Double quotes
  mean the shell runs each backtick span as a command and substitutes its output,
  which for prose is almost always empty. This repository's commit messages are
  full of backticked identifiers by convention, so the trap is universal here:
  one message lost `` `--` ``, an entire example command line, and `` `add_neg` ``,
  leaving sentences like "cargo swallows a flag when the command has no
  separator". The commit is fine; the explanation of it is gone, and `git log`
  gives no hint that anything was removed. Use a quoted heredoc — which cannot
  substitute anything — and the message survives verbatim:

      git commit -F - -- <paths> <<'MSG'
      subject line

      body with `backticks` and $vars intact
      MSG

  `git commit -m 'single quotes'` also works, but only until the message needs an
  apostrophe.
- **THE STAGED-SET ASSERTION CANNOT CATCH A WRONG PATHSPEC — check it BOTH
  ways, or use `scripts/lane-commit.sh`.** Eleventh and twelfth incidents,
  2026-08-18, by the same agent within an hour, in opposite directions, both
  passing the assertion above.

  *Too narrow.* A pathspec derived from `git status --porcelain
  --untracked-files=no` after a `git mv`: the renamed-TO files are untracked in a
  freshly `read-tree`'d private index, so they were omitted. The commit landed
  four ADR **deletions with none of the additions** — 705 lines removed, 243
  added — and four decisions were absent from history while every reference in
  the tree pointed at them.

  *Too wide.* The remedy was `--untracked-files=all`, which in a shared checkout
  enumerates **other lanes' untracked files**. The next commit swept a sibling
  lane's new example and another's pinned output file.

  Both passed `test -z "$(git diff --cached --name-only HEAD | grep -vxF …)"`,
  because that compares the staged set against the pathspec and **both times the
  pathspec itself was wrong**. It catches HEAD moving under you mid-commit, which
  is a real hazard and a different one. Note also that with rename detection on,
  `--name-only` prints only a rename's DESTINATION, so a pathspec that correctly
  names both sides is reported as half-unstaged — use `--no-renames`.

  `scripts/lane-commit.sh -m <msgfile> -- <path>…` takes the paths explicitly and
  refuses unless: nothing staged that you did not name, nothing named that failed
  to stage, and no path in `HEAD` gone from disk with its deletion unstaged in a
  directory you are committing into (the half-rename). It then resyncs the shared
  index for exactly those paths, using `git hash-object` against `git rev-parse
  HEAD:<path>` rather than `git diff HEAD`, and `git reset HEAD -- <path>` for
  anything another lane moved under you. Controls:
  `scripts/tests/test-lane-commit.sh`, one case per incident above; each guard
  mutation-verified to kill exactly one.

  The guard that catches the *wide* case is unreachable when every named path is
  an explicit file — `git add -A -- <file>` cannot stage anything else. It fires
  on a pathspec naming a **directory**, which is what actually happened. A suite
  without that case would let the guard be deleted while staying green.
- **A MERGE CANNOT USE A PRIVATE INDEX, SO ANOTHER LANE'S STAGED FILE BLOCKS
  YOURS — USE A DETACHED WORKTREE.** The `GIT_INDEX_FILE` remedy above covers
  *commits*. A merge has to write the index, and git refuses when the shared one
  holds a staged path the merge would touch:

      error: Your local changes to the following files would be overwritten by merge:
        docs/plan/status/117-parity-freshness.md
      Merge with strategy ort failed.

  Measured 2026-08-21. That file was another lane's, staged and uncommitted, and
  **no incoming commit touched it** — git is conservative about any staged path.
  Unstaging it is exactly the "you would drop their staging" mistake this section
  already warns against, and `git stash` is worse (it corrupted a file the same
  day: the pop conflicted and wrote `<<<<<<<` markers into a source file while
  `git status` still showed the expected shape).

  The way through is an index that is genuinely yours:

      W=/data0/axeyum/scratch/wt-$AXEYUM_AGENT-push
      git worktree add --detach "$W" HEAD
      cd "$W" && git merge --no-edit origin/main && scripts/lane-push.sh --to main
      cd - && git worktree remove --force "$W"

  A worktree has its own index and its own `HEAD`, so the merge, the regeneration
  and the push all happen without touching the shared checkout. Verify afterwards
  that their entry survived — `git ls-files -s <path>` should print the same blob
  hash it did before you started.

- **AN ADR NUMBER IS A SHARED ALLOCATION POINT, AND GENERATING THE INDEX DID NOT
  FIX IT.** `docs/research/09-decisions/README.md` is generated precisely so
  concurrent lanes stop conflicting on it — but the NUMBER in the filename is
  still one key every lane writes, chosen by looking at the tree. Two lanes that
  start within an hour of each other read the same maximum and pick the same
  next number.

  Measured 2026-08-30, twice in a row: `queue-refill` and `holdout-amendment`
  both wrote **0617**; after the first was renumbered to 0618,
  `mobility-census` had independently written **0618** as well. Each collision
  costs a `git mv`, a sweep of inbound references, and an index regeneration —
  and the second one was caused by the fix for the first.

  Nothing surfaces it at merge time. The two files have different names, so git
  merges them cleanly and `git show --stat` looks ordinary.
  `scripts/gen-adr-index.py --check` DOES fail on a duplicate outside its
  grandfathered `{0166, 0167}` set (verified: injecting a duplicate makes it
  exit 1), and it is wired into both aggregate gates — the gate is not the
  problem. The problem is that merges happen far more often than the ~10-minute
  gate runs.

  So: **when briefing a lane, name a specific number well above the current
  maximum**, and tell it to check the tree first. When merging, run
  `scripts/check-merge-hygiene.sh` (~2s) — it runs `gen-adr-index.py --check`
  plus a conflict-marker scan and a generated-file freshness check, each of the
  three being a defect that reached a commit through this same gap.

- **Lane identity lives in the environment, not in git config.**
  `export AXEYUM_AGENT=<lane>`; the `hooks/commit-msg` hook stamps an
  `Agent:` trailer and refuses an unidentified commit. Do **not** use
  `git config axeyum.agent` in a shared checkout: it is repo-local, so the
  last writer silently renames every other lane's commits (this happened
  within five minutes of the hook landing).
- **Never** `git stash`, `git checkout`/`restore` on files you did not
  modify, or any history rewrite — another lane's uncommitted WIP lives in
  this tree. Treat dirty files you don't own as off-limits.
- Format single files with `rustfmt --edition 2024 <file>` — never
  `cargo fmt`/`cargo fmt -p` (workspace-wide; clobbers other lanes' WIP).
- **MUTATION TESTING IN THE SHARED WORKTREE BREAKS OTHER LANES' BUILDS, and the
  failures it causes look like their bug.** Deleting a guard to check that
  exactly one test dies means editing a tracked source file in place. Every
  other lane compiles from that same file, so for the seconds or minutes your
  mutant is on disk, their build sees it.

  Measured 2026-08-20: verifying a `MAX_UNARY_TERMS` budget by `sed`-ing the
  constant to `4096` and then `2` made a sibling lane's
  `cargo test --features full --lib reconstruct::` report **8 failures**, all in
  `string_length::tests`, all complaining about "the **2** budget" while the
  committed constant was `128`. That lane lost time re-running from a snapshot
  before working out the failures were not theirs. Nothing in the output pointed
  at another lane; a mutated constant is indistinguishable from a wrong one.

  `scripts/tests/mutation_controls.py` does not have this problem, and that is
  most of why it exists: it `copytree`s to a scratch root and mutates the copy.
  Register a suite there instead. If you must mutate by hand, do it in
  `W=$(scripts/lane-snapshot.sh HEAD)`, never in the shared checkout — and see
  the `__pycache__` trap under Gotchas, which makes hand loops report the
  *previous* mutant's result anyway.

- **TWO LANES CAN EACH BUMP A PINNED COUNT CORRECTLY AND THE MERGE STILL WILL
  NOT COMPILE.** The standing rule — "recompute by COUNTING the list, never by
  adding to the old number" — is written for the LANE, and it works: measured
  2026-08-25, both the chain-rule lane and the series lane landed one
  declaration each and both correctly took `creal_tests.rs`'s pin from 199 to
  200 against their own bases.

  Git then merged both array ENTRIES cleanly, because they are different lines,
  and left the DECLARED size at 200 with 201 entries:

      error[E0308]: mismatched types
      let expected: [(&str, crate::NameId, &str); 200] = [ ... ]

  The case the rule does not cover is the COORDINATOR merging two correct
  increments. So recount after every merge that touches a pinned list, not only
  after a conflicted one — this merge had **zero conflicts**. It happened eight
  times in one day across `creal_tests.rs` and `nat_prelude_tests.rs`.

  `hooks/pre-push` refuses the push, so it does not reach `main`; the cost is a
  wasted push attempt, which on this repository is several minutes of battery.

  **AND "COUNT THE LIST" IS ITSELF EASY TO GET WRONG, BECAUSE ENTRIES ARE NOT
  ONE PER LINE.** rustfmt wraps any entry whose name is long across five lines,
  beginning with a bare `(` on its own line, so the obvious count -- lines
  matching `("` -- silently undercounts. Measured 2026-08-26 while resolving a
  pin conflict in `creal_tests.rs`: **210 such lines against a true 283**, and
  the wrong number was written into the file before the gap was noticed. An
  entry starts at either `^        \("` or `^        \($`, and only those two.

  Do not hand-roll it. `scripts/recount-pinned-inventory.py <file>` rewrites the
  pin to the counted value and exits nonzero when it moved; `--check` reports
  without rewriting. Controls: `scripts/tests/test-recount-pinned-inventory.sh`,
  each guard mutation-verified to be killed by the case that names it.

  **CURRENT STATE (2026-08-27): `creal_tests.rs` no longer has this pin at
  all.** Everything above is the incident history that motivated the fix, kept
  because the failure mode it describes is general (it will recur in
  `nat_prelude_tests.rs` or anywhere else this array shape is used) — but the
  432-entry single array is gone from `creal_tests.rs` specifically. It was
  the thing making EVERY pair of concurrent `creal` lanes collide (any two
  declarations anywhere in `creal/` touched the same one file), so it was
  sharded into one plain `Vec` per `creal/` source module under
  `crates/axeyum-lean-kernel/src/creal/inventory/` (plus `base.rs` for the
  algebra declared directly in `creal.rs`), registered from
  `crates/axeyum-lean-kernel/src/creal/inventory.rs`. A lane adding a
  declaration to an existing `creal/` module now edits exactly one file —
  that module's shard — never the array every other `creal` lane also edits.

  No shard carries a pinned length, and none should be added: the length pin
  answered "is this list internally consistent", never "is it complete", and
  `creal_tests::every_creal_declaration_is_checked_and_axiom_free` already
  answers the question that matters — coverage read from
  `kernel.environment()` directly, both directions (an environment
  declaration missing from every shard, and a shard entry naming a
  declaration no longer in the environment) — plus a check new to the
  sharded shape: no declaration may be claimed by more than one shard. A
  single array could never have that failure mode; many files can, if two
  lanes both add an entry for the same declaration. `scripts/
  recount-pinned-inventory.py` is unchanged and still applies verbatim to any
  `*_tests.rs` that keeps this pin shape (`nat_prelude_tests.rs` and
  `complex_tests.rs` do not use it today — see their own `theorem_names`/
  `named` helpers — so nothing else needed updating for this).

- **AN ABSOLUTE PATH UNDER THE MAIN CHECKOUT SILENTLY EDITS THE MAIN CHECKOUT,
  EVEN FROM INSIDE A WORKTREE.** A lane working in
  `.claude/worktrees/agent-<id>/` opened `CLAUDE.md` by its familiar path,
  `/home/mjbommar/projects/personal/axeyum/CLAUDE.md`, and was reading — and
  would have been writing — the SHARED checkout, not its own isolated copy. The
  worktree's whole purpose is that its writes are isolated; an absolute path
  defeats that without any error.

  It is asymmetric and that is what makes it easy to miss: a shell command is
  fine, because the lane's cwd IS the worktree and relative paths resolve there.
  Only the absolute form escapes. The lane caught it before an edit landed in
  the wrong tree, but it cost exploration turns and it would have looked, to
  everyone else, like a mystery edit from nowhere.

  So from a worktree, prefix absolute paths with your own worktree root, or use
  relative paths from cwd. When briefing a lane, say this explicitly — "read
  your reference files from your own worktree" is not enough, because the lane
  believes it is doing that.

- **THE SESSION SCRATCHPAD IS SHARED BY EVERY LANE IN THE SESSION, and a
  fixed-name file in it is a shared append point.** `/tmp/claude-1000/<project>/
  <session>/scratchpad` is per SESSION, not per lane, so concurrent lanes write
  into one directory. On 2026-08-18 a lane kept its snapshot path in `W.txt`
  there; another lane overwrote `W.txt` with its own path, and the first lane's
  next `cp` loop wrote 13 files into the second lane's `/data0` snapshot tree
  before it noticed. It restored every one with `git show <sha>:<path>`, but any
  UNCOMMITTED edit inside that snapshot would have been gone.

  The failure is not the collision, it is that the collision was silent and
  compounded: a wrong path in a variable turns an ordinary `cp` into a write
  into someone else's checkout. Name scratchpad files per lane
  (`$AXEYUM_AGENT.W`, not `W.txt`) — the repository's own rule about per-lane
  state in per-lane paths applies here too, and nothing said so until it cost
  something. Prefer `scripts/lane-snapshot.sh`, which already stamps its
  directories with the owning lane, and prefer passing paths in a variable
  within one invocation over persisting them to a file at all.
- **Push with `scripts/lane-push.sh`, and never start a second push.** Measured
  2026-08-19: two pushes started ten minutes apart took **5,510 s and 9,876 s**,
  and the second's own steps account for only ~4,900 s of that — the rest was
  spent blocked on `hooks/pre-push`'s worktree flock, printing nothing. `git
  push` is silent while it waits and has no timeout, so that state is
  indistinguishable from a hang, and I did it to myself twice in one day. The
  wrapper refuses with exit **75** when another push is running (`--force`
  overrides), and prints what the push will COST before starting: the hook exits
  immediately when no `*.rs`/`*.toml` changed in the range, and otherwise runs a
  battery measured at **545 s uncontended** — with single steps reaching 2,699 s
  under lane contention. Batching commits makes that early exit fire less often,
  not more: one Rust file in a range of twenty commits buys the whole battery.
- **Heavy cargo goes through `scripts/cargo-serialized.sh <cargo args…>`.** Two
  dev boxes (s1, s4) have been taken down by concurrent lane builds, and on
  2026-08-17 a kernel OOM killed a live agent session — one test reached 125 GB,
  because `recv_timeout` on a detached thread bounds *time*, not memory. Every
  lane was told in prose to serialize; prose does not hold a lock. The wrapper
  takes an `flock` on a host-local file (one cargo at a time on this host) and
  runs the job in a `systemd-run --user --scope` carrying **both** `MemoryMax`
  and `MemorySwapMax`, so the ceiling kills the JOB instead of leaving the host's
  OOM killer to pick — and it has picked the agent.

  **`MemoryMax` alone does not bite, and I nearly documented that it does.**
  Measured here: `MemoryMax=64M` *is* applied (`memory.max` reads `67108864`
  inside the scope's cgroup) and a 400 MB allocation still succeeds, because
  `memory.swap.max` is `max` and the cgroup just swaps — on a box with 7 G of
  swap already 6 G full, so the runaway thrashes and takes the host down anyway.
  Adding `MemorySwapMax=0` turns the same allocation into status **137**, a
  SIGKILL from the cgroup's own OOM killer, host untouched. A ceiling without a
  swap ceiling is decoration.

  So the wrapper carries its own probe: `scripts/cargo-serialized.sh --self-check`
  over-allocates through the same lock and the same scope construction and fails
  if it survives. It discriminates — `AXEYUM_CARGO_SWAP=1G` flips it to
  `NOT-ENFORCED|status=0|out=SURVIVED`, exit 1. **Run it per host**: swap and
  cgroup delegation differ, so a wrapper that caps s4 says nothing about s5.
  Exit **75** means the lock timed out, deliberately distinct from a test
  failure; the job's own status passes through otherwise (verified 0, 101, 75).
  `AXEYUM_CARGO_MEM` / `AXEYUM_CARGO_SWAP` / `AXEYUM_CARGO_WAIT` /
  `AXEYUM_CARGO_CPUS` tune it. Snapshot builds should set `AXEYUM_CARGO_LOCK` to
  a per-tree path so a long cold build does not starve the shared worktree.
- One writer per worktree/area at a time; long-running background gates are
  run FOREGROUND by the agent that owns them (waiting on completion
  notifications has stalled agents repeatedly).
- Full details: [docs/contributor-guide/multi-agent-worktrees.md](docs/contributor-guide/multi-agent-worktrees.md).

## Hard Rules

- **Partial/underspecified operators carry a fuzz seed-class that generates the
  degenerate argument.** A wrong-unsat shipped (`a946f925`) because
  `div`/`mod`-by-**constant-zero** was folded to a fixed convention, and the
  differential fuzz that "passed" only ever emitted *variable* divisors — it
  structurally could not generate `(div x 0)`. Every underspecified operator
  (int `div`/`mod`-by-0, `bvudiv`/`bvurem`-by-0, `str.at` out-of-range,
  `str.to_code` of non-singletons, …) must have a fuzz generator that
  deliberately emits the degenerate case, or the differential gate is blind on
  exactly the axis where soundness is most fragile. A corpus sweep + a fuzz
  that avoids the corner is not a soundness gate.
- The default build must compile with **no C/C++ dependency**; native solver
  backends are feature-gated leaf dependencies only.
- `unsafe_code` is denied workspace-wide (workspace lints); exceptions need
  an ADR.
- Semantics, model/proof lifting, and replay/checker routes must be explicit
  before a new operator, rewrite class, encoding, backend, or logic fragment
  becomes public surface.
- `unknown` is a first-class solver result, never an error.
- Determinism is a public API promise: stable iteration order, explicit
  seeds, explicit resource limits. No hash-map iteration order in output.
- Every `sat` result must be checkable by evaluating the original term
  against the lifted model; never drop lowering/lift maps after solving.
- Term handles are lifetime-free `Copy` IDs; never let backend FFI types or
  lifetimes leak into public APIs.
- BV operator semantics follow SMT-LIB totality verbatim (e.g.
  `bvudiv x 0` = all-ones); see
  [docs/research/01-foundations/bv-semantics-and-partial-operations.md](docs/research/01-foundations/bv-semantics-and-partial-operations.md).

## Gotchas

- **`explain_corpus` IS NOT AN ORACLE, and it now says so in every line it
  prints.** It calls `check_auto_explained` on the *flat* view; the shipped
  front door is `solve_smtlib`, which adds the ADR-0052 `StringGate`, the word
  / online / membership routes, and the multi-`check-sat` lifecycle. Measured
  2026-08-21 over 397 committed benchmarks, the two disagree on **134** — 71
  where this tool ERRORS and the front door decides, 46 bounded-string
  refusals (the front door decides three of those `sat`), 17 where it says
  unknown and the front door decides.

  This entry used to say "it prints `unsat` for `regex-032-…-fuzz`, which is
  genuinely `sat`", and a doc line did not stop a whole lever being built on a
  fabricated verdict. So the output changed instead: every verdict is prefixed
  (`flat-unsat`, `front-door-sat`, `not-attempted`) and **nothing it emits can
  be `grep -x`'d as an SMT-LIB answer**; the two structurally divergent shapes
  — a multi-`check-sat` script, and a bounded-string `unsat` — are refused with
  a reason instead of answered; and every JSONL record carries
  `"oracle":false`. Pass `--confirm` to have it re-solve each file through the
  real front door and stamp `front_door_verdict` / `agrees`.

  Do NOT measure that divergence by diffing against `smtcomp_cli`: SMT-COMP
  §7.1.2 makes the CLI print `unknown` for an error, so 59 both-sides-decline
  files read as disagreements and the count comes out 193 instead of 134.
  `--confirm` compares in-process, which is the difference.
- **AN INVENTORY TEST THAT ITERATES ITS OWN LIST CANNOT SEE WHAT IS MISSING
  FROM IT, AND ITS NAME WILL SAY OTHERWISE.** Measured 2026-08-26.
  `every_creal_declaration_is_checked_and_axiom_free` looped over a
  hand-maintained `expected` array, checking each entry's declaration kind and
  `axiom_footprint`. Its name promises *every* `CReal` declaration; its
  behaviour was *every declaration someone remembered to add*. Green on every
  run, for as long as it has existed.

  **The pinned length does not catch this.** It constrains the list against
  itself -- 294 entries declared, 294 entries present -- and says nothing about
  what the prelude actually declared. Both numbers can be right while the test
  covers a fraction of the environment.

  The fix is one assertion, checked against the ENVIRONMENT rather than the
  list: enumerate `kernel.environment().iter()`, filter to the namespace the
  file owns, and fail naming anything absent from `expected`.

  It found **twelve** unchecked declarations on its first run. Five were that
  session's. The other seven had been unchecked far longer -- `lt_cotrans` and
  `apart_cotrans` (Ch12 cotransitivity) and the entire `limit` family
  (`RegularSeq`, `limitSeq`, `limitSeq_regular`, `limit`, `limit_dist`), which
  is **Bishop completeness**, this project's constructive substitute for the
  least-upper-bound property. None had a `Theorem`-kind or axiom-footprint
  check from this test.

  All twelve passed once listed, so nothing rested on an axiom; the gap was in
  the checking. And the headline axiom-freedom figure was never affected,
  because `prelude_theorem_inventory` reads the environment directly -- which
  is precisely why this file insists on reading metrics from the kernel and
  never from a list or from source text.

  Generalize it: **any test named "every X" must derive its X from the
  authority, not from a literal.** If the list is maintained by hand, the test
  measures the maintainer's memory. `nat_prelude_tests.rs`'s `theorem_names`
  and the `complex` `named` array have the same shape and deserve the same
  assertion.

- **A TEST THAT PASSES ONLY UNDER AN AMBIENT ENVIRONMENT VARIABLE IS A GATE ON
  ONE SHELL, AND THE LANE THAT ADDS IT CANNOT SEE THE PROBLEM.** Measured
  2026-08-26. A lane added a concrete-instantiation test for
  `riemann_sum_reblock_close`, ran `cargo test --lib creal::`, got **93 passed,
  0 failed**, and reported -- accurately, from where it stood -- that no
  deep-stack wrapper was needed for this step. In a clean shell the same test
  SIGABRTs: `has overflowed its stack`, `signal: 6`.

  The cause is that the lane had `RUST_MIN_STACK` **exported earlier in its own
  run**, while hand-bisecting the stack requirement of the PREVIOUS step's test.
  Every later command in that shell inherited it. Real measurement, false
  conclusion, and nothing in the output hints at the dependency.

  Two rules follow, and the second is the one that generalizes:

  - A test needing a deep stack must **carry it explicitly** -- an
    `on_a_deep_stack` wrapper spawning a 256 MiB thread (the pattern in
    `creal_point_tests.rs`, `creal/integral.rs`) -- never rely on the ambient
    `RUST_MIN_STACK`.
  - **Verify with `env -u <VAR>` for any variable you have set by hand this
    session.** A coordinator re-running the lane's command in the coordinator's
    own shell reproduces the lane's contamination whenever both shells set the
    same thing. `env -u RUST_MIN_STACK cargo test ...` is what distinguished
    them here.

  Note the interaction with the entry below: a stack overflow in this kernel
  looks exactly like a broken tool or an absent declaration (`exit 134`,
  SIGABRT), which is why `prelude_theorem_inventory` must be run `--release`.
  The same symptom, two unrelated causes, and neither one is a proof bug.

- **A CONCRETE INSTANTIATION CAN HIDE THE BUG A SYMBOLIC ONE EXPOSES, so the
  mandatory-instantiation rule is NECESSARY AND NOT SUFFICIENT.** Measured
  2026-08-26 in `creal/exponential.rs`. A proof of `2^n <= 2*n!` type-checked at
  every concrete `n` tried (2, then 3) and failed with `TypeMismatch` for
  symbolic `n`. The cause was real: `Int.int_le_of_mul_le_mul_right`'s
  conclusion is `a * (ofNat c)`, ONE multiplication, while the chain produced
  `(a * d1z) * d2z`, two left-associated ones -- propositionally equal, not
  definitionally. At a concrete `n` every term reduces to a numeral and full
  evaluation papers the associativity hole over.

  This cuts against the instinct the rest of this file builds. Concrete
  instantiation is what catches a transposed branch, a sign error, and a wrong
  hand-computed expectation -- three separate defects this session, none of
  which a symbolic check would have found. But numerals reduce, and reduction
  hides every defeq-shaped gap. The two checks fail on disjoint defect classes,
  so a declaration needs BOTH: instantiate at concrete arguments AND confirm the
  proof term builds against a genuinely free variable.

  The bisect that finds it: run `Kernel::infer` on each intermediate step with a
  FREE fvar in the position, not a literal, and compare the inferred shape
  against what the next lemma's conclusion expects. The first step whose shape
  differs is the one needing an explicit `mul_assoc` (or `add_assoc`) rewrite.

  **AND THE ERRORS CAN BE MUTUALLY CONSISTENT, WHICH DEFEATS CHECKING THE
  INTERMEDIATES ONE BY ONE.** Measured 2026-08-29 on `Int.fib_two_mul`. Five
  `isymm(a, b, h)` call sites had their arguments backwards relative to the
  hypothesis actually in hand — and **each individually type-checked**, because
  each was checked against an expectation that was backwards in the same way.
  A concrete `n = 3` test passed every named intermediate cleanly. The defect
  surfaced only when the pieces were chained through `itrans` at a genuinely
  free `n`.

  So "instantiate concretely AND check symbolically" is right, and *where* you
  check symbolically matters: a per-step symbolic check can pass on a chain that
  does not compose. The technique that found it was to re-derive the whole proof
  against a real `fresh_fvar` pushed into an explicit `LocalContext`, checking
  each named intermediate with `infer_in`/`def_eq_in` — the free variable is
  what makes a self-consistent pair of reversals disagree.

- **A CERTIFICATE MUST CARRY EVERY DISTINCTION ITS PRODUCER MAKES, or the checker
  cannot re-derive the refutation — and mutation testing will not find the gap.**
  Measured 2026-08-20 in `nra_monomial_bound_cert.rs`. The producer distinguished
  `M < k` from `M <= k` (the first is refuted by `M >= k`, the second only by the
  strictly stronger `M > k`), but the certificate recorded only the CONSTANT `k`.
  So `check_monomial_bound_refutation` could not tell them apart and returned
  `true` for a certificate refuting `a >= 1 ∧ b >= 1 ∧ a*b <= 1` — **satisfiable
  at a = b = 1**. No wrong `unsat` shipped, because the producer declines that
  query; but the *independent re-validator*, whose entire job is to catch a
  producer that is wrong, would have accepted a forged refutation of a SAT query.

  **Mutation testing could not have caught this, and it is important to see why.**
  Mutation deletes guards that EXIST and asks whether a test dies. A guard that
  was never written has nothing to delete. Nine guards in that module were each
  killed by exactly one test, and the module was still unsound. The technique
  measures the strength of the guards you have; it says nothing about the ones
  you are missing.

  What does find them: for every case the PRODUCER distinguishes, write an
  adversarial fixture over a **satisfiable** query in which every other guard
  passes. If the certificate cannot express the distinction, that fixture is
  impossible to write — and the impossibility is the finding.

- **BANNED SHELL IDIOMS. Every one of these has printed a WRONG ANSWER that was
  then reported as fact, and none of them look broken when they fail.** The
  shared failure mode: the command exits 0 and prints something plausible.

  1. **`echo "exit=$?"` after a pipeline.** `$?` is the LAST stage. Measured
     2026-08-20: `python3 scripts/create-autogenesis-nursery-dispatch-baseline.py
     --check 2>&1 | tail -12; echo "exit=$?"` printed `exit=0` for a script that
     exits **1** — `tail`'s status. Run the command bare, or use
     `${PIPESTATUS[0]}`, or `set -o pipefail`.
  2. **`grep -q` as a pipeline consumer under `set -o pipefail`.** `-q` exits at
     the first match and SIGPIPEs the producer, so the pipeline status is 141 —
     which `pipefail` turns into "not found". Measured 2026-08-20 in
     `scripts/check-control-registration.sh`: the same unchanged tree reported
     **7 orphans on one run and 3 on the next**, because whether the producer
     finished writing first depends on buffering. Use `grep -c` and test the
     count; it consumes all input and cannot SIGPIPE.
  3. **`grep -B1`/`-A1` to pair a commit subject with its trailer.** With
     `--format=%b` the line before a trailer is BLANK. Measured 2026-08-20:
     reported **1 commit when there were 21**. Use
     `git log --format='%H|%s|%(trailers:key=Agent,valueonly)'`.
  4. **Testing a grep PATTERN interactively and trusting it in a script.** On
     this host `grep` is a shell FUNCTION wrapping `ugrep 7.5.0` in an
     interactive shell, and plain `/usr/bin/grep` (GNU grep 3.12) everywhere
     else. They disagree on `\t`: ugrep reads it as a tab in ERE, GNU grep
     reads it as a literal `t`. Measured 2026-08-25, each with its control:

         printf 'a\tb\n' | /usr/bin/grep -cE 'a\tb'   -> 0   # a real tab: NO match
         printf 'atb\n'  | /usr/bin/grep -cE 'a\tb'   -> 1   # literal 't': matches

     **54 facts / 68 `checker_command`s matched the inventory's tab-separated
     output with `\t`**, so each reported a theorem that EXISTS as absent from
     any script or CI run, while passing when a human ran it by hand. It is
     fail-closed, so flakiness rather than unsoundness -- but the evidence
     re-derived nowhere except one interactive shell. Use `[[:space:]]`, and
     **test every pattern with `/usr/bin/grep` explicitly**. `command -v grep`
     prints `/usr/bin/grep` under `bash -c` and `grep is a function`
     interactively, which is the fastest way to tell which one you have.

  5. **Reporting an empty `grep` as a negative result.** An empty answer and a
     wrong query are the same observation. This is the grep-shaped case of the
     coverage trap below; pair the negative with a positive control that MUST
     produce output, in the same command.
  6. **Fixed-name files in the session scratchpad.** It is per-SESSION, shared by
     every lane (see the multi-agent section). `push.log`, `reg.log`, `audit.log`
     collide; prefix with `$AXEYUM_AGENT`.
  7. **A "did it finish?" check that has never been shown to fire.** Measured
     2026-08-20: an end-marker sweep reported `!! NO END MARKER` for two jobs
     that had completed normally — the scripts had never written markers. The
     check was wrong, not the job, and the natural reading was the opposite.

  The rule underneath all seven, and the one to apply to any command not on this
  list: **before believing a result, ask what the command would print if it were
  broken.** If that is what it just printed, it is not evidence.

- **A HAND-ROLLED MUTATION LOOP OVER A PYTHON FILE REPORTS THE PREVIOUS MUTANT'S
  RESULT.** Python caches compiled modules on `(source mtime in whole SECONDS,
  source size in bytes)`. Mutation testing produces equal-size mutants **by
  construction** — one fixed string replaced by another fixed string at
  different sites — written back to back, well inside one second. So the cache
  is not a corner case here; it is the default.

  Measured 2026-08-20: three copies of one guard in
  `check-lra-hypothesis-binding.py` (`bind_structural`, `bind_anchored`,
  `classify_attestation`, all 138,581 bytes when mutated) each reported killing
  the *same* test — `AStructuralModule…`. Clearing `__pycache__` between
  iterations, each kills its own distinct control, correctly named. The loop was
  restoring and re-mutating exactly as intended; only the bytecode was stale, and
  `git diff` confirmed the right line changed every time, which is what made the
  wrong answer so convincing.

  Both directions occur. If the BASELINE is cached, a real kill reports
  `SURVIVED` — you go hunting a gap that does not exist. If a KILLED mutant is
  cached, a mutation that changes nothing reports `KILLED` — coverage that was
  never measured, which is the failure this repository cares most about.

  `scripts/tests/mutation_controls.py` is **not** vulnerable: its `Unittest.build`
  runs `py_compile` on every target, which rewrites the cache entry. That step
  was written to catch a subject that does not parse; its second job is invisible
  from its own code. It is now pinned by `StaleBytecodeTests` and by a self-table
  entry that keeps the syntax check and drops only the recompile. Use the
  harness. If you must loop by hand, `find . -name __pycache__ -exec rm -rf {} +`
  between iterations, and never trust two mutants that report the same dead test.
- **A SUBAGENT THAT LAUNCHES A BACKGROUND JOB AND WAITS FOR IT STALLS, AND THE
  HARNESS WILL NOT WAKE IT.** Measured 2026-08-22: three separate Sonnet lanes
  finished their real work, launched a `cargo test` in the background as a final
  check, and returned "waiting for the background test run" as their entire
  report. Each had results in hand and reported none of them. Each needed an
  explicit `SendMessage` to resume, costing minutes per incident and one full
  round-trip of context.

  This is the multi-agent form of the standing "run long gates in the FOREGROUND"
  rule, and it bites harder for a subagent because a stalled subagent looks
  *completed* to the coordinator — the task notification arrives with a
  no-content result and nothing indicates the work is done but unreported.

  **THREE MORE STALLED ON 2026-08-24, AND THE COORDINATOR HAD THE ANSWER IN
  THIS PARAGRAPH THE WHOLE TIME.** Every one of those briefs said, in bold, to
  run checks in the FOREGROUND and that "a check which did not complete is
  reported as 'did not run'". All three backgrounded the kernel gate anyway and
  returned a holding message with finished work in hand; each needed a
  `SendMessage` to resume. The gate they were told to run takes 550 s under lane
  contention, and no amount of instruction survives that.

  The paragraph below already says what to do — *"tell it not to measure at all
  and do the measuring yourself"* — and it was not followed, because asking for a
  narrow per-module check feels cheap and reads as diligence. It is neither. The
  coordinator re-runs the full gate in its own checkout before every merge
  regardless, so a lane's narrow run is **duplicated work that gates nothing**
  and is the single largest source of stalls. Do not ask a lane to run
  `cargo test` at all. Ask it to commit and report; verify it yourself.

  **Telling it not to is not enough — measured 2026-08-22, a fourth lane stalled
  after the brief explicitly said "foreground with bounded timeouts, report
  partial results rather than holding them".** The instruction does not survive
  contact with a slow gate: the agent reasons that one more check would make the
  report complete, and a backgrounded check looks like the way to get it.

  What does work is removing the temptation. Give the subagent the specific
  bounded command to run and tell it that a check which did not complete is
  reported as "did not run" — and point it at the prebuilt binaries under
  `target/release/examples/`, which take no cargo lock, for everything that is
  only a measurement. Better still, tell it not to measure at all and do the
  measuring yourself: the coordinator has to re-verify the numbers anyway. And note that prebuilt binaries under
  `target/release/examples/` run directly, take no cargo lock at all, and are the
  right tool for measurement when several lanes are contending — a sweep that
  queues behind three other lanes is what tempts an agent to background it in the
  first place.

  **AND WHEN THE MEASUREMENT *IS* THE TASK, "do not background it" is not
  advice a lane can follow.** Ninth stall, 2026-08-25: a lane sent to profile a
  gate that takes ~500 s per run returned *"I'll stop here and wait for the
  monitor's completion notification."* It could not do the work without a long
  run and had been told not to background one, so it did both and reported
  neither. Telling it harder would not have helped.

  What works is bounding the measurement in the brief instead of forbidding the
  wait: **"profile a SINGLE invocation"**, and — the part that unlocks it — *"if
  one full run is too long, profile a REDUCED input and say the numbers are from
  a reduced run."* A profile of a smaller input still locates the hotspot, and a
  located hotspot is the deliverable. Give the lane a way to finish, not just a
  way to fail.

  **ELEVENTH STALL, 2026-08-27, AND THE BRIEF HAD ALREADY ENUMERATED MONITORS.**
  The prohibition above was followed to the letter in the brief — *"do not defer
  the answer by ANY mechanism — not a background task, not a monitor, not a
  scheduled wakeup, not a second agent"* — and the lane started a monitor and
  returned *"I'll pause here and wait for the monitor's notification."*
  Enumerating the forbidden mechanisms does not work either, because the lane is
  not reasoning about mechanisms; it is reasoning that one more check would make
  its report complete.

  **So stop trying to prevent the stall and make it CHEAP.** What separated this
  incident from a costly one was purely whether commits existed:

      git log --oneline main..worktree-agent-<id>   -> EMPTY
      git -C .claude/worktrees/agent-<id> status --porcelain
        M crates/axeyum-lean-kernel/src/creal.rs
        M crates/axeyum-lean-kernel/src/creal/creal_tests.rs
        M crates/axeyum-lean-kernel/src/creal/crossing.rs

  Three modified files, zero commits, ~30 minutes of work visible to nobody. The
  brief said *"Commit BEFORE running any long check"* — the instruction exists,
  and a lane that is about to stall is exactly the lane that skips it, because
  it intends to commit *after* the check confirms the work.

  Two things that actually help, neither of which is another prohibition:

  - **Require an EARLY commit, not a pre-check commit.** "Your first commit must
    land within your first ten tool calls, containing whatever you have, even if
    it does not compile — say so in the message." A stalled lane with commits is
    resumed by reading its branch; a stalled lane without them needs a
    round-trip, and its work is one `git worktree remove` from gone.
  - **Diagnose before waking it.** `git log --oneline main..<branch>` plus
    `git status --porcelain` in the worktree tells you in one command whether
    there is work to rescue and what the resume message should demand. Do not
    infer a stall from a quiet transcript alone — see
    `is-a-subagent-actually-stalled`.

  The resume message that works names the recovery, not the failure: tell it to
  treat any unfinished check as **"did not run"**, commit what it has *even if
  broken*, and report — explicitly, that partial results reported now beat
  complete results reported never.

  **TENTH STALL, 2026-08-26, AND IT HAD A MECHANICAL CAUSE — EVERY LANE WORKTREE
  BUILDS ITS OWN `target/` FROM SCRATCH.** Measured that day: **83 GB of lane
  `target/` directories across 125 worktrees**, 400-800 MB each. Nothing is
  shared, so a lane's first check pays a full cold build of the workspace
  *behind the `cargo-serialized.sh` flock*, which is many minutes before a
  single test runs. That wait is what a lane backgrounds. No amount of
  instruction survives it, and the nine retrospectives above all read the
  behaviour as discipline when half of it is arithmetic.

  It also reframes the disk: the worktree tree is roughly half build artifacts,
  so reaping worktrees reclaims far more than the source suggests.

  **AND THE PROHIBITION MUST NAME THE OUTCOME, NOT A MECHANISM.** That lane's
  brief said, in bold, *"Do NOT background a cargo run and wait for it."* It
  started a **monitor** instead and stalled inside the letter of the rule —
  a monitor is not literally a backgrounded cargo run. Write the constraint as
  *"do not defer the answer by ANY mechanism — background task, monitor,
  scheduled wakeup, or a second agent — and if a check has not finished when you
  are ready to report, report it as 'did not run'."*

- **DISPATCHING WITHOUT `isolation: "worktree"` PUTS THE LANE IN THE SHARED
  CHECKOUT WHILE ITS BRIEF SAYS OTHERWISE.** Measured 2026-08-26: three lanes
  dispatched for one prelude, all briefed in bold that they were working in
  their own worktree, and the `Agent` calls carried no isolation. Two of the
  three needed the same `creal.rs` and `creal_tests.rs`.

  Nothing surfaces it. `git status` looks ordinary, the lane's own report reads
  like normal work, and the first real symptom would be two lanes overwriting
  each other's whole-file edits. It was caught only by noticing that a lane 32
  minutes and 104 tool calls into its task had no worktree directory.

  Two rules, and the second is the one that cost time:
  - Pass `isolation: "worktree"` for any lane that will WRITE, and never assert
    isolation in a brief you did not provide.
  - **`git worktree list` is the check — not the presence of a directory under
    `.claude/worktrees/agent-<id>`.** A capable lane may create its own worktree
    somewhere else entirely (one did, on `/data0`, as its first action after
    noticing the shared tree was mid-merge). Inferring "no `.claude` directory"
    ⇒ "working in the shared checkout" is wrong, and it produced a false alarm
    aimed at the one lane that had handled the situation correctly.

- **A BACKGROUND TASK REPORTED AS EXITED MAY STILL BE RUNNING, AND IT WILL TAX
  EVERY MEASUREMENT YOU TAKE AFTERWARDS.** Found 2026-08-21: a `python3 -` from
  a session task started **2026-08-18 03:43**, whose output file recorded
  `[exited with code 144]` at 03:49, was still at **99.5% CPU 85 hours later** —
  orphaned to `systemd`, parent shell long dead, nothing reading its stdout. The
  harness had closed the book on it; the kernel had not.

  Cost: a full core of a 16-core box, continuously, for three and a half days.
  Reaping it took load from **9.27 to 3.44**. Every wall-clock measurement on
  this host in that window — the `progress_frontier` reference frames, the
  timing in two capability diagnoses, the competition sweeps — ran ~6% short on
  capacity, and some of the ratchet's `NOT COMPARABLE` / `ADVISORY ONLY`
  markings were firing partly because of a ghost. Verdict counts are unaffected
  (a decided file is decided); anything timing-shaped is not.

  So before trusting a load-sensitive number, look for orphans, not just for
  your own jobs:

      ps -eo pid,ppid,etimes,pcpu,args --sort=-pcpu --no-headers \
        | awk '$2==1 && $4>50'      # reparented to init AND burning CPU

  Kill by **PID**, never `pkill -f <pattern>` — that pattern matches the killing
  shell's own command line, and a lane killed its own ratchet launcher that way
  the same day. `/proc/<pid>/fd` tells you what a mystery process is writing to,
  which is how this one was identified as a session task rather than a user's
  job.

- **`command -v lean` RETURNS NOTHING ON A HOST THAT HAS LEAN, and an agent has
  already reported a whole capability as impossible because of it.** `elan`
  installs toolchains under `~/.elan/toolchains/*/bin/lean` and does **not** put
  them on `PATH`. `scripts/check-lean-gate.sh` exists to document exactly this and
  resolves the pinned toolchain properly — `scripts/check-lean-gate.sh
  --print-toolchain`, or `AXEYUM_LEAN_BIN` to override.

  Measured 2026-08-22: `command -v lean` empty on s4, while
  `~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean --version` reports
  4.30.0 at the pinned commit `d024af09`. A Sonnet lane holding a working
  three-fact producer concluded from the empty `command -v` that authoritative
  admission "requires a toolchain this environment doesn't have" and declined to
  register. Nothing was wrong except the probe.

  **The Mathlib and lean4export checkouts are a separate question from whether
  Lean is installed**, and neither is answered by `command -v`. As of
  2026-08-22 they existed **on s5 only** —
  `/home/mjbommar/lean-import-scale/{mathlib4,lean4export}`, reachable by
  `ssh s5` with BatchMode, both at exactly the commits the adapter manifests
  pin (`c5ea0035…`, `a3e35a58…`), with s2/s6/s7 having neither.

  **THAT IS NO LONGER TRUE, AND READING IT AS CURRENT COSTS A THIRD OF A
  LANE'S BUDGET.** Measured 2026-08-28: a lane sized the Lean route as
  impossible here on exactly this paragraph plus an empty `command -v lean`,
  then found **s4 can run the entire import route**.
  `scripts/provision-lean-import-toolchain.sh` provisions it in ~5 minutes —
  pinned, idempotent, and `--verify` needs no network. A blobless mathlib4 at
  the pinned commit is 92 MB and the olean cache is already in
  `~/.cache/mathlib`; `lean4export` builds in under a minute. Verified by the
  coordinator at `/data0/axeyum/lean-import-toolchain`:

      LEAN_IMPORT_TOOLCHAIN|mathlib=c5ea0035…|lean4export=a3e35a58…|
                            lean=d024af09…|verdict=PASS

  So: **run `scripts/provision-lean-import-toolchain.sh --verify` before
  concluding a host cannot do Lean work.** Host-capability prose in this file
  is a snapshot of the day it was written, and this entry is the second one to
  go stale in the direction that says "impossible" about something cheap.

- **A BLIND EVALUATION POPULATION IS A SHARED RESOURCE WITH NO OWNER, AND
  TOUCHING ONE MEMBER SPENDS THE WHOLE FAMILY.** `artifacts/autogenesis/nursery-v1.json`
  preregisters 214 Mathlib propositions into train / development / **held-out**,
  and the split key is `<family>:<statement-shape>` precisely because a proof
  route for one member is evidence about its siblings. On 2026-08-21 a capsule
  was registered against `F:ml430-nat-gcd-greatest-0a04214a` — a held-out row —
  and it cost **19 of 76** held-out propositions, 25% of the partition, for one
  theorem.

  Nothing caught it for a day. `check-autogenesis-nursery.py` validates the
  manifest's *internal* integrity and never inspects what operations do to it;
  `validate-autogenesis-operations.py` mentioned partitions zero times; the
  README's "immutable held-out populations" guarantee was prose. Now gated by
  `scripts/check-autogenesis-holdout-isolation.py`, and the repair is an
  amendment ledger, never a deletion (ADR-0542).

  The trap that nearly caught the repair too: **"dependency-ready facts" and
  "train + development" are both 138 and are different sets** — the ready set is
  44 train, 44 development and **50 held-out**. Check the partition, never the
  count.

- **AN OPERATION REGISTRY WHERE EVERY ENTRY NAMES ONE TARGET IS A DISPATCH
  TABLE, NOT A PRODUCER — and it cannot fail to "produce".** Measured
  2026-08-22: 24 registered operations, 23 facts covered, **0 naming more than
  one fact, and 0 of 144 dependency-ready facts covered**. Coverage was 23-of-23
  on theorems already proved and 0-of-144 on anything unproved. Nine capsules
  landed in the ten hours before that was measured, each with a plan, a receipt
  and a gate; the shape of the output had stopped changing and nothing was
  watching that.

  This is the checker-that-cannot-fail defect moved one arrow upstream, so the
  same discipline applies: `scripts/gen-production-provenance-ledger.py` derives
  generality from `applicability.fact_ids` — never from a label a fact carries —
  and gates both counters. Before writing an operation for one theorem, ask what
  the next three targets share with it; `applicability.fact_ids` is a list and
  nothing ever required length one. Full retrospective:
  `docs/autogenesis/228-capsule-lane-retrospective.md`.

- **TWO STRUCTURALLY-UNRELATED REPRESENTATIONS OF THE SAME VALUE FORCE A FULL
  `Definition` UNFOLD, AND THE COST LANDS ON EVERY PRELUDE BUILD.** Measured
  2026-08-26. `riemannSum_integral_close`'s second leg built
  `sample(CReal.integral F a b hab u, e)` and had to show it defeq to a
  hand-rebuilt `speedup(raw, K)` term that never mentions `CReal.integral` at
  all. The two share no head symbol, so the kernel fully delta-unfolded
  `CReal.integral`'s `Definition` -- whose stored value embeds an entire
  `regular_of_scaled_cauchy` construction -- **on every prelude build**.

  `creal_prelude_builds` went **18.7 s -> 92.6 s** from that one declaration,
  and because dozens of tests build a prelude, the full `--lib` sweep went from
  802 tests in 316 s to **timing out at 1700 s with 95 tests done**. An
  unrunnable gate blocks all publication, including other lanes' finished work.

  **The fix is to make the two sides the SAME `ExprId`, not merely defeq.**
  Route through the already-checked theorem (`integral_converges` via
  `exists_elim`) instead of re-deriving its witness triple by hand: the
  eliminated witness builds the value with the identical `const_app` recipe, so
  the definition is never unfolded. Restored to **18.4 s**, statement unchanged.

  **This is NOT the concrete-witness/lazy-delta family above**, and treating it
  as one wastes the diagnosis -- everything here was symbolic, with no concrete
  `Nat` partial evaluation. Nor is `--release` the discriminator. What found it
  was **bisecting WITHIN the declaration**: build a throwaway variant keeping
  only leg 1, then only leg 2, and time each. Leg 1 was 18.35 s, leg 2 alone was
  95.15 s -- the whole regression, isolated in one experiment.

  The general rule: **when a proof must relate a value produced by a
  `Definition` to a value you rebuilt yourself, reach for the theorem that
  already names it.** If a prelude build slows by a multiple, bisect the
  declaration by legs before reaching for any of the documented families.

- **`le_congr`'s PREMISE TAKES THE PRE-SUBSTITUTION TYPE, AND AN `Equiv` PROOF IN
  A `le` SLOT FAILS IDENTICALLY TO A DIRECTION BUG.** Measured across 2026-08-26.
  Eleven separate rejections in one session came from this family, in six
  different files, and every one presented as an opaque `TypeMismatch`:

  - `le_congr(x, x', y, y', hxx', hyy', h)` needs `h : le x y` — the type
    **before** the rewrite. A lane twice passed a proof about a sub-term where
    the whole product's bound was needed; the kernel rendered `Equiv A A` (the
    reflexivity witness for the wrong side) against `A`'s unfolded definition.
  - The same call needs `Equiv x' x`, not `Equiv x x'`, when `h` is about `x`.
    Getting `x`/`x'` backwards is the single most common bug in this
    development.
  - **`Equiv` and `le` are different props.** Passing `equiv_refl` into an
    `add_le_add` slot that wants `le_refl` produces a failure indistinguishable
    from either of the above.

  Three habits that actually work, each of which produced a first-attempt
  kernel accept the same day:
  - **Mirror an existing helper's construction** rather than building a term by
    hand. Two lanes reported first-attempt accepts from this alone.
  - **Check a lemma's stated direction rather than assuming it matches its
    neighbour.** `Rat.sub_add_add`'s direction is the OPPOSITE of
    `sub_add_sub`'s, in the same file.
  - When both sides of a `TypeMismatch` are multi-hundred-KB and `Read` cannot
    load them, **write a small differ**. One lane found a swapped `rsymm` that
    way in minutes.

- **A SYMBOLIC TEST CAN BE PATHOLOGICAL, AND THE RIGHT MOVE IS TO DELETE IT AND
  SAY SO.** Measured 2026-08-26: a lane added an extra symbolic negative control
  that built fvars from a separate `IntDev`; it pegged one core at **10.7 GB RSS
  for over twelve minutes** before being killed. Not slow — pathological. The
  lane removed the test, recorded it in the commit message, and did **not**
  investigate. That is correct: the real verification is `creal_prelude_builds`
  plus the environment-derived coverage assertion, and a hanging test in the
  suite is worse than a missing one. If a test behaves this way, delete it,
  say so, and move on.

- **A CONCRETE WITNESS CAN COST THE KERNEL MORE THAN A SYMBOLIC ONE, and the
  symptom is unbounded WORK rather than a stuck term.** Measured 2026-08-26.
  `declare_e_converges` built its per-`n` proof against the **concrete**
  `k_final` (an unreduced `Nat.mul`/`Nat.add` expression) and let
  `exists_intro`'s argument check decide `speedup_term(n) =?= seq(e, n)`. The two
  sides have different head symbols, so lazy-delta unfolds **both in lockstep**
  -- and because `k_final` is concrete enough for `Nat.mul`/`Nat.add` to
  *partially* fire against the still-symbolic `n`, that drives a partial
  evaluation of `sumRange` at a symbolic index which never re-synchronises.

  `declare_converges_of_cauchy`, the existing pattern it was copying, never hits
  this: its `K` stays a **bound variable** all the way to `add_declaration`, so
  the same arithmetic stays stuck against two free variables and simply never
  runs. **Build generically over a bound `(k, h)` and substitute the concrete
  pair only in the final Pi-application.**

  The cost is not subtle. The parent commit built the prelude in **14.8 s on the
  default 2 MiB stack**; the defective one overflowed **1 GiB in RELEASE**,
  against a measured release budget of 131,072 bytes for `creal` -- roughly
  8,000x over.

  **The dangerous part is the misdiagnosis, not the bug.** A stack overflow here
  is indistinguishable from the resource limit that ADR-0584 measures, and the
  coordinator had *just* measured `creal` at exactly zero margin -- a perfectly
  plausible explanation, arrived at without testing. Wrapping the test in a
  bigger stack made it *look* fixed. **A wrapper that silences a real failure is
  worse than no wrapper**, and it is the checker-that-cannot-fail defect arriving
  by a route none of the existing guards cover.

  The first test is one command and costs nothing: **run it in `--release`.**
  Debug frames cost up to 32x release frames, so a debug-only margin overrun
  disappears in release. Do that BEFORE characterising any stack overflow, and
  bisect against the parent commit rather than reasoning about which
  explanation fits.

  **BUT `--release` IS NOT SUFFICIENT, AND THIS FILE USED TO SAY IT WAS.**
  Measured 2026-08-28: `reconstruct::arithmetic::monomial_bound` aborted with
  SIGABRT **in release**, and it was NOT runaway recursion — it was a finite,
  bounded requirement that had simply grown past the default in **both**
  profiles. `creal` went debug 2,097,152 -> 16,777,216 and release 131,072 ->
  8,388,608 in two days of ordinary development.

  So the rule separates *a debug-only margin problem* from *everything else*.
  It does **not** separate a grown requirement from a divergent term, and
  treating "fails in release" as proof of non-termination sends you hunting a
  bug that does not exist. (I made exactly that call and reported it as fact.)

  **The command that actually decides it is `--measure`:**

      scripts/check-kernel-stack-envelope.sh --measure --profile release --prelude <p>

  A real requirement bisects to a passing power of two and prints it. A
  divergent term never finds one. Then raise the row in
  `artifacts/kernel-stack-envelope.tsv` and say what grew — and note that
  `--check` was **RED on `main` and nobody had run it**, so it will not tell
  you on its own.

  Two second-order traps this incident exposed:
  - **An overflow aborts the process, so only the FIRST affected test is
    named.** Four more suites were failing for the same reason and reported
    nothing. Do not scope the fix to the test that appeared in the log.
  - **A prelude built on the CALLING thread inherits a `#[test]`'s 2 MiB.**
    The fix belongs in the constructor (one 256 MiB worker thread covering
    every call site), not in a wrapper around each test — otherwise a
    *consumer's* process aborts at the front door.

- **`Nat.add` RECURSES ON ITS RIGHT ARGUMENT, so `Nat.add(literal, k)` IS STUCK
  FOR SYMBOLIC `k` — and it fails by not reducing, not by erroring.** Measured
  2026-08-25 while normalizing a `CReal` bound: two fusion steps built
  `Nat.add(8, k)` instead of `Nat.add(k, 8)`, and the term never reduced to
  `succ^8(k)`. The kernel reported a `TypeMismatch` deep inside an unrelated
  `Rat.le` cross-multiplication unfold, several rewrites away from the cause.

  What makes it worth its own entry is the SECOND-order damage: the whole
  construction had been designed so that every `K`-containing accumulator stays
  the left operand, which keeps the index arithmetic **pure defeq and needs no
  `Nat.add_assoc`/`Nat.add_comm` at all**. Putting the literal on the left does
  not merely produce a stuck term — it silently forfeits that property, so the
  proof would need associativity and commutativity lemmas everywhere it
  previously needed none.

  The rule: **when a `Nat.add` will be padded, compared, or fused, the symbolic
  side goes LEFT and the literal RIGHT.** If a term mysteriously will not reduce
  and the error surfaces far from the arithmetic, check the operand order before
  anything else.

  **`Nat.mul` HAS THE SAME ASYMMETRY, AND IT DECIDES WHICH EQUATION IS `refl`.**
  Measured 2026-08-29. `Nat.mul` also recurses on its RIGHT argument, so
  `mul_succ : mul n (succ m) = add (mul n m) n` is refl-provable, while the
  left-successor form `succ_mul : mul (succ n) m = add (mul n m) m` is a real
  induction-proved THEOREM. A lane building `mul_lt_mul_right` copied the
  left-hand core's `mul_succ` shortcut and assumed `mul (succ b) a` reduced the
  same way. It does not: the assumption poisoned **all 169** `nat_prelude::`
  tests with one `TypeMismatch`. Fixed with an explicit transport along
  `succ_mul`.

  So the rule generalises: **before assuming an arithmetic equation holds by
  `Eq.refl`, check which argument the operation recurses on.** The mirrored form
  is a theorem, not a reduction, and copying a sibling proof's shortcut across
  the mirror is how you find out.

  **AND IT DECIDES WHICH VARIABLE A CASE TREE MUST SPLIT ON.** Measured
  2026-08-29 building the `Nat.bit` decode bridge. `bit test k` puts
  `cond test 1 0` in `Nat.add`'s SECOND position, so — because `add` eats the
  right argument — **`bit true k` is `succ`-shaped for ANY `k`, even a symbolic
  one, while `bit false k` needs `k`'s own shape exposed.** The first draft
  split its case tree on the `Nat` operands and the kernel rejected it with an
  opaque `TypeMismatch`; splitting on the **Bool** is what works.

  The technique that found it, and it is the one to reach for whenever both
  sides of a `TypeMismatch` are too large to read: a throwaway probe test that
  renders both mismatched sides with `Kernel::render_lean` and diffs them.

- **A RECURSOR APPLIED TO A BARE FREE VARIABLE IS STUCK — AND FOR A
  TWO-ARGUMENT DEFINITION YOU MUST KNOW *WHICH* ARGUMENT IT RECURSES ON.**
  The `Nat.add` entry above is one instance of a general rule: a free variable
  is not a constructor, so any `Nat.rec` on it simply does not reduce.

  Measured 2026-08-28 on `Nat.choose`, which is a **two-argument** structural
  recursion — outer `Nat.rec` on the FIRST argument, inner on the second
  (`nat_prelude/choose.rs`, the `outer_motive` / `row` construction). So
  `choose(succ a, k)` reduces and `choose(a, k)` does not, for any `k`
  whatsoever. A lane's `choose_le_succ` base case assumed `choose(a, 0)` was
  defeq to `1` for symbolic `a`; it is not, and the fix was to route through
  the equation lemma `choose_zero_right(a)` rather than rely on reduction.

  The rule: **before assuming a defeq, check which argument the definition
  recurses on, and confirm that argument is constructor-shaped in your goal.**
  An equation lemma exists for exactly this case — reach for it rather than
  hoping the term reduces.

- **ONE BAD DECLARATION POISONS THE SHARED PRELUDE BUILD, SO THE FAILURE COUNT
  TELLS YOU NOTHING ABOUT HOW MANY THINGS ARE BROKEN — AND A NARROW FILTER CAN
  MISS IT ENTIRELY.** Measured 2026-08-28: one wrong `choose_le_succ` base case
  produced `TypeMismatch` across **all 95** `nat_prelude::` tests, because every
  one of them builds the same prelude. Nothing in that output distinguishes "95
  broken theorems" from "one broken theorem"; the same shape has been seen at
  230 failures from a single name collision.

  Two consequences:

  - **Bisect by toggling declarations, not by reading failures.** The lane found
    it by commenting out each of the five `declare_choose_*` calls in
    `declare_choose_all` one at a time against a single fast test. Serial, cheap,
    and it names the culprit exactly; reading 95 identical `TypeMismatch`es does
    not.
  - **A single-test filter is not a gate for a prelude change.** The same lane
    ran `--lib <that one theorem>` and it PASSED, then the full `nat_prelude::`
    sweep failed. **The mechanism for that is NOT established** — `prelude_cache`
    is process-wide and in-memory (ADR-0464), so it cannot carry state between
    two `cargo test` invocations, and the lane's cache explanation does not hold
    up. Do not propagate it as fact. What IS established is the observation, and
    the rule it supports: after touching any `declare_*`, run the whole
    `<prelude>::` sweep and confirm a NONZERO count, never a filtered subset.

- **EVERY `Nat` NUMERAL THIS PRELUDE BUILDS IS UNARY, SO THE KERNEL'S BINARY
  LITERAL FAST PATH NEVER FIRES — AND THAT, NOT NESTING DEPTH, IS WHY LARGE
  CONSTANTS BLOW THE BUILD BUDGET.** Found 2026-08-27 by a lane chasing a
  587 s prelude build, verified independently by reading the three sites:

  - `NatOps::num` (`nat_prelude/ops.rs`) is `let mut e = self.zero(); for _ in
    0..n { e = self.succ(e); } e`. `13125` is 13,125 nested `succ`
    applications.
  - `Kernel::reduce_nat_succ` (`tc.rs`) whnfs its argument and requires
    `ExprNode::Lit(Lit::Nat(_))`. **`Nat.zero` is a `Const` with no
    definition, so it never whnfs to `Lit::Nat(0)`** — `reduce_nat_succ`
    returns `None` on `succ (Const Nat.zero)` and the tower never collapses
    bottom-up.
  - `Kernel::reduce_nat_binop` — the accelerated `add`/`sub`/`mul`/`div`/`mod`/
    `gcd`/`pow`/`beq`/`ble` — needs **both** arguments to whnf to `Lit::Nat`.
    They never do.

  So every `gcd` and division inside `Rat.normalize`, and all index arithmetic
  in `creal`, runs by unary recursion, and cost is superlinear in the largest
  magnitude **formed** — not in the depth of the expression and not in the
  operand count.

  The A/B that isolates it on one variable: bounding an intermediate at
  `8/75 <= 7/64` (largest `Nat` **525**) instead of the exact
  `512/1875 <= 7/25` (largest `Nat` **13,125**) took a prelude build from
  **587.02 s to 113.46 s**.

  **Two earlier attributions for the same symptom were WRONG and were
  propagated in briefs before this was measured** — operand *size* alone (a
  60,000 threshold that does not exist; the real run's max operand was 46,875
  and was fine) and *nesting depth* (refuted by a flat construction that
  failed identically). Do not reach for either.

  **MEASURED 2026-08-28, AND THE SCOPE IS NARROWER THAN THIS ENTRY FIRST
  IMPLIED.** `examples/nat_numeral_whnf_probe` times the same term built both
  ways and classifies the reduct, so a run that reduced nothing cannot look
  fast:

      mul 25 21     2,304 us  ->    11 us      210x
      mul 125 105  52,399 us  ->    10 us    5,240x
      gcd 512 1875  25.6 s    ->    16 us  1,600,000x
      div 13125 25  STACK OVERFLOW ->10 us      --

  So the mechanism is real and catastrophic **when a declaration forms a large
  magnitude**. But converting EVERY prelude numeral to `Lit::Nat` moves the
  `creal` prelude build only 14.91 s -> 14.23 s (4.6%, with a contended re-run
  putting the unary side *faster*) — **noise exceeds effect.** The prelude
  build as a whole was never spending its time here.

  Two consequences. First, do not reach for a global numeral change to relieve
  a slow build; it is measured at zero (ADR-0614, proposed and NOT adopted —
  the cost is 388 fact `formal.statement` strings whose rendering would drift
  silently). Second, the remedy is local and it is the one the pi rung-2 case
  proved: **keep formed magnitudes small**, which took one declaration from
  587 s to 113 s.

  What to do about it, in order:
  - **Keep formed magnitudes small.** Choose intermediate bounds that land on
    the value the next step needs rather than the exact quotient. In the case
    above `7/64` is *forced* — it is `(7/25)/(8/5)^2` — and the remaining
    factors ride `mul_le_mul_of_nonneg_left` instead of an evaluation.
  - **Do not reach for `Rat.ble`'s computational close on large operands.**
    Closing `le` by `Eq.refl` at `Bool.true` is a SMALL-NUMBERS tool. It
    settles `64/25 <= 3` cheaply and does not reach `-13/1875`; two
    independent constructions both blew the budget through it.
  - Note the kernel's binary literal machinery EXISTS and is tested
    (`nat_literal_semantics`, `nat_literal_arithmetic`, `nat_literal_bignum`,
    `nat_literal_to_constructor`, `NatOffset`). It is simply not what the
    prelude constructs.

- **`scripts/cargo-serialized.sh` TAKES A HOST-WIDE FLOCK, so a TIMING run
  under lane contention measures the QUEUE.** A lane lost a 600 s run to the
  wall this way with nothing to show. Read the test harness's own
  `finished in Xs` rather than wall-clock, or run the prebuilt binary under
  `target/debug/deps/` directly, which takes no lock. Use the wrapper for
  CORRECTNESS, the prebuilt binary for MEASUREMENT.

- **WHEN IS FLIPPING AN `ml430` MIRROR HONEST? THE TEST IS WHETHER MATHLIB
  *DEFINES* IT THAT WAY OR *PROVES* IT ABOUT A DIFFERENT DEFINITION.**

  Ten definition lanes have created new `F:nat-*`/`F:int-*` facts rather than
  flipping the `ml430` mirror, on the standing rule that "our construction is
  not Mathlib's". That rule is right far more often than not, but it was being
  applied as a blanket, and a blanket rule cannot tell you when a flip WOULD be
  honest. The criterion, checkable per fact at the Mathlib source:

  > **If Mathlib's `def` is the same function, the mirror is our statement and
  > flipping it is honest. If our definitional BODY is Mathlib's THEOREM about
  > a structurally different `def`, the mirror is a different proposition and
  > must stay open.**

  Both outcomes occurred in one session, which is why the distinction is worth
  having:

  - **`Nat.descFactorial_of_lt` — flip.** The landed lemma already stated
    `F:ml430-nat-descfactorial-of-lt`'s `formal.statement` verbatim. A quarter
    of that lane's task was evidence plus a status flip, no proof work.
  - **`Nat.multichoose` — must stay open.** A lane fetched
    `Mathlib/Data/Nat/Choose/Basic.lean` at the pinned commit `c5ea0035…`
    rather than inferring from prose. Mathlib's is a **three-case double
    recursion** (`multichoose n (k+1) + multichoose (n+1) k`), and
    `multichoose_eq : multichoose n k = (n + k - 1).choose k` is a **proved
    theorem** about it. Ours *defines* that formula as the body. So we define
    what Mathlib proves, about a different function. All three mirrors stayed
    open and the lane wrote no code.

  **Compare the fact's `formal.statement` against the landed lemma's RENDERED
  TYPE** (`nat_theorem_inventory`), never against a doc comment or a module
  banner — and when it matters, read Mathlib's actual source at the pinned
  commit. Prose has been wrong about this repository's own contents repeatedly.

  Note the residue: showing our formula and Mathlib's recursion agree at every
  argument needs an induction relating **two independently-built `Nat.rec`
  instances**. The `bitwise` lane hit the same wall from the other side
  (`bitwise and m n = land m n` is true at every concrete `{0,1}` pair and not
  definitionally equal at symbolic operands). That is a real, recurring
  boundary, not a gap in either lane's effort.

- **THE TRUSTED GATE CANNOT TELL YOU A `Definition` IS WRONG. ONLY EVALUATION
  CAN.** `Kernel::add_declaration` type-checks a proof term against its stated
  type. A `Definition` has no proof body — it is admitted once it is
  well-typed, and a function that computes the WRONG VALUE still has the right
  type. `Nat → Nat → Nat` is `Nat → Nat → Nat` whatever it returns.

  So for a definition, "the kernel accepted it" means *well-formed*, not
  *correct*. Every guard this repository leans on — `axiom_footprint`,
  `every_*_declaration_is_checked_and_axiom_free`, the prelude build — is blind
  to a definition that means something other than what you intended.

  Three instances in one day, each caught by a lane *reasoning*, not by the
  kernel:

  - **`Nat.lor`.** `Nat.land`'s `fuel = m` shortcut is sound only because AND
    has an **absorbing zero** (`m = 0` ⇒ result 0 regardless of `n`). OR has no
    absorbing element, so the same base case would **silently drop every bit of
    `n` whenever `m = 0`** — `lor 0 1000000 = 0`. Type-correct, admitted, wrong.
    Fixed by returning `n` at fuel exhaustion, which is sound because `m` is
    fully halved to 0 well within `m` steps.
  - **Bézout witnesses.** `↑(gcd x y) = x·gcdA + y·gcdB` is satisfied by *some*
    pair for **any** correct gcd, so type-checking the identity pins down
    nothing about what `gcdA` returns. The lane added evaluation at 13 points
    across all four sign branches, and it caught its own wrong hand-computation
    at `(1,1)`.
  - **`Nat.descFactorial`.** Concrete instantiation is where `Nat.sub`'s silent
    truncation actually bites, and only evaluation past the base exercises it.

  **So: every new `Definition` needs an evaluation test** — reduce it to normal
  form at concrete arguments and compare against independently computed values.
  Two rules that make the test worth having:

  - **Pick arguments that DISCRIMINATE.** `land 3 5 = 1` and `lor 3 5 = 7` use
    the same numeral pair deliberately, so a copy-paste between the two files
    fails loudly instead of passing.
  - **Keep the magnitudes small** — unary numerals mean `whnf` walks towers
    (one declaration: 2,426 unfolds against **291,261 attempts**, 98% of them
    `Nat.succ`). `land 3 5` is right; `land 512 1875` would cost more than the
    whole prelude.

  **The specific rule the bitwise family yielded, since it decides
  correctness rather than style.** A fuel-recursive binary definition here has
  the shape `Aux m m n` — the `m` operand supplies **both** the fuel and the
  value halved toward structural zero. So the fuel-exhaustion base case is
  determined by ONE question:

  > **Does the FUEL operand carry this operator's absorbing zero?**

  | definition | fuel operand absorbing? | base case | why |
  | --- | --- | --- | --- |
  | `Nat.land` | yes (`0 AND n = 0`) | constant `0` | safe |
  | `Nat.lor` | **no** (`0 OR n = n`) | return **`n`** | constant `0` would give `lor 0 1000000 = 0` |
  | `Nat.ldiff` | yes (`ldiff 0 n = 0`) | constant `0` | same reason as `land`, **not by analogy** |
  | `Nat.bit` | — non-recursive | no device at all | |

  `ldiff` is the instructive one: it takes `land`'s base case but its inner
  succ-row guard is a **hybrid** — the `n = 0` branch returns `m` (`lor`'s
  shape, since `ldiff m 0 = m`), the `m = 0` branch returns `0` (`land`'s).
  **One-sided absorption gives a mixed definition**, and copying either
  template wholesale produces a wrong one that type-checks.

  **AND THE GENERAL FORM DOES NOT HAVE TO RECONCILE THOSE FOUR BASE CASES — IT
  DERIVES THEM.** I briefed a lane that "any agreement proof must line up the
  base cases first, and they are not the same shape across the four." That was
  wrong, and the lane refuted it while landing
  `Nat.bitwise_and_eq_land` / `Nat.bitwise_or_eq_lor`.

  `bitwiseAux`'s general fuel row is `if f false true then n else 0`. For a
  **concrete** `f`, that reproduces each sibling's hand-chosen row **by δβι
  alone**: `and false true = false → 0`, matching `land`'s constant `0`;
  `or false true = true → n`, matching `lor`'s `n`. Same for the succ row via
  `f true false`. **Every base case is `refl`, no lemma.** The absorbing-zero
  rule decided what each *sibling's* row had to be; `bitwise` re-derives the
  same answer from `f` itself.

  The real difficulty is the **per-bit combine** —
  `bool_select_nat (f (beq (m%2) 1) (beq (n%2) 1)) 1 0` against `mul (m%2) (n%2)`
  — both stuck at symbolic operands and equal only once each bit is known to be
  `0` or `1`. Four leaves under a doubled `cases_mod_two`, each `refl`.

  **`Nat.mod_two_eq_zero_or_one` had to be built**, and the search for it is
  instructive: the *ingredients* existed inline in `powsq.rs`'s
  `declare_even_or_odd` (a `Bool.rec` on `beq r 0`, plus a private
  `mod_two_eq_one_of_ne_zero` giving only the `= 1` half), immediately consumed
  into a `div`-shaped conclusion that never mentions `Nat.mod`. Hiding place 2
  exactly. `binary.rs`'s seven `mod _ 2` sites use `Lt r 2` as a bound and never
  split it. Grep proof BODIES, not names.

  **FUEL-IRRELEVANCE NEEDS A *DOUBLE*-FUEL INDUCTION, BECAUSE THE SINGLE-FUEL
  ONE IS SELF-REFERENTIAL.** `Nat.land_aux_eq_land_of_le :
  ∀ fuel m n, Le m fuel → Eq (landAux fuel m n) (land m n)` landed, and the
  obvious route does not work: `land m n` unfolds to `landAux m m n`, putting
  the same value back in the fuel slot, so an induction on one fuel needs the
  canonical instance to unfold and refers to itself. The fix is to generalize
  over **two independently-chosen sufficient fuels**
  (`agree_by_double_fuel_induction`, `ops.rs`); the single-fuel statement is
  then a one-line corollary at `fuel2 := m` via `le_refl`, since defeq handles
  `land m n ≡ landAux m m n`.

  The hypothesis must be `Le m fuel`, **not** unconditional: `landAux 0 m n = 0`
  for any `m > 0` while `land m n` need not be. Callers always arrive with
  MORE than canonical fuel (`land_bit` unfolds at `fuel = bit a m`), never
  less. Pin the negative control at insufficient fuel — `(1, 7, 7)` gives
  `landAux 1 7 7 = 1` against `land 7 7 = 7` — or the statement could be
  quietly false and the kernel would prove it anyway.

  **A NEGATIVE CONTROL COPIED FROM A SIBLING OPERATOR CAN BE VACUOUS, AND I
  KEPT TELLING LANES TO COPY ONE.** `land`'s insufficient-fuel witness
  `(fuel, m, n) = (1, 7, 7)` — where `landAux 1 7 7 = 1` against
  `land 7 7 = 7` — **does not discriminate `lor` at all**: both sides give 7,
  so the "control" passes while checking nothing. The transporting lane found
  this, and picked `(1, 3, 4)` for `lor` (`lorAux = 5` vs `lor = 7`) and
  `(0, 7, 0)` for `ldiff` (`0` vs `7`) instead — **simulating each recursion in
  Python first**, before committing to a Rust proof.

  So: **derive the witness from the operator you are testing, and check it
  actually separates the two sides before you build anything around it.** A
  control inherited from a neighbouring proof is exactly the shape that looks
  rigorous and measures nothing — the failure this file warns about everywhere
  else, arriving through the door marked "reuse".

  **Two more corrections from that transport, both about `lor`:**

  - The sizing "~20 lines each" held **exactly** for `ldiffAux` (its
    `zero_left_any_fuel` is byte-for-byte `land`'s) and **not** for `lorAux`,
    which needed a nested `cases_zero_succ` on `n`: `bool_select_nat_same` does
    not apply because `lor`'s two guard branches are `m` and the reduced `n` —
    *different terms*, not one repeated.
  - **What broke `lor` was its fuel-exhaustion ROW (returns `n`, not `0`), not
    its guard order.** The absorbing-zero rule predicts the row correctly; what
    it does not predict is that the row's shape then propagates into the
    *proof* of every lemma above it.

  **AND IT PROPAGATES INTO THE *STATEMENT*, NOT ONLY THE PROOF — THE
  UNCONDITIONAL FORM CAN BE FALSE.** Measured 2026-08-29 transporting
  `land_comm`'s same-fuel commutativity to `lorAux`.
  `Nat.land_aux_comm_of_fuel : ∀ fuel m n, landAux fuel m n = landAux fuel n m`
  needs **no hypotheses at all**, because `landAux`'s fuel-exhaustion row is the
  absorbing constant `0` and is therefore symmetric for free. The obvious `lor`
  analogue is not merely harder to prove — it is **false**:

      lorAux 0 0 1 = 1     against     lorAux 0 1 0 = 0

  because the pass-through row returns `n`, which is not symmetric in `m`/`n`.
  So `Nat.lor_aux_comm_of_fuel` must carry `Le m fuel → Le n fuel`, and both
  places need them: the base case (the hypotheses force `m = n = 0`, restoring
  symmetry) and the both-nonzero step (bounding each half for the IH).

  **FOR A SYMBOLIC COMBINATOR THE BOUNDARY ROWS NEED IT TOO, WHICH IS NOT
  OBVIOUS.** Measured 2026-08-29 proving `Nat.bitwise_comm` over a symbolic
  `f`. The unconditional form is false whenever `f false true = true` (so for
  `or` and `xor`, and true only for `and`) — confirmed by Python simulation
  before any Rust — so the proof takes `lor`'s shape plus an explicit
  `hf : ∀ a b, f a b = f b a` that neither `land` nor `lor` ever needed. `hf`
  is required in **two** places: the per-bit combine, which is expected, and
  the `m = 0` / `n = 0` **boundary**, which is not — for symbolic `f` the two
  boundary rows are *different partial applications of `f`*, where for a
  concrete operator they reduce to comparable constants.

  **AND WHEN TRANSPORTING A *PROOF*, CHECK THE NESTING ORDER OF ITS CASE
  SPLITS — COPY-PASTING A CLOSING WRAPPER SILENTLY CLOSES OVER THE WRONG
  BINDERS.** Measured 2026-08-29 executing `lor_assoc` from `land_assoc`'s
  shape. `land`'s hard leaf nests its two dichotomies **Y-outer / X-inner**;
  `lor`'s nests them the **opposite** way. The copied closing wrapper therefore
  captured the outer `X`-dichotomy's binders where it needed its own inner
  `Y`-dichotomy's. Caught by self-review before the first compile — but it
  would have surfaced as an opaque `TypeMismatch` naming neither dichotomy.

  So a transported proof needs its **binder structure** re-derived, not only
  its lemma names re-pointed. The tell is a wrapper referring to fvars whose
  names match the source proof rather than the one you are writing.

  The rule to carry: **when transporting a lemma between these operators, ask
  first whether the fuel-exhaustion row is symmetric in the two operands.** If
  it is not, the transported statement needs sufficiency hypotheses that the
  original did not, and writing the unconditional version wastes the attempt on
  a false goal. Simulate both recursions in Python at small arguments before
  writing any Rust — that is what caught this one, and it is the same step that
  catches a vacuous negative control.

  **And fuel-irrelevance is NECESSARY BUT NOT SUFFICIENT for the 7 facts a
  triage attributed to it.** `land_comm`/`land_assoc`/`land_bit` and their
  `lor`/`ldiff` siblings each need something further — a `Nat.bit` decode
  bridge, or a same-fuel commutativity lemma. The triage's "these 7 reduce to
  fuel-irrelevance" was the right diagnosis of a *blocker* and an optimistic
  reading of a *cost*; I relayed it as the latter. Transport to `lorAux`/
  `ldiffAux` is ~20 lines each (the induction machinery and arithmetic helper
  carry over; only a per-auxiliary any-fuel base case is new).

  **Fuel-irrelevance is a SEPARATE piece and is not needed for agreement.**
  `bitwise f m n := bitwiseAux f m m n` and `land m n := landAux m m n` put the
  *same expression* in the fuel slot, so one counter decrements in lockstep and
  there are never two fuels to reconcile. But **7 open `natural-bitwise` facts
  (`land_comm`, `land_assoc`, `lor_comm`, `lor_assoc`, `land_bit`, `lor_bit`,
  `ldiff_bit`) DO need it** — unfolding `landAux` at `fuel = bit a m` arrives at
  a non-canonical fuel. `agree_by_fuel_induction`'s `statement` closure returns
  an arbitrary `Prop`, so `fun fuel => ∀ m n, Le m fuel → …` is directly
  expressible in it.

  Per-bit combination is a separate choice with its own reasoning: `land` uses
  the `Nat` **product** of two values in `{0,1}`, `lor` uses `max` via
  `ble` + `bool_select_nat` (a product is wrong for OR), `ldiff` uses
  `beq` + `bool_select_nat`. Pick it from the operator's truth table, not from
  the neighbouring file.

  **Asymmetric operators hand you the best negative control for free**:
  `ldiff 3 5 = 2` against `ldiff 5 3 = 4`, with an explicit assertion that the
  swapped value does NOT `def_eq`. `land`/`lor` are commutative and cannot
  offer that, which is why they use a shared numeral pair across files instead.

  A theorem *about* the definition is not a substitute. It constrains the
  definition only as far as the theorem's own content reaches, which for an
  existence statement is often not at all.

- **IF THE GOAL ONLY CONSTRAINS A BOUNDED PROJECTION OF A RECURSIVE VALUE, YOU
  DO NOT HAVE TO REASON ABOUT THE RECURSION AT ALL — AND THIS REFUTES THE
  "NEEDS A DEEP INDUCTION" SIZING INSTINCT.** Measured 2026-08-29 closing
  `Nat.even_xor`, which TWO prior sizings — a lane's handoff and `xor.rs`'s own
  module doc — called out of reach, needing machinery "well beyond defining
  xor".

  It took one unfold. The goal constrains only the **low bit** of `xor m n`,
  and that survives exactly one step of `bitwiseAux`'s recursor; the
  higher-order recursive term underneath never has to be related to anything,
  because `mod 2` erases it. Admitted axiom-free.

  So before budgeting an induction, ask: **how much of the recursive value does
  the goal actually mention?** If it is a bounded projection — a low bit, a
  parity, a residue, a head element — unfold once, erase the tail, and check
  whether the obligation is already discharged. The instinct to match the
  recursion's depth to the definition's depth is what made two independent
  readers oversize this.

  Note the shape of the counter-example this does NOT cover: `lt_xor_cases`
  stayed open in the same lane, because a highest-differing-bit statement
  mentions an **unbounded** part of the value and the technique gives no
  foothold.

- **A TRACED PLAN'S "VERIFIED NUMERICALLY" IS ITSELF A CLAIM, AND ONE OF THEM
  WAS FALSE.** The tracer/executor split — one lane writes a hand-traced,
  Python-checked plan and deliberately writes no code, the next executes it —
  closed this repository's two hardest bitwise targets and three successive
  totient refinements. Its stated strength is that every non-obvious step is
  checked numerically first.

  Measured 2026-08-30: a plan asserted a `count_range_row_major` identity was
  coprimality-INDEPENDENT and "verified numerically at non-coprime pairs
  (4,6),(6,9)". It is false at **26 of 26** non-coprime pairs with
  `1 <= m,n <= 9` — the smallest counterexample is `m = n = 2`, where
  `totient(4) = 2` against `totient(2)*totient(2) = 1`. The identity is exactly
  CRT bijectivity and needs `gcd(m,n) = 1`, which that plan explicitly said was
  "not needed".

  Nothing catches this. An executor finds a *structural* error by running the
  proof — that has happened every time — but a false NUMERICAL claim survives
  until someone re-runs the numbers, and the plan's confidence is the reason
  nobody does.

  **So: re-run a plan's numeric checks, do not inherit them.** They are ten
  lines of Python and the plan already tells you which pairs to try. And when
  writing a plan, state the check you ran as a command that can be re-executed,
  not as a sentence claiming it passed.

- **NO FUEL ENCODING CAN BE A DEPENDENT RECURSOR, AND THAT PERMANENTLY DECIDES
  A WHOLE CLASS OF `ml430` MIRRORS.** Measured 2026-08-29 building
  `Nat.binaryRec`. Mathlib's (`Mathlib/Data/Nat/BinaryRec.lean:88` at the pinned
  commit `c5ea0035…`) is well-founded recursion on a `log2` measure with a
  **dependent** `{motive : Nat → Sort u}`. Ours is structural recursion on a
  fuel counter with a motive **constant in `n`**, plus an extra fuel argument
  whose recursive equation must be *proved* rather than obtained definitionally.

  **The non-dependence is FORCED, not a shortcut.** A fuel-exhaustion row has to
  return a value for an arbitrary `n`, and the only thing in hand at that point
  is `motive 0`. So no amount of care makes a fuel encoding into Mathlib's
  construction.

  **CORRECTION, SAME DAY: I GENERALISED THIS TOO FAR AND IT IS FALSE.** I wrote
  that "any `ml430` mirror whose Mathlib definition is `WellFounded.fix` with a
  dependent motive stays open on this route, however much infrastructure gets
  built." **This kernel HAS `WellFounded.fix.{u,v}`** — universe-polymorphic,
  with a checked `WellFounded.fix_eq` unfolding theorem (`prelude.rs:215`) —
  and it is already used by `gcd`, `bezout_witnesses`, `modeq` and `wilson`.
  A lane closed `F:ml430-nat-base-induction` with it on 2026-08-29, against a
  genuine `P : Nat → Prop` motive parameter.

  What is true is only the narrow claim: **a FUEL encoding's non-dependence is
  forced.** The `binaryRec` lane chose fuel; it was not obliged to. So
  `F:ml430-nat-fastfib-eq-cde11774` is **not permanently blocked** — it is
  blocked on a `binaryRec` built the well-founded way rather than the fuel way,
  which is ordinary work, and the content landed as local facts in the
  meantime.

  This is the standing "do not generalise a lane's local finding" failure in
  its purest form: the lane reported accurately on *its own construction*, and
  I promoted that into a claim about the whole route. Before writing "cannot be
  done here", check whether the kernel already has the primitive. This is the `multichoose`/`minFac` side of the
  mirror-flip criterion, arriving from the recursion principle rather than from
  the algorithm.

  Also measured there, and general: **`Prod` does not exist in this kernel.**
  The complete inductive list is `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/
  Decidable` + `Nat.le` + `Nat.Fin` + `Char` (plus `Nat.Pair`, added by that
  lane). Every other `Prod` hit is a test fixture or a doc comment recording its
  absence. The prelude's standing workaround for a pair is a **`Bool`-selected
  function** (`Nat.xgcdAux (sel : Bool)`, `Nat.divModState`, `creal/ivt.rs`'s
  `Bool → CReal`) — deliberate, and documented at those sites.

  One defect that class of work reliably produces, invisible to `cargo check`:
  `NatOps::congr` states its conclusion at `Nat`, so rewriting a component of a
  value in ANOTHER type gives `expected: AxNat, got: AxNat.Pair`. The fix is a
  `congr_nat_to` keeping the hypothesis at `Nat` and moving only the motive's
  body. Anyone building over `Nat.Pair`, `Nat.Fin` or `CReal` will hit it.

- **THE DEV-HELPER LAYER HARDCODES A CARRIER, AND EVERY CROSS-CARRIER USE FAILS
  AS ONE OPAQUE `TypeMismatch` ACROSS THE WHOLE SUITE.** Three separate lanes
  hit this on 2026-08-29, in three different helpers:

  - `NatOps::congr` states its conclusion at `Nat`, so rewriting a component of
    a value in another type gives `expected: AxNat, got: AxNat.Pair`. The
    `Nat.Pair` lane needed a `congr_nat_to` that keeps the hypothesis at `Nat`
    and moves only the motive's body.
  - The same defect for `Bool`: the `xor_assoc` lane had to build
    `congr_bool_to_nat` for exactly the same reason.
  - `IntDev::irefl` is the **Int-typed** `Eq.refl`. Applied to a `Nat`-sorted
    term it made EVERY `int_prelude` test fail with one `TypeMismatch`; the fix
    was `d.refl`, the `NatOps` trait's Nat-level reflexivity.

  None of the three is visible from the call site — the helper name says
  `congr` or `refl`, not `congr_at_Nat`. **Before using a dev helper on a term
  whose carrier is not the module's own, check what carrier the helper states
  its conclusion at.** A tiny `expected` `ExprId` (single digits) means the
  kernel wanted a SORT; a mismatch between two large ids in a module that only
  touches one carrier usually means this instead.

  All three were isolated the same way, and it is the standard move: a
  throwaway `#[cfg(test)] mod debug_probe` built against a prelude with the new
  declarations disabled, running `Kernel::infer` on each intermediate. Five
  lanes used it that day rather than reading a poisoned-prelude failure across
  every test in the suite.

- **A PRELUDE CAN DECLARE INTO ANOTHER PRELUDE'S NAMESPACE, SO "IS THIS NAME
  TAKEN?" IS NOT ANSWERED BY READING THE MODULE IT BELONGS IN.** Measured
  2026-08-25: a lane built an explicit inverse for a bijection on `[0,n)` and
  named it `Nat.inverseIndex`. That name was already owned by
  `int_prelude/wilson.rs`, which declares `Nat.inverseIndex` and eight lemmas
  about it into the **`Nat`** namespace from the **Int** prelude — the modular
  inverse index from Wilson's theorem, an unrelated function.

  Three things made it expensive, and they compound:
  - Nothing in `nat_prelude/` mentions the name. The lane was told to check for
    an existing inverse, did, and looked where the code lives.
  - **The nat prelude builds fine alone.** `cargo test --lib nat_prelude::` was
    **66 green with the collision present.** It fires only once a downstream
    prelude builds on it.
  - The message names neither the string nor either site: `the Int model must
    build: DeclarationExists { name: NameId(457) }`, across **230** failures in
    `arith_model` and `characterization`, none of which mention `Nat` or the
    file that added it.

  So before naming a declaration, check the **whole** inventory
  (`prelude_theorem_inventory --include-constructed`, `--release`), not the
  module you are writing in. And note the asymmetry when you find a clash: the
  older declaration is usually load-bearing elsewhere, so rename the NEW one.

- **TWO LANES ADDING FUNCTIONS TO ONE RUST FILE PRODUCE A CONFLICT WHERE
  "KEEP BOTH SIDES" SILENTLY DOES NOT PARSE.** The conflict looks purely
  additive — no line is changed by both — so concatenating the sides is the
  obvious resolution and it is wrong. Git's hunk boundaries cut **mid-item**:
  each side ends with a dangling

      pub(super) fn declare_something(

  whose parameter list is the shared context *after* the hunk, because that
  boilerplate is byte-identical on both sides and the differ aligns on it.
  Measured 2026-08-25 in `nat_prelude/finite_set.rs` — three `mismatched
  closing delimiter` errors — and again in `nat_prelude_tests.rs` with two
  `#[test] fn` bodies. **`-X patience` does not fix the alignment.** Reordering
  the sides does not either: there is one shared tail and two dangling
  signatures.

  The tell is **delimiter balance per hunk side**, and it must count parens and
  brackets, not just braces — the real failure dangled an open paren.
  `scripts/lane-merge-additive.py check <file>` reports it and exits 1;
  `… splice <file> --theirs <ref> --anchor <text>` reconstructs instead, lifting
  whole items out of the other branch's own file by brace matching. It strips
  line comments first, because this repository's doc comments are full of
  `[0,n)` and [`Self::foo`] links that are deliberately unbalanced.

  Two things `splice` does NOT do, and both have bitten: it moves item bodies
  but **not their call sites** (wire each `declare_*` into its dispatcher
  yourself), and it replaces the whole file, so **name-list and pin edits from
  the other side are lost** — re-derive them, and recompute the pin by
  **counting** the lists.

  **THREE things, and the third SILENCES A TEST WITH EVERY COUNT STILL GREEN.**
  `--anchor` inserts the spliced items immediately before the matching text, so
  an anchor naming an item's **`fn` line** puts them *between* that item's
  `#[test]` attribute and the function it decorates. Measured 2026-08-29:
  anchoring on `fn clog_computes_and_its_boundary_equations_apply(` bound
  `clog`'s `#[test]` to `land_bit`'s function, duplicated `land_bit`'s own
  attribute, and **one test silently never ran**.

  `cargo test` reported a healthy nonzero count throughout — the count is the
  check this repository leans on hardest, and it cannot see this. Only
  `clippy -D warnings` surfaced it, incidentally, in a sibling lane's tree.

  So: **the anchor must sit ABOVE the item's attributes and doc comment**, not
  on its `fn` line — anchor on the first line of the preceding item's doc
  block, or on a `#[test]` you intend to precede. And after any splice into a
  test file, run the affected tests BY NAME and confirm `1 passed`, never
  `0 filtered out`. A `#[test]` separated from its function is invisible to
  every count-based check there is.

- **A NEGATIVE CONTROL MUST DIFFER IN A *SMALL* TERM, or the control itself is
  the pathology.** Measured 2026-08-27. A lane's control transposed two whole
  `riemannSum`s in a conclusion and asserted `!Kernel::def_eq` for
  non-vacuity. Both sides are then FAILING defeq checks across different
  endpoints, which forces full unfolds of `sumRange`'s `Nat.rec` over a symbolic
  `succ m`: **>300 s and RSS 2.0 -> 3.1 GB with no sign of stopping**, against
  **34.9 s** for the positive check on the identical proof term. A *failing*
  defeq is unbounded in a way a succeeding one is not -- there is no early exit.

  The replacement varies only the term count in the bound (`ofNat m` vs
  `ofNat (succ m)`), leaving the left-hand side the identical `ExprId`. Equally
  discriminating (false at `m := 0`) and free. This pairs with the standing rule
  that a pathological test is worth deleting rather than debugging: here the
  pathology was in the *control*, not the subject.

- **`UnboundFVar` NAMES NOTHING, AND THE FIX IS A TREE-WALK YOU CAN WRITE IN ONE
  FUNCTION.** `pi_fv` versus `d.arrow` is a recurring trap: a hypothesis whose
  fvar the CONCLUSION mentions must bind with `pi_fv`, because `arrow` is
  non-dependent and leaves the variable free. The kernel then rejects with a
  bare `UnboundFVar` that names neither the binder nor the offending hypothesis.

  Measured 2026-08-27 on `integral_by_parts`: **five of seven** hypotheses were
  wrong, each referenced by value inside the conclusion's embedded integral and
  uniform-continuity witnesses. Rather than bisecting, the lane wrote a
  **temporary tree-walk that scanned the built term for free-variable leaks
  before calling `add_declaration`**, which pinpointed all five in ONE run; it
  then removed the diagnostic and the second attempt succeeded.

  Do that instead of bisecting. The scan is cheap, it is exhaustive where a
  bisect is serial, and it turns an error that names nothing into a list of
  exactly which binders are wrong.

- **A SORT ERROR ARRIVES WEARING A `TypeMismatch`'s CLOTHES, and the tell is a
  tiny `expected` id.** Measured 2026-08-27: a constant function built with a
  `CReal` binder where `sumRange` needs `Nat -> CReal` reported
  `TypeMismatch { expected: ExprId(3), got: ExprId(1503219) }` -- naming neither
  the lambda nor `sumRange`. **A sort lives at a single-digit `ExprId`**, so an
  `expected` in the low single digits means the kernel wanted a SORT and you
  handed it a term (or the binder's domain is wrong), not that two elaborate
  types disagree. Check the binder before diffing the types.

- **`cargo test --lib 'filterA filterB'` RUNS ZERO TESTS AND EXITS 0.** The
  second word is parsed as a positional the harness does not use, so nothing
  matches. Same green-looking nothing as the feature-gated-suite trap, from a
  quoting slip rather than a missing flag. **Confirm a NONZERO count**, always.

- **Tools in this repo have lied more often than the solver has been weak.**
  In one session: a corpus gate that ran zero tests for 15 days while exiting 0;
  a pre-push hook that had never run because `core.hooksPath` was unset; a
  `DIRTY WORKTREE` stamp that fired on the harness's own side effects; a
  reference-solver smoke probe blind to a 1000× budget-unit error; an error
  message naming a node cap when the real cause was an i128 overflow; and a doc
  comment claiming a witness binds "every declared String variable" when it
  binds the source problem's private symbol ids. Prefer a measurement over a
  message, an exit status, or a comment — including the ones you just wrote.
- **THE LEMMA YOU NEED USUALLY EXISTS, AND THE NAME SEARCH WILL NOT FIND IT.
  THREE DISTINCT HIDING PLACES, ALL MEASURED 2026-08-27.** Four lanes in one
  session reported their blocker already solved, in three different ways. The
  common cost is not the rebuild -- it is that each lane first *sized* the work
  as new, and two nearly built a duplicate.

  1. **General infrastructure filed under its first consumer's module.**
     `CReal.bucketIndex` (a computed index on the unit-fraction grid, with four
     clamp lemmas) lives in `creal/uniform_continuity.rs` because a covering
     argument needed it first. It is now consumed by `crossing.rs`,
     `integral.rs` and `sqrt.rs`. A lane sent to build an Archimedean crossing
     index found it in step 0 and reduced its whole task to a rescaling.
  2. **A reusable step built INLINE inside a larger declaration and never
     exposed.** `nat_prelude/powsq.rs`'s `declare_pow_half_split` builds a full
     `Nat` even/odd split (`e_eq_final`, twice -- once per branch) purely as
     scaffolding toward a `pow` equation. Nothing named it. A lane sent to build
     `Nat.even_or_odd` extracted it instead of re-deriving it. The same shape
     blocks the Weierstrass M-test today: `converges_of_scaled_cauchy`
     (`creal/convergence.rs:1356`) performs the `Within` -> CReal `close_within`
     step internally via `speedup_close` + one `Rat.natDivSucc_add` fusion, and
     the only PUBLIC lemma of that shape, `within_of_two_sided_le`, runs the
     **opposite direction**.
     <!-- was-absent: CReal.weierstrassMTest, CReal.close_within_of_within -- the claim above is historical; `scripts/check-absence-claims.py` (ADR-0611) fails if either is ever removed, and had this carried an `absent:` marker it would have gone red the day they landed instead of costing two lanes -->
  **CORRECTION, 2026-08-27: the M-test example above is STALE, and it cost two
  lanes.** `CReal.weierstrassMTest` was landed in full generality
  (`creal/uniform_convergence.rs`, commit `1d08388a3`), along with
  `CReal.close_within_of_within` — which solved the `Within` -> `close_within`
  step NOT by extracting `convergence.rs`'s private helper as the text above
  speculates, but by an independent route through the already-public
  `sample_upper_bound`/`sample_lower_bound`. The coordinator read the stale text
  as a live blocker and dispatched a lane at a finished task.

  It happened TWICE in one hour. The same coordinator logged a deficiency
  asserting `Rat.sumRange` had no diagonal/rectangle reindexing and dispatched an
  Opus lane; `rat_prelude/diagonal.rs` already carried it, AND `complex.rs`
  already ran the same argument over ℂ including the two-bound form that
  `diagonal.rs`'s own module doc called missing.

  **So the rule this section states for LANES applies to whoever writes the
  brief, and more sharply**, because a brief multiplies the error by the lane it
  dispatches: **verify a blocker still exists in the tree before treating it as
  one — including a blocker this file names.** A file that records obstacles
  accumulates stale ones by construction, and its authority is exactly what makes
  them expensive. Cheap check, and the only one that works: grep the tree for the
  declaration, with a positive control of the same kind.

  3. **A lemma whose stated hypothesis is WEAKER than everyone assumes.**
     `CReal.sumRange_cauchy_of_dominated` is `∀ f g, (∀ k, le (abs (f k)) (g k))
     → …` -- it never required `f` nonnegative, so it **already covers signed
     series** and the separate absolute-convergence bridge is unnecessary for
     that purpose. TWO lanes discovered this independently, both against a brief
     that asserted the opposite. Read the signature, not the surrounding prose.

  5. **THE SAME MODULE NAME EXISTS IN TWO PRELUDES, AND EVERYONE CHECKS THE
     WRONG ONE.** Measured 2026-08-29. Three successive totient triages, plus a
     brief I wrote pointing at it explicitly, all looked at
     `int_prelude/crt.rs` and concluded the Chinese Remainder machinery did not
     transport to a `Nat` counting argument. **`nat_prelude/crt.rs` also
     exists** — Nat-native, 17 KB, with `Nat.crt_unique` — and it transports
     directly. Combined with the existing pigeonhole
     (`injective_on_imp_surjective_on`) it gives the residue-pairing map's
     bijectivity with no Bezout witness at all.

     Two files, same basename, different preludes. `ls src/*/crt.rs` would have
     shown both in one command, and nobody ran it because everybody already
     "knew" where CRT lived. The same pair exists for `parity.rs`, `gcd.rs`,
     `division.rs` and others.

     **When a module you need is named for a mathematical topic rather than a
     carrier, check EVERY prelude for that basename before concluding anything
     about transport.**

  6. **THE SAME ARGUMENT OVER A DIFFERENT AGGREGATE IN A DIFFERENT PRELUDE.
     This one defeats BOTH retrieval tools, which is why it is worth its own
     entry.** Measured 2026-08-30. A lane needed "counting over `[0,n)` is
     invariant under an injective self-map" and `320`'s triage had searched
     `permutation.rs`, `cardinality.rs` and `subset_product.rs` and correctly
     found nothing. The answer was **`Int.prodRange_permute`**, which had
     existed since Wilson's theorem: same induction, same
     `restrict_injective`/`restrict_maps_into` helpers, reusable skeleton --
     but over the **product** aggregate in the **Int** prelude.

     A name search misses it (nothing says `countRange`). `shape_search` misses
     it too, and that is the point: its conclusion head is `AxInt.prodRange`,
     so no `--concl AxNat.countRange` query can reach it. The only thing that
     finds it is recognising the PROOF SKELETON, which no index we have
     represents.

     So when a triage reports a permutation/reindexing/invariance lemma absent,
     **ask which other aggregates this development folds over** (`sumRange`,
     `prodRange`, `countRange`, `maxRange`) and **in which other preludes**, and
     read the one that is furthest along rather than the one that matches your
     carrier. Not everything transports -- that lane deliberately did NOT copy
     `prodRange_swap`'s adjacent-transposition machinery, because counting
     accumulates with `Nat.add` and a single point-change lemma replaced the
     whole apparatus -- but the skeleton did.

  4. **THERE IS NO SINGLE SPELLING, so grep fails even when you DO know the
     name.** The kernel name is `CReal.congrOfUniformlyContinuous`; the Rust
     prelude field, the design docs, every brief and this file all say
     `congr_of_uniformly_continuous`. Measured 2026-08-27 over 447 `CReal`
     declaration names: **315 carry an underscore, 225 an internal capital, and
     117 carry BOTH.** So a lane grepping the spelling it read in a doc misses
     the declaration, and a lane grepping the kernel spelling misses every Rust
     call site. This is not a naming inconsistency to clean up -- the two
     conventions serve different layers -- it is a retrieval hazard to route
     around. `shape_search --name-like <either spelling>` normalizes; grep does
     not.

  **The technique that works: search for the STEP, not the NAME -- and there is
  now a tool for it (ADR-0608).** `examples/shape_search.rs` indexes **every**
  declaration kind by conclusion head, per-hypothesis head and type constants
  (1,838 declarations, ~13-21 s), and **fails on absence** with exit 1, printing
  a same-kind positive control; exit 3 means *unanswerable*, deliberately
  distinct. The canonical miss returns exactly one row from shape alone:

      cargo run --release -p axeyum-lean-kernel --example shape_search -- \
        --include-constructed --concl CReal.Equiv \
        --hyp CReal.UniformlyContinuousOn --hyp CReal.Equiv

  Failing that, grep for the shape of the intermediate you need -- an index
  computation, a case split, a direction of transport -- across the whole crate,
  not for what you would have called the finished lemma.

  **A STALE PREBUILT `shape_search` REPORTS A FALSE ABSENT, which is the one
  failure this tool exists to prevent.** It indexes the declarations its own
  binary was compiled against, so `target/release/examples/shape_search` left
  over from an earlier build answers about an OLD environment. Measured
  2026-08-27: a prebuilt copy in the shared checkout reported **1,845**
  declarations against a current **1,850**, and did not know `CReal.integral_abs_le`
  -- a declaration that had landed hours earlier. Harmless for an old lemma;
  for a RECENT one it says ABSENT, exit 1, with a perfectly convincing
  same-kind positive control beside it.

  This is the general prebuilt-binary hazard (`target/release/examples/` takes
  no cargo lock and is the right tool for measurement under contention) meeting
  the one question where a wrong negative is expensive. **Before trusting an
  ABSENT verdict, check the `declarations=` count in the coverage line against a
  fresh build, or rebuild.** A FOUND verdict needs no such care -- a stale index
  cannot invent a declaration.

  **AND A STALE BINARY CAN PRODUCE A CONFIDENT *POSITIVE* THAT IS ALSO WRONG,
  WHICH THE "FOUND NEEDS NO CARE" RULE ABOVE DOES NOT COVER.** Measured
  2026-08-29: a stale prebuilt dumper emitted a **96 MB** Lean module for a
  trivial `14x + 21y = 5` refutation. That binary predated
  `reconstruct::MAX_LEAN_MODULE_BYTES`, so it produced the giant string where
  the current code *declines* and exits 1 with zero bytes. The 96 MB number was
  real output from real code -- just not the code in the tree.

  It then survived two hops: a lane reported it, I wrote it into a brief as
  "over the checker's 64 MB safety cap", and the cap is not the checker's at
  all. The lane that finally measured it had to correct both the size story and
  whose cap it was.

  So the rule generalises past ABSENT verdicts: **a stale binary's output
  describes an older tree in every direction -- absent, present, and how big.**
  When a measurement will be quoted, rebuild or check freshness first, and when
  a number seems implausible for the input, suspect the binary before the
  algorithm. `--include-constructed` inventories are useless
  here for case 2 by construction: an inline step has no name to list.

  And note the asymmetry when you find one: extracting an inline step into its
  own declaration is cheap and reusable; **re-deriving it beside the original
  leaves two proofs of one fact that must stay in sync while the kernel happily
  verifies both.** That has already happened once this session, with six private
  helpers copied verbatim rather than reported.

  **PROSE HAS NOT FIXED THIS, AND THE COUNT KEPT CLIMBING AFTER THIS SECTION WAS
  WRITTEN.** Every brief in the 2026-08-27 session repeated "search for the STEP,
  not the NAME", and lanes still reported reaching **thirteen** instances, with
  more landing the same day: `CReal.equiv_of_le_le` and
  `CReal.equiv_zero_of_small` were both budgeted as new work in a Fermat brief
  and both already existed.

  The most expensive was `CReal.congr_of_uniformly_continuous`, which stalled a
  whole rung of `supOn`. A lane needed exactly it, searched
  `creal/uniform_continuity.rs` -- the module where it BELONGS -- found nothing,
  and stopped. It lives in `creal/integral.rs:17010`, because
  `riemann_sum_split_exact_of_uc` consumed it first. **The search was competent
  and its answer was correct**; you cannot find by name a thing whose name you do
  not know. (Nor can it be strengthened to a global
  `∀ x y, Equiv x y → Equiv (F x) (F y)` -- that form is FALSE for an arbitrary
  witness, since `UniformlyContinuousOn` says nothing about `F` outside `[a,b]`.)

  Because instruction demonstrably does not close it, it is logged as a
  first-class TOOLING deficiency in
  [`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`](docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md),
  with shape-indexed retrieval over `kernel.environment()` dispatched against it.
  Two things that write-up is careful about, and you should be too: the thirteen
  is a **lane-reported tally that has not been independently audited**, and any
  name index is **structurally blind to hiding place 2** -- an inline step has no
  declaration to index, so no such tool can ever reach it.

  Retrieval is one of the three gates on marginal cost per theorem named in
  `docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
  (contracts, retrieval, sharding). On this evidence it is the binding one:
  **more lane-hours went to re-deriving what existed than to proof difficulty.**

- **An empty result from a tool that was never pointed at your subject is
  indistinguishable from a strong negative result.** Distinct from the inert-gate
  trap above: the tool runs, exits 0, and prints a correct empty answer to a
  question you did not ask. `prelude_axiom_inventory` builds the `real`,
  `integer` and `string` preludes and never `nat` or `logic`, so grepping its
  output for Nat rows returns nothing — which the coordinator read as "the Nat
  prelude is axiom-free" and put into two agent briefs before checking. The
  conclusion happened to be true; the evidence for it did not exist. Before
  believing a zero, confirm the tool's COVERAGE includes your subject, not just
  that it ran. (`nat_axiom_inventory` now covers `nat`/`logic` and the full
  trusted surface — `Axiom` alone is not it, since `Opaque` has no proof body and
  `Quotient` admits `Quot.sound`.)
- **`prelude_theorem_inventory` MUST BE RUN `--release`. In debug it SIGABRTs,
  and that looks like a broken tool or an absent subject.** This is the
  repository's primary instrument for reading theorem counts and axiom
  footprints, so agents reach for it constantly. Measured 2026-08-24 on the same
  tree, same flags, same moment:

      cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory \
        -- --include-constructed   ->  exit 0, 3,924 rows
      cargo run           -p axeyum-lean-kernel --example prelude_theorem_inventory \
        -- --include-constructed   ->  exit 134, "has overflowed its stack"

  Building the full constructed environment recurses deeply through
  `Kernel::add_declaration`, and the debug build's larger stack frames blow the
  default thread stack. **Nothing is wrong with the kernel or with any term** —
  it is a resource limit wearing a crash's clothes, the same one that makes
  `complex_tests.rs` and `creal_point_tests.rs` carry `on_a_deep_stack` helpers.

  A lane hit this and reported the inventory as "stack-overflows unrelated to
  this work", which is a reasonable reading and a wrong one: it had simply
  omitted `--release`. The failure mode that matters is the quieter one — an
  agent runs the debug form, gets no rows, and concludes a declaration is
  ABSENT. That is the coverage trap below, with the tool broken rather than
  misaimed.

- **`theorem_dependency_inventory` CONSUMES ONLY ITS FIRST NAME ARGUMENT AND
  SILENTLY IGNORES THE REST — a three-name call reads as success.** Measured
  2026-08-29 while checking seven new declarations at once. The run printed one
  row and the summary line

      1 theorems, 1 with dependencies, 1 edges

  which looks like a clean result rather than a tool that discarded six of the
  seven names it was handed. Exit 0 either way. This is the
  checker-that-cannot-fail defect in its quietest form: the output is not empty,
  not an error, and not obviously about the wrong subject.

  For a MULTI-declaration check use `prelude_theorem_inventory` with a **tested
  count**, and anchor the match on the prelude column — `complex` and `cpoint`
  re-declare every `CReal` name, so an unanchored `grep -c` over a `CReal.*`
  pattern comes out **3x** and a count-based guard passes for the wrong reason.

- **`prelude_theorem_inventory` LISTS THEOREMS, NOT DEFINITIONS — so `Nat.add`
  returns ZERO ROWS, and every construction this project is proudest of is
  invisible to it.** Measured 2026-08-27 on one inventory of 5,130 rows, each
  name matched against the whole row's second field rather than by substring:

      Nat.add  Nat.mul  Rat.polyEval  CReal.integral  CReal.e  CReal.sqrt
      Complex.conj                                        -> 0 rows EACH
      Nat.add_comm 6,  CReal.integral_const 3,  Rat.sub_mul 4   (control)

  Every one of those zeros is a `Definition` that certainly exists. The tool
  filters to `Declaration::Theorem`, which is correct for what it was built for
  and catastrophic for the question agents actually ask it: *does `X` exist?*

  **The prefix grep is what makes it dangerous, because it answers NONZERO.**
  `grep -c 'Rat.polyEval'` returns **16** — every hit a `Rat.polyEval_add` /
  `_smul` / `_succ` lemma, and not one of them the definition. So the careless
  query confirms presence, and the careful anchored query reports absence, and
  **both are wrong about the definition itself.** It bit in both directions
  within one hour: a lane recorded that no in-tree tool inventories definitions
  by name with fail-on-absence semantics (true, and it had to weaken a fact
  ledger checker because of it), and separately a coordinator grep for `Nat.max`
  came back empty and proved nothing at all, because the control — `Nat.add` —
  came back empty too.

  This is the coverage trap above with the tool **correctly aimed and answering
  a narrower question than the one asked**, which is why the usual remedy
  ("confirm the tool covers your subject") is not enough on its own. Two rules:

  - **Pair every negative with a positive control of the SAME DECLARATION KIND.**
    A theorem is not a control for a definition. `Nat.add` returning zero is the
    fastest way to tell you are asking this tool the wrong question.
  - **To ask whether a definition exists, read the environment** —
    `kernel.environment().iter()` — or the source, never a theorem inventory.

  Related and load-bearing: a fact-ledger `checker_command` asserting a
  CONSTRUCTION (`CReal.integral`, `CReal.e`) cannot use the theorem inventory as
  its discriminator; it must either name a theorem whose admission entails the
  definition, and say so, or use a checker that fails on absence for the kind it
  is actually checking.

- **`AxNat` IS NOT AN AXIOMATIZED `Nat` — the `Ax` is *axeyum*, and the prefix
  means the opposite of what it means in `AxReal`.** Every rendered type in this
  kernel prints the naturals as `AxNat`: `AxNat.sumRange`, `AxNat.injectiveOn`,
  `Eq.{1} AxNat`. That is `lean_pp`'s non-shadowing root for the kernel's
  **computational, inductive, constructed** naturals, chosen so an exported term
  does not collide with Lean's own `Nat`, and `nat` measures **0** — no `Axiom`,
  no `Opaque`, no `Quotient`.

  In `AxReal` the same prefix does mean axiomatized, and that package is this
  repository's only nonzero row at **30**. So the two names differ by one letter
  and disagree about the headline metric, and a reader who sees `AxNat` in a
  pinned type and infers an assumed carrier has axiom-freedom exactly backwards.

  The rule this generalizes: **read a carrier's trusted surface from
  `Kernel::axiom_footprint`, never from its rendered name.**
  `nat_axiom_inventory` covers `nat`/`logic`; `prelude_theorem_inventory
  --include-constructed` lists every declared name with its footprint. And note
  that `lean_pp` rewrites names on export for two reasons at once — the other is
  that a numeric component becomes `_0`, since `foo.0` parses as a projection —
  so matching display names against module text reports "not covered" for
  artefacts that are perfectly correct.

- **`AxReal` and `CReal` are different things and one is a substring of the
  other.** `CReal` is the CONSTRUCTED reals — a Bishop setoid over the
  constructed rationals, trusted surface 0 (ADR-0512) — and it is what the
  shipped route actually reasons over. `AxReal` is the legacy AXIOMATIZED
  ordered-field package, and it is the repository's only nonzero row:
  `axreal: axiom=30`. Every other prelude — `logic`, `nat`, `integer`, `rat`,
  `creal`, `complex`, `string` — measures 0.

  **The prelude key was `real` until 2026-08-19, and the rename was half-done for
  a day.** ADR-0522 renamed the declarations `Real.*` → `AxReal.*`, but the
  ledger still filed them under prelude `real`, so the table a referee reads said
  `real 30` about 30 rows all named `AxReal.…` — the label contradicting its own
  contents, and inviting precisely the reading the rename existed to prevent
  ("their reals cost 30 axioms", when the reals are `creal` at 0). Both halves
  are landed now. Do not reintroduce `real` as a prelude label; the generated
  ledger carries a paragraph saying what `axreal` is, and `EXPECTED_PRELUDES`
  in `scripts/gen-lean-axiom-ledger.py` is the list a new one must join.

  A `contains("Real.")` test matches `CReal.` too, and that has already been hit
  and worked around locally (`examples/front_door_carrier.rs:169` decides the
  carrier from the carrier DECLARATION for exactly this reason). The same hazard
  bit the ledger's own prose scanner: `real (\d+), integer (\d+), string (\d+)`
  matched inside "creal 0, integer 0, string 0" — an ordinary sentence now that
  the constructed carrier is the one at zero — and scored it against `axreal`,
  so a document stating the counts CORRECTLY would have redded the gate. Fixed
  with a `(?<![A-Za-z])` lookbehind and controlled both ways in
  `scripts/tests/test_lean_axiom_ledger.py`. Decide which package you mean by
  its declaration, never by a substring; if you must match text, anchor it.

  **Declared is not reached by the DEFAULT route, and both numbers are
  published** (ADR-0509). The 30 are declared; the default reconstruction does
  not reach them — `Lra`, `DisjunctiveLra`, `Sos` and `IntFarkas` all
  reconstruct over constructed carriers. So "we have 30 axioms" and "our proofs
  rest on 30 axioms" are both wrong: the first ignores that the shipped route
  does not reach them, the second is simply false. Quote the pair.

  **"No route reaches them" is too strong, and a lane that reads it that way
  will distrust a correct measurement.** One route deliberately does, and
  measured 2026-08-27 it is live and green:

      cargo run --release -p axeyum-solver --features full \
        --example infeasibility_farkas_lean -- \
        artifacts/instances/infeasibility/schedule-deadline.smt2 \
        --require-kernel --expect-axioms 26
      ->  kernel-lean route   REACHED (term infers to False)
          kernel axioms       26 = 17 prelude + 4 variable + 5 hypothesis
          axiom-free          no -- the ordered field and every core row are asserted

  Nothing about that is a leak, and every part of it is opt-in and loud:
  `examples/infeasibility_farkas_lean.rs:292` calls
  `LraReconstructCtx::new_over_axreal()` — a constructor NAMED for the choice it
  makes, which is ADR-0605's fix for a plain `new()` that used to make it
  silently. `prove_unsat_to_lean_module` stopped routing pure-AxReal on
  2026-08-15. The tool prints `axiom-free no` itself, and the fact
  `F:schedule-critical-chain-infeasible` publishes all 26 in its
  `axiom_footprint` with a `--expect-axioms 26` checker that fails if the count
  moves.

  The distinction to carry: **the default route reaches zero; an explicitly
  opted-in demonstrator reaches 26 and says so.** Both are true, both are
  measured, and only the pair is honest.

  The count is not a dial. `Real`'s carrier is opaque, so nothing over it is
  definable and every operation and law must be assumed — **30 is the floor for
  an axiomatized ordered field**, not a choice. The negative control every
  axiom-freedom measurement is read against is now one assumed law over a
  CONSTRUCTED carrier (ADR-0515), which is stronger, because that axiom is
  provably redundant and the 30 are only relatively consistent.
- **You cannot read the kernel's theorem inventory from source text.**
  Declarations go through a `.theorem(name, …)` helper taking an interned
  `NameId` field, so grepping `.theorem("…")` returns **zero** matches and
  `Declaration::Theorem` returns 1 against 119 real theorems. Three separate
  counts of this repository's theorems were wrong before anyone built the
  environment to look, and one lane built an out-of-tree probe crate to get types
  it could have read directly. Use the examples:
  `nat_theorem_inventory` (names + canonical types, the paste-into-a-fact form),
  `theorem_axiom_footprint` (per-declaration `Kernel::axiom_footprint`, this
  kernel's `#print axioms`), `nat_axiom_inventory` (trusted surface).
- The `z3` crate ≥ 0.20 removed the old `'ctx` lifetime API; `Solver::new()`
  takes no arguments and contexts are managed internally
  (`with_z3_context`/`with_z3_config`). Don't copy pre-0.20 examples.
- varisat is effectively unmaintained (last release 2019) but is the only
  Rust SAT solver with DRAT/LRAT proof output; treat it as a design reference
  and benchmark candidate, not a guaranteed dependency.
- The first pure-Rust SAT adapter is `rustsat-batsat` through RustSAT
  (ADR-0007). Its UNSAT results are lower-assurance until a proof-producing
  route and checker exist.
- The custom CDCL core is settled identity (ADR-0002) but its *priority* is
  gated by
  [docs/research/08-planning/benchmarking-and-performance-methodology.md](docs/research/08-planning/benchmarking-and-performance-methodology.md);
  encodings come first until SAT time dominates on real corpora. Lazy
  techniques are likewise priority-gated.
