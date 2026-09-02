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
  unfalsifiable claims at full speed. So: when you attach evidence, make the exit
  status depend on the finding; when you touch a checker, delete one guard and
  require that **exactly one** test dies. Six of seven guards in one suite were
  removable with everything still green, because they all rejected through one
  shared check. The two audits behind this rule — and why they do not share a
  denominator, so you must check the METHOD before quoting either number — are in
  [evidence-and-checker-discipline.md](docs/contributor-guide/evidence-and-checker-discipline.md).

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

**Twelve measured incidents have eaten another lane's work through the git
index, and several were caused by the fix for the previous one.** The full
history, and why each obvious remedy fails, is in
[multi-agent-worktrees.md](docs/contributor-guide/multi-agent-worktrees.md).
What you need to follow:

- **Commit with `scripts/lane-commit.sh -m <msgfile> -- <path>…`.** It takes the
  paths explicitly and refuses unless nothing staged was unnamed, nothing named
  failed to stage, and no half-rename is left behind; then it resyncs the shared
  index for exactly those paths. Every guard in it is mutation-verified against
  one real incident.

  Doing it by hand is not one rule but six, and each of the obvious ones has
  failed in production: bare `git commit` sweeps other lanes' staged files;
  `git commit -- <pathspec>` discards your own staged hunks; a private
  `GIT_INDEX_FILE` leaves a staged **revert** of your own commit behind it; a
  `read-tree` in an earlier shell invocation is already stale; and the staged-set
  assertion that catches a moved HEAD cannot catch a wrong pathspec. Read the
  doc before hand-rolling any of it.
- **`git commit -m "…"` silently deletes anything in backticks.** This repo's
  messages are full of backticked identifiers. Use a quoted heredoc:
  `git commit -F - <<'MSG'`.
- **A merge cannot use a private index**, so another lane's staged file blocks
  yours. Use a detached worktree; never `git stash` (it has corrupted a source
  file here).
- **Verify every commit with `git show --stat`** — read the FILE COUNT, not
  whether your own hunks look right.
- **After any merge touching a pinned count, RECOUNT** — two lanes can each bump
  it correctly and the clean merge still will not compile. Use
  `scripts/recount-pinned-inventory.py`; entries are not one per line.
- **Lane identity lives in the environment** — `export AXEYUM_AGENT=<lane>`.
  Never `git config axeyum.agent` in a shared checkout: it is repo-local, so the
  last writer silently renames every other lane's commits.
- **Never** `git stash`, `git checkout`/`restore` on files you did not modify,
  or any history rewrite — another lane's uncommitted WIP lives in this tree.
  Treat dirty files you don't own as off-limits.
- Format single files with `rustfmt --edition 2024 <file>` — never
  `cargo fmt`/`cargo fmt -p` (workspace-wide; clobbers other lanes' WIP).
- **Never mutation-test in the shared worktree.** Your mutant is on disk for
  every other lane's build, and the failures it causes look like their bug. Use
  `scripts/tests/mutation_controls.py` (it copies to a scratch root) or
  `scripts/lane-snapshot.sh`.
- **From a worktree, an absolute path under the main checkout silently edits the
  main checkout.** Use relative paths, or prefix with your own worktree root.
- **The session scratchpad is shared by every lane in the session.** Name files
  per lane (`$AXEYUM_AGENT.W`, not `W.txt`); prefer passing paths in a variable
  over persisting them to a file.
- **Push with `scripts/lane-push.sh`, and never start a second push.** It
  refuses with exit 75 when another is running and prints the cost first; two
  concurrent pushes took 5,510 s and 9,876 s, most of it blocked silently on a
  flock. Batching commits makes the hook's early exit fire LESS often, not more.
- **Heavy cargo goes through `scripts/cargo-serialized.sh <cargo args…>`.** Two
  dev boxes have been taken down by concurrent lane builds and a kernel OOM
  killed a live agent session. It holds a host-wide `flock` and runs the job in a
  scope carrying **both** `MemoryMax` and `MemorySwapMax` — a memory ceiling
  without a swap ceiling is decoration, verified by its own `--self-check`, which
  you should run **per host**. Exit 75 means the lock timed out.
- **When merging, run `scripts/check-merge-hygiene.sh`** (~2s): duplicate ADR
  numbers, conflict markers, and stale generated files have each reached a commit
  through this gap. **An ADR number is a shared allocation point** — when
  briefing a lane, name a specific number well above the current maximum.
- **Two lanes adding functions to one Rust file produce a conflict where "keep
  both sides" silently does not parse.** Use `scripts/lane-merge-additive.py`;
  note it moves item bodies but not call sites, and an `--anchor` on an item's
  `fn` line will separate a `#[test]` from its function — which every count-based
  check is blind to.
- One writer per worktree/area at a time; long-running background gates are
  run FOREGROUND by the agent that owns them (waiting on completion
  notifications has stalled agents repeatedly).
- Full details:
  [multi-agent-worktrees.md](docs/contributor-guide/multi-agent-worktrees.md)
  (the model and the index-hygiene history) and
  [multi-agent-operations.md](docs/contributor-guide/multi-agent-operations.md)
  (the operating discipline and lane dispatch).

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

**This section is a trigger index, not the record.** Each line is enough to
recognize a situation you are already in; the measurement, the incident history
and the worked fix live in the linked document. The rule underneath all of them:

> **Before believing a result, ask what the command would print if it were
> broken. If that is what it just printed, it is not evidence.**

Tools in this repo have lied more often than the solver has been weak — a gate
that ran zero tests for 15 days while exiting 0, a pre-push hook that had never
run, an error naming a node cap when the cause was an i128 overflow. Prefer a
measurement over a message, an exit status, or a comment — including ones you
just wrote.

### Before you build anything: does it already exist?

**More lane-hours have gone to re-deriving what existed than to proof
difficulty.** Thirteen-plus measured instances. A name search does not find it,
because you do not know the name — and there is no single spelling (315 of 447
`CReal` names carry an underscore, 225 an internal capital, 117 both).

- Run **`just brief <target…>`** first. It is step 0 of a brief and belongs to
  whoever WRITES the brief, not to the lane.
- Search for the **STEP**, not the NAME: `examples/shape_search.rs`.
- A **stale prebuilt binary reports a false ABSENT** — check the `declarations=`
  count against a fresh build before trusting absence.
- Three hiding places, one of which no tool can reach (an inline step has no
  declaration to index).
- **A handoff's "blocked on X" is a claim about one route, and reliably
  pessimistic.** Verify each named prerequisite in-tree.
- **Verify a blocker still exists before treating it as one — including a
  blocker this file names.** A file that records obstacles accumulates stale
  ones by construction, and its authority is what makes them expensive.

→ [Finding Existing Lemmas](docs/contributor-guide/finding-existing-lemmas.md)

### Kernel: the declaration is rejected, or admitted and wrong

**The trusted gate cannot tell you a `Definition` is wrong.** It type-checks; a
function computing the wrong value has the right type. **Every new `Definition`
needs an evaluation test** at concrete arguments, with discriminating arguments
and small magnitudes.

- **Instantiate concretely AND check symbolically** — the two catch disjoint
  defect classes, and self-consistent errors defeat per-step symbolic checks.
- **`Nat.add`/`Nat.mul`/`Nat.choose` recurse on their RIGHT (or first) argument.**
  Symbolic side LEFT, literal RIGHT. This decides which equations are `refl` and
  which variable a case tree must split on.
- **A recursor on a bare free variable is stuck** — it fails by not reducing.
- **`le_congr` takes the PRE-substitution type**; `Equiv` and `le` are different
  props. Eleven rejections in one session from this family.
- **`UnboundFVar` names nothing** — write a tree-walk over the term, do not
  bisect. **A tiny `expected` `ExprId`** (single digits) means the kernel wanted
  a SORT, not that two types disagree.
- **Dev helpers hardcode a carrier** (`NatOps::congr`, `IntDev::irefl`); a
  cross-carrier use fails as one opaque `TypeMismatch` across the whole suite.
- **A prelude can declare into another prelude's namespace** — check the whole
  inventory before naming, not the module you are writing in.
- **`AxNat` is not axiomatized** (`Ax` is *axeyum*); **`AxReal` ≠ `CReal`**, and
  one is a substring of the other. Read a trusted surface from
  `Kernel::axiom_footprint`, never from a rendered name.
- **A fuel encoding's non-dependence is forced** — but this kernel HAS
  `WellFounded.fix`, so do not generalize that to "cannot be done here".

→ [Kernel Proof Engineering](docs/contributor-guide/kernel-proof-engineering.md)

### Kernel: it builds, but slowly (or blows the stack)

A slow prelude blocks every lane's gate. **Bisect; do not theorise** — three
attributions for one slow build were propagated in briefs before anyone measured.

- **Run it in `--release` first** (debug frames cost up to 32x), then
  `check-kernel-stack-envelope.sh --measure`. Release-failure does NOT prove
  non-termination — a bounded requirement can simply have grown.
- **Bisect WITHIN the declaration**, leg by leg.
- **Every `Nat` numeral here is unary**, so the binary literal fast path never
  fires. Cost is superlinear in the largest magnitude FORMED. Keep magnitudes
  small; a global numeral change is measured at zero.
- **Relating a `Definition`'s value to one you rebuilt forces a full unfold** —
  route through the theorem that already names it.
- **A concrete witness can cost more than a symbolic one.** Build generically
  over a bound variable, substitute concretely only at the end.
- **One bad declaration poisons the shared build**, so the failure count says
  nothing about how many things are broken. Bisect by toggling declarations.
- **A pathological test is worth deleting** — say so and move on. This includes
  a pathological *negative control*: it must differ in a SMALL term.

→ [Prelude Build Cost](docs/contributor-guide/prelude-build-cost.md)

### Measuring anything

- **Banned shell idioms**, each of which printed a wrong answer reported as
  fact: `echo "exit=$?"` after a pipeline; `grep -q` under `pipefail`;
  `grep -B1` for commit trailers; testing a grep pattern interactively (`grep`
  is ugrep in your shell, GNU grep in scripts — they disagree on `\t`, and 68
  fact checkers were wrong because of it); an empty grep as a negative result;
  fixed-name scratchpad files; a "did it finish?" check never shown to fire.
- **Confirm a NONZERO test count.** A feature-gated suite compiles to nothing
  and exits 0. `cargo test --lib 'filterA filterB'` runs zero tests and exits 0.
- **`prelude_theorem_inventory` must be run `--release`** (debug SIGABRTs) and
  **lists theorems, NOT definitions** — `Nat.add` returns zero rows. Pair every
  negative with a positive control **of the same declaration kind**.
- **`theorem_dependency_inventory` and `nat_theorem_inventory` silently discard
  all but one name argument, and keep opposite ends.** One name per invocation.
- **An empty result from a tool never pointed at your subject** is
  indistinguishable from a strong negative. Confirm COVERAGE, not just that it
  ran.
- **A stale prebuilt binary describes an older tree in every direction** —
  absent, present, and how big.
- **A hand-rolled Python mutation loop reports the previous mutant's result**
  (`__pycache__` keys on whole-second mtime + size). Use
  `scripts/tests/mutation_controls.py`.
- **A background task reported as exited may still be running** and taxes every
  timing measurement. Check `ppid==1` before trusting a load-sensitive number.
- **A test passing only under an ambient env var is a gate on one shell.**
  Verify with `env -u <VAR>`.
- **`command -v lean` returns nothing on a host that HAS Lean** (elan does not
  touch `PATH`). Run `scripts/provision-lean-import-toolchain.sh --verify`
  before concluding a host cannot do Lean work.
- **`explain_corpus` is not an oracle** — it disagrees with the shipped front
  door on 134 of 397 benchmarks.
- **`cargo-serialized.sh` takes a host-wide flock**, so a timing run measures
  the queue. Wrapper for CORRECTNESS, prebuilt binary for MEASUREMENT.

→ [Measurement Hazards](docs/contributor-guide/measurement-hazards.md)

### Evidence, checkers, and blind populations

- **Make the exit status depend on the finding.** When you touch a checker,
  delete one guard and require that **exactly one** test dies.
- **A test named "every X" must derive its X from the authority, not a
  literal** — otherwise it measures the maintainer's memory. One such test
  found twelve unchecked declarations on its first honest run.
- **Mutation testing measures the guards you HAVE, never the ones you are
  missing.** For every case the PRODUCER distinguishes, write an adversarial
  fixture over a SATISFIABLE query; if the certificate cannot express the
  distinction, that impossibility is the finding.
- **A certificate must carry every distinction its producer makes.**
- **An operation registry where every entry names one target is a dispatch
  table, not a producer**, and cannot fail to "produce".
- **A traced plan's "verified numerically" is itself a claim** — re-run its
  numbers, do not inherit them. One was false at 26 of 26 pairs.
- **A blind evaluation population is a shared resource with no owner.** Touching
  one member spends the whole family; check the PARTITION, never the count. When
  unblocking a held-out family, declare the construction and **not** theorems
  about it.

→ [Evidence and Checker Discipline](docs/contributor-guide/evidence-and-checker-discipline.md)

### Dispatching lanes

- **Pass `isolation: "worktree"` for any lane that will WRITE**, and never
  assert isolation in a brief you did not provide. `git worktree list` is the
  check, not the presence of a directory.
- **Do not ask a lane to run `cargo test`.** It is duplicated work that gates
  nothing and is the largest source of stalls. Require an EARLY commit instead.
- **Write a constraint as an OUTCOME, not a mechanism** — "do not defer the
  answer by ANY mechanism, and report an unfinished check as 'did not run'".

→ [Multi-Agent Operations](docs/contributor-guide/multi-agent-operations.md)

### Reference-solver notes

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
