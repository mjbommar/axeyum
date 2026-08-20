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

- **`explain_corpus` can print a WRONG VERDICT. Never use it as an oracle.**
  It calls `check_auto_explained` on the *flat* view, which bypasses
  `StringGate::confirm`, so on `regex-032-…-fuzz` it prints `unsat` for a file
  that is genuinely `sat` (cvc5 agrees, and the shipped front door returns
  `sat`). The solver is correct; only the diagnostic lies. This matters because
  agents are routinely pointed at it for string triage — a whole lever can get
  built on a fabricated `unsat`. Cross-check any verdict it reports against the
  reference binary and the file's declared `:status` before believing it.
- **Tools in this repo have lied more often than the solver has been weak.**
  In one session: a corpus gate that ran zero tests for 15 days while exiting 0;
  a pre-push hook that had never run because `core.hooksPath` was unset; a
  `DIRTY WORKTREE` stamp that fired on the harness's own side effects; a
  reference-solver smoke probe blind to a 1000× budget-unit error; an error
  message naming a node cap when the real cause was an i128 overflow; and a doc
  comment claiming a witness binds "every declared String variable" when it
  binds the source problem's private symbol ids. Prefer a measurement over a
  message, an exit status, or a comment — including the ones you just wrote.
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

  **Declared is not reached, and both numbers are published** (ADR-0509). The 30
  are declared; no shipped route reaches them — `Lra`, `DisjunctiveLra`, `Sos`
  and `IntFarkas` all reconstruct over constructed carriers. So "we have 30
  axioms" and "our proofs rest on 30 axioms" are both wrong: the first ignores
  that nothing reaches them, the second is simply false. Quote the pair.

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
