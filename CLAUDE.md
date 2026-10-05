# CLAUDE.md

Guidance for Claude Code (and other agents) working in this repository.
**Keep in sync:** `CLAUDE.md` and `AGENTS.md` carry the same text; only the
title and this line differ. Edit both in the same commit. Incident history and dated
measurements live in [`docs/contributor-guide/`](docs/contributor-guide/README.md),
not here ([archive of the long form](docs/contributor-guide/agent-instructions-history.md)).

## What This Project Is

Axeyum is a Rust-first automated reasoning stack: typed term IR → rewriting →
query planning → solver backends (a pure Rust SAT/SMT path plus feature-gated
native oracles) → models, proofs, and checkable evidence. Identity:
**untrusted fast search, trusted small checking.** North star: a complete
framework for general reasoning, logic, and proving — do not paint the IR,
solver trait, or evidence formats into a quantifier-free corner
([north star](docs/research/00-orientation/north-star.md)).

## The Flywheel

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

Every arrow exists and the cycle has closed end to end; the work is making it
**automatic** — not theorem count, not benchmark position
([throughput](docs/formalized-math-2026-08/05-throughput.md)).
- **The metric is the trusted base, not output volume** — assumptions remaining
  per prelude, and results nobody hand-wrote. Read them from the kernel, never
  from source text or a doc.
- **A checker that cannot fail is worse than no checker.** Make exit status
  depend on the finding; when you touch a checker, delete one guard and require
  that exactly one test dies ([discipline](docs/contributor-guide/evidence-and-checker-discipline.md)).

Strategy, decided — read before framing any "compare to Mathlib / Mathematica" work:
- [ADR-0601](docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md) — autogenesis, CAS, importer are producers behind ONE trust anchor (`Kernel::add_declaration`).
- [ADR-0602](docs/research/09-decisions/adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md) — operations are receipts; dispatch needs a producer contract with no `proved` field.
- [ADR-0603](docs/research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md) — a classical theorem lands as a graded statement family, one fact per statement.
- [Architecture review 2026-08-27](docs/research/11-design-review/2026-08-27-architecture-review.md) — read before a refactor or a congruence fight (`creal.rs` fusion, interval-relative mesh, "computed, not extracted").
- [Cost model](docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md) — tokens are capex; claim per-statement dominance, never coverage parity.

## Working Stance

We ship toward Z3 + Lean parity, one verifiable increment at a time. There is
always a next concrete task; big tasks are sliced, not deferred. Soundness is a
method (conservative slices, soundness-negative tests, independent re-validation,
self-checking evidence), never an excuse to punt. Z3 parity is a measured claim;
Lean parity means every unsat/valid carries a machine-checkable proof. Spend the
words on the diff.

## Session Protocol

1. Read [PLAN.md](PLAN.md) **first**. It is the only file with mutable session
   state, and it is **generated** (`python3 scripts/gen-plan.py`; `--check` is a
   gate) — never hand-edit it. The project-wide queue is
   [`docs/plan/global/20-next-actions.md`](docs/plan/global/20-next-actions.md),
   organized as tracks with item ids (`SOL-n`, `LIB-n`, `EVD-n`, `CON-n`, `ENG-n`).
2. When you start a queue item, open `docs/plan/status/<lane>.md`
   ([format](docs/plan/status/README.md)). Keep it ≤ 3,000 bytes: what is true
   now, what is next, what is blocked. Move detail to `docs/plan/notes/<lane>.md`
   with `python3 scripts/archive-plan-status.py`. When the lane is DONE (or
   paused), archive it in the same commit: `python3 scripts/archive-plan-lane.py
   <lane>` moves it to `docs/plan/archive/lanes/` and keeps every link. A gate
   allows no DONE lane and at most 25 lane files in `status/`.
3. History is evidence, not the queue. Search it (`rg`) in [`docs/plan/CATALOG.md`](docs/plan/CATALOG.md)
   (generated) and `docs/plan/archive/` instead of reading old plans end to end.
4. Before adding public operators, rewrites, encodings, backends, evidence
   artifacts, or logic fragments, check the
   [foundational DAG](docs/research/08-planning/foundational-dag.md).
5. Decisions are not made silently in code: close questions with ADRs
   ([decisions](docs/research/09-decisions/README.md)). The ADR index is generated
   (`python3 scripts/gen-adr-index.py`); never add an index row by hand.
6. Before ending a session: update your lane file, run
   `python3 scripts/gen-plan.py`, and commit both with `scripts/lane-commit.sh`.
   Touch `docs/plan/global/` only for a genuinely project-wide change: per-lane
   state belongs in per-lane paths, never in one file every lane writes.

## Commands

These assume a gate-capable host — check [fleet hosts](docs/contributor-guide/fleet-hosts.md)
before believing a gate. Every command with its full rationale:
[gate-commands reference](docs/contributor-guide/gate-commands-reference.md).
**Always confirm a NONZERO test count**: feature-gated suites exit 0 having run nothing.

```sh
just check                    # the fullest aggregate gate; ./scripts/check.sh is a narrower no-just fallback
just brief <target…>          # step 0 of any brief: does the target already exist?
cargo fmt --all --check       # read-only; format single files with rustfmt --edition 2024 <file>
scripts/check-clippy-complete.sh   # clippy -D warnings; bare cargo clippy can skip stale-mtime files
scripts/check-workspace-tests.sh   # workspace tests, reports how many it actually ran
cargo test --workspace --lib                       # NOT -p axeyum-solver: defects live in other crates too
cargo test -p axeyum-solver --lib --features full  # default features compile only a sliver of solver tests
cargo test -p axeyum-solver --features full --test corpus_regression  # without full: 0 tests, exit 0
cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1  # read its reference-frame lines
python3 scripts/validate-facts.py  # the fact ledger
python3 scripts/gen-plan.py --check && ./scripts/check-links.sh
scripts/cargo-serialized.sh <cargo args…>  # wrap every heavy cargo job (host flock + memory ceiling)
```

Pre-merge gate by change type (each in addition to `--workspace --lib`):

| Change | Must also run |
|---|---|
| String route / parser / front door | `corpus_regression --features full`, plus `--test online_string_front_door`, `word_first_fallback`, `qf_slia_fixed_splice`, `stoi_len_abstraction` (all `--features full`) |
| Any solver change | `cargo test -p axeyum-solver --lib --features full` |
| Linear arithmetic (simplex, LRA/LIA, difference logic) | the z3 differential fuzzes, `--features z3`: `qf_lra_differential_fuzz`, `simplex_lra_fallback_differential`, `qf_uflra_differential_fuzz`, `difference_logic_differential_fuzz`, `qf_lia_differential_fuzz` |
| Decider / dispatch | `progress_frontier --features full -- --test-threads=1` |

CI runs stable plus MSRV 1.88; edition 2024, resolver 3. WebAssembly is a
supported target (ADR-0017): `cargo build --target wasm32-unknown-unknown -p axeyum-solver`.

## Layout

- Term/circuit core: `axeyum-ir` (sorts, terms, interning, ground eval),
  `axeyum-aig` (structurally hashed AIG), `axeyum-bv` (term → AIG lowering with
  lift maps), `axeyum-cnf` (Tseitin, DIMACS, the native CDCL core with DRAT
  output and an independent DRAT checker; no linked SAT solver — ADR-1910 removed
  BatSat, the referee is an external binary over DIMACS).
- Theories and front end: `axeyum-arith` (exact arithmetic), `axeyum-fp`
  (IEEE 754 builders), `axeyum-strings`, `axeyum-egraph` (congruence closure),
  `axeyum-query`, `axeyum-rewrite` (rewrite contracts, array elimination),
  `axeyum-smtlib` (SMT-LIB reader/writer), `axeyum-solver` (backend trait,
  dispatch, models; native backends behind features, `z3` is the oracle).
- Proof side: `axeyum-lean-kernel` (in-tree Lean kernel, the trust anchor),
  `axeyum-lean-import` (fail-closed `lean4export` reader), `axeyum-cas`
  (proof-carrying computer algebra), `axeyum-search` (cube-and-conquer covers).
- Consumers: `axeyum-verify`(+`-macros`), `axeyum-property`(+`-macros`),
  `axeyum-evm`, `axeyum-machine`, `axeyum-machine-evidence`, `axeyum-py`,
  `axeyum-wasm`, `axeyum-scenarios` (oracle-free workloads), `axeyum-bench`.
- `artifacts/facts/` — the fact ledger: one JSON per proposition with formal
  statement, status, evidence and axiom footprint (schema
  `artifacts/ontology/fact.schema.json`). `epistemic_status` is what we
  established; `external_status` is what mathematics knows.
- `docs/refactor-2026-08/`, `docs/mathematics-2026-08/`,
  `docs/formalized-math-2026-08/` — the August strands, frozen 2026-10-05: their
  reasoning holds, their counts and "next" lists do not; `docs/research/`
  — design rationale ([map](docs/research/README.md)); `references/` —
  gitignored reference-solver clones (`scripts/fetch-references.sh`).
- Crates are added only once a boundary is proven by use (ADR-0001). The pure
  Rust stack is the product; linked solvers stay backend/oracle/cross-check
  only without a new ADR (ADR-0002).

## Multi-agent hygiene

Many lanes share one checkout; the git index has eaten work twelve times. Full
model: [worktrees](docs/contributor-guide/multi-agent-worktrees.md),
[operations](docs/contributor-guide/multi-agent-operations.md).
- Commit with `scripts/lane-commit.sh -m <msgfile> -- <path>…`; never bare `git commit`.
- Write commit messages via a file or quoted heredoc (`git commit -F - <<'MSG'`); `-m "…"` strips backticks.
- Verify every commit with `git show --stat` — read the file count.
- Set lane identity with `export AXEYUM_AGENT=<lane>`; never `git config axeyum.agent`.
- Never `git stash`, `checkout`/`restore` files you did not modify, or rewrite history.
- Format single files with `rustfmt --edition 2024 <file>`; never `cargo fmt` (it writes every lane's files).
- Heavy cargo goes through `scripts/cargo-serialized.sh`; exit 75 means the lock timed out.
- Push with `scripts/lane-push.sh` and never start a second push.
- After any merge run `scripts/check-merge-hygiene.sh`; recount pinned counts with `scripts/recount-pinned-inventory.py`.
- Two lanes adding to one Rust file: merge with `scripts/lane-merge-additive.py`.
- Never mutation-test in the shared tree: use `scripts/tests/mutation_controls.py` or `scripts/lane-snapshot.sh`.
- Snapshots come from `W=$(scripts/lane-snapshot.sh <ref>)`, never `mktemp` + `git archive` (/tmp is RAM; mtimes go stale).
- Dispatch writing lanes with `isolation: "worktree"`; from a worktree, an absolute main-checkout path edits main.
- An ADR number is a shared allocation: brief a specific number well above the current maximum.

## Hard Rules

- Partial/underspecified operators (`div`/`mod` by 0, `bvudiv`/`bvurem` by 0,
  `str.at` out of range, …) need a fuzz seed-class that emits the degenerate
  argument; a fuzz that avoids the corner is not a soundness gate.
- The default build has **no C/C++ dependency**; native backends are feature-gated leaves.
- `unsafe_code` is denied workspace-wide; exceptions need an ADR.
- Semantics, model/proof lifting, and replay/checker routes are explicit before
  any new operator, rewrite class, encoding, backend, or logic fragment goes public.
- `unknown` is a first-class result, never an error.
- Determinism is API: stable order, explicit seeds and limits, no hash-map order in output.
- Every `sat` is checkable against the lifted model; never drop lowering/lift maps.
- Term handles are lifetime-free `Copy` IDs; no FFI types or lifetimes in public APIs.
- BV semantics follow SMT-LIB totality verbatim (`bvudiv x 0` = all-ones;
  [semantics](docs/research/01-foundations/bv-semantics-and-partial-operations.md)).

## Gotchas (trigger index)

> **Before believing a result, ask what the command would print if it were
> broken. If that is what it just printed, it is not evidence.**

**Does it already exist?** → [finding existing lemmas](docs/contributor-guide/finding-existing-lemmas.md)
- Run `just brief <target…>` before writing a brief; search for the STEP, not the
  NAME (`crates/axeyum-lean-kernel/examples/shape_search.rs`).
- A stale prebuilt binary reports a false ABSENT; a handoff's "blocked on X" is a claim — verify it in-tree.

**Kernel: rejected, or admitted and wrong** → [kernel proof engineering](docs/contributor-guide/kernel-proof-engineering.md)
- Every new `Definition` needs an evaluation test at concrete, discriminating arguments.
- `Nat.add`/`Nat.mul` recurse on the right argument; a recursor on a bare free variable is stuck.
- Read trusted surface from `Kernel::axiom_footprint`, never a rendered name (`AxNat` ≠ axiomatized; `AxReal` ≠ `CReal`).

**Kernel: slow or stack overflow** → [prelude build cost](docs/contributor-guide/prelude-build-cost.md)
- Bisect, do not theorize; measure in `--release` first; numerals are unary, keep magnitudes small.

**Measuring anything** → [measurement hazards](docs/contributor-guide/measurement-hazards.md)
- Banned: `$?` after a pipeline, `grep -q` under pipefail, empty grep as a negative, fixed-name scratch files.
- `prelude_theorem_inventory` runs `--release` and lists theorems only; pair every negative with a positive control.
- `cargo-serialized.sh` serializes jobs, not memory: put `ulimit -S -v` on expanding scripts.

**Evidence and blind populations** → [checker discipline](docs/contributor-guide/evidence-and-checker-discipline.md)
- A test named "every X" derives X from the authority; a certificate carries every distinction its producer makes.
- A held-out population is shared: touching one member spends the family.

**Dispatching lanes** → [operations](docs/contributor-guide/multi-agent-operations.md)
- Require an early commit, not a `cargo test` run; state constraints as outcomes, not mechanisms.

**Reference solvers**
- `z3` crate ≥ 0.20 has no `'ctx` lifetime; `Solver::new()` takes no arguments.
- varisat (unmaintained since 0.2.2) is the only Rust SAT solver with LRAT; splr has DRAT only.
- Our own CDCL core is the engine (ADR-1703, ADR-1910); external solvers are yardsticks.
- CDCL *priority* is gated by [benchmark methodology](docs/research/08-planning/benchmarking-and-performance-methodology.md).
