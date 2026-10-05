# Gate commands reference

The full, annotated gate-command list that `CLAUDE.md` / `AGENTS.md` carried
until 2026-10-05, kept verbatim. The agent instruction files now carry only a
short command block and a per-change pre-merge table; this page keeps every
command's rationale, including the incident that made each flag mandatory.

Two rules dominate everything below:

- **`--features full` (or `--features z3`) is mandatory on the suites marked
  so.** Without it they compile to an empty binary, print
  `running 0 tests ... ok`, and exit 0.
- **Always confirm a NONZERO test count** before reporting a gate as passed.

Which host can run which gate: [fleet hosts](fleet-hosts.md). Focused versus
pre-merge gate selection: [testing and validation](testing-and-validation.md).

## Commands (verbatim, as of 2026-09-14)

**These commands assume a gate-capable host.** They are not equally runnable
everywhere: measured 2026-08-16, `lean` and `just` existed on one fleet host of
five and `cargo-deny` on none, so an agent that runs `just check` on a host
lacking `just` silently falls back to the narrower `check.sh` and reports it as
the gate. The capability baseline, the provisioning script, and the map of which
gate needs which toolchain are in
[docs/contributor-guide/fleet-hosts.md](fleet-hosts.md).
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
#
# NOTE (2026-09-09): until this date the three LRA/UFLRA fuzzes below were the
# whole list, and this block's own prose claimed they covered DIFFERENCE LOGIC.
# They did not. DL had NO oracle coverage at all — and it is a COMPLETE decider
# that runs FIRST in the dispatch ladder, so a wrong answer there is caught by
# nothing downstream. Pure QF_LIA had none either. Both now exist (roadmap item
# 2.6) and are the last two lines. Still uncovered: int_real_relax and lia_gcd
# have no suite of their own, and bmc/imc/pdr have none.
cargo test -p axeyum-solver --features z3 --test qf_lra_differential_fuzz
cargo test -p axeyum-solver --features z3 --test simplex_lra_fallback_differential
cargo test -p axeyum-solver --features z3 --test qf_uflra_differential_fuzz
cargo test -p axeyum-solver --features z3 --test difference_logic_differential_fuzz
cargo test -p axeyum-solver --features z3 --test qf_lia_differential_fuzz
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
