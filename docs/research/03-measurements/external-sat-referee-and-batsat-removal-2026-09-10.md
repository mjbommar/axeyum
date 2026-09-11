# The external SAT referee, and what removing BatSat actually cost

Date: 2026-09-10
Lane: `E4-referee`
Subject: phases A1 and A4 of
[`docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md`](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
deciding [ADR-1910](../09-decisions/adr-1910-the-sat-referee-is-an-external-binary-reading-dimacs-text-and-batsat-is-removed.md).
Input: [the R-B removal-surface inventory](batsat-slice2-surface-2026-09-10.md).

Every number below was produced by a command run in this lane's worktree. Where
a check did not run, it says "did not run" rather than being inferred.

## 1. The mutation table — the whole argument in six numbers

R-B's central analytical claim was that the BatSat differential could not see a
DIMACS writer or parser defect, because it hands BatSat the same `CnfFormula`
object our own parser built. That was an argument from the code's shape. This
lane measured it.

Method: mutate `crates/axeyum-cnf/src/lib.rs` in this lane's isolated worktree,
run both referees, revert. Each mutation flips the sign of the FIRST literal of
every clause — a silent semantic change that preserves clause count, literal
count, variable count, and file shape, so nothing structural can catch it.

| mutation | `native_vs_batsat_differential` | `external_sat_referee` |
|---|---|---|
| `to_dimacs` writes each clause's first literal with the wrong sign | **3/3 PASS** | **3/4 FAIL** |
| `parse_dimacs` reads each clause's first literal with the wrong sign | **3/3 PASS** | **3/4 FAIL** |
| (no mutation) | 3/3 pass | 4/4 pass |

Both referees are green on a clean tree, so neither row is a vacuous failure.
The old referee is green on a DIMACS writer defect **and** on a DIMACS parser
defect; the new one dies on both.

Which of the four dies differs between the two mutations, and the difference is
informative:

- Under the **writer** mutation the known-verdict control survives, because it
  compares the external binary's answer against a verdict fixed in the test and
  the mutation moves both the written text and nothing else consistently for that
  one formula's shape.
- Under the **parser** mutation the degenerate-formula test survives, because
  every one of its cases is *built by* `parse_dimacs` from a literal string, so
  the mutated parser produces a formula that the mutated round-trip agrees with.
  The random 3-SAT family, built programmatically, is the one that catches it.

That is an argument for keeping both a programmatically-built family and a
text-built family, which the suite does.

## 2. What the referee adjudicates

`crates/axeyum-cnf/tests/external_sat_referee.rs`, on the provisioning host with
**cadical 3.0.1 and kissat 4.0.4** both present:

```
external-sat-referee: compared=12  test=micro-cnf corpus
external-sat-referee: compared=480 test=random 3-SAT at the threshold ratio
external-sat-referee: compared=28  test=degenerate formulas
external-sat-referee: compared=4   test=known-verdict control
external-sat-referee: OK -- 4 tests, 524 adjudicated comparisons
```

A "comparison" is one (instance, referee, native-arm) triple: two native arms
(in-memory, round-tripped) times two referees. With one referee the count
halves; the gate's floor is 100, well below either.

Three verdicts are compared per instance and every external `sat` model is
replayed against the ORIGINAL in-memory formula — a second, independent probe of
the writer's variable numbering that verdict agreement cannot perform.

### Skip and require, both exercised

| condition | test binary | gate script |
|---|---|---|
| binary present | 4 passed | exit 0, prints the four counts |
| no binary | 4 passed + loud stderr banner | exit 0, prints `SKIPPED` and *"THE NATIVE CORE'S VERDICTS WERE NOT ADJUDICATED BY ANY THIRD PARTY ON THIS RUN"* |
| no binary, `AXEYUM_REQUIRE_EXTERNAL_SAT=1` | **4 failed** | **exit 1** |

Absence was simulated by pointing `AXEYUM_CADICAL_BIN` and `AXEYUM_KISSAT_BIN`
at a non-existent path, which is the same code path as a host with neither
binary.

### The gate's own guard fired on its first run

`scripts/check-external-sat-referee.sh` re-derives the adjudicated count from the
suite's `compared=N` lines rather than trusting `test result: ok`. Its first run
reported:

```
external-sat-referee: FAIL -- the suite passed but emitted NO 'compared=' report.
```

The suite was healthy; the pattern was anchored with `^`, and libtest under
`--test-threads=1 --nocapture` prints a test's stdout on the line it opened with
`test <name> ... `. The guard was right about its own wiring and the anchor was
the bug. Recording it because a guard whose failure has never been observed is a
claim, not a check — and this one made its claim good before it was asked to.

## 3. Where it runs

The referee it replaces was in **no** gate, CI job, `justfile` recipe or git hook
(R-B, measured with positive controls). The replacement is in three:

| place | form |
|---|---|
| `scripts/check.sh` | `step external-sat-referee scripts/check-external-sat-referee.sh` — the script now lists **545** steps |
| `justfile` | `external-sat-referee` recipe, added to the `check` dependency list |
| `hooks/pre-push` | `step_seconds "external SAT referee (ADR-1910)"`, ~2 s warm |

`scripts/check-aggregate-scope.sh` confirms the step is NOT in the
check.sh-vs-`just check` divergence list: it runs on both sides.

Binaries come from `scripts/provision-external-sat-referee.sh`, which builds
CaDiCaL and Kissat from the gitignored `references/` clones into `~/.local/bin`.
It copies to a scratch directory first — building in the clone would leave a
build tree in a directory every lane on the host shares. Measured cold on this
box: both configure-and-make in well under a minute, `-j4`.
`scripts/provision-fleet-host.sh` now runs it and verifies both binaries by
making them speak, not by reading the installer's exit status.

## 4. What removal actually removed

### Dependencies

| check | result | control |
|---|---|---|
| `cargo tree -e normal --workspace --all-features` | **0** batsat/rustsat lines | `axeyum-cnf` matches **5** times; tree is 300 lines |
| `cargo tree --workspace --all-features` (normal + build + dev) | **0** | tree is 706 lines |
| `cargo check -p axeyum-cnf --features batsat-reference` | *"the package 'axeyum-cnf' does not contain this feature"* | — |

Both edge sets were run; the second is the one that answers "is it a
dev-dependency of anything".

### The lockfile — R-B's open question, now measured

R-B recorded this as **did not run**. Ten crates leave `Cargo.lock` (92 lines
deleted, no additions):

`batsat`, `rustsat`, `rustsat-batsat`, `bit-vec`, `cpu-time`,
`minimal-lexical`, `nom`, `winapi`, `winapi-i686-pc-windows-gnu`,
`winapi-x86_64-pc-windows-gnu`.

`anyhow`, `itertools`, `tempfile`, `thiserror` and `rustix` stayed — R-B
predicted exactly this, and it is why "the rustsat subtree" is not the same set
as "what leaves the lockfile".

### Code

Deleted: `crates/axeyum-cnf/src/batsat_reference.rs` (306 lines),
`crates/axeyum-cnf/tests/native_vs_batsat_differential.rs`,
`crates/axeyum-solver/tests/native_cdcl_baseline.rs`, the four adapter unit
tests in `lib.rs`, the `pub mod`, the six-name re-export, and both gated `use`
statements.

Manifests: the feature in `crates/axeyum-cnf/Cargo.toml` and the two forwarding
declarations, the three `optional = true` lines, the three
`[workspace.dependencies]` lines, and `gate_b_sweep`'s `required-features`
block.

### Test counts — the number that says coverage went UP

```
cargo test -p axeyum-cnf --lib   →  623 passed   (was 618)
```

The five `proof_sat.rs` differentials were **ungated**, not deleted: each lost
its BatSat arm and kept the two decisive assertions (every `sat` model must
satisfy; every `unsat` proof must DRAT-check). 618 + 5 = 623, and those five had
never been compiled by any gate, because nothing set the feature they were
behind.

For the two *policy* tests the referee got sharper rather than weaker:
`ema_restart_schedule_preserves_every_verdict` and
`blocking_literal_bcp_preserves_verdicts` assert a property defined as
verdict-preservation, so the right referee is the same core under the DEFAULT
policy — it varies one thing instead of everything. `reduce_db_stress_proof_checks`
now asserts its pigeonhole arm from the pigeonhole principle instead of from a
second opinion: two engines can agree and both be wrong.

### Ported rather than retired

- **`gate_b_sweep`** keeps its native arm and its `verify` subcommand (the
  CaDiCaL/Kissat arms were always external binaries whose stdout it parses), and
  loses `required-features`, so it now builds on a default
  `cargo check --all-targets` instead of being skipped by it. Resuming now
  REFUSES to append to a TSV whose header is not the current one — appending
  single-engine rows to a four-engine file yields a file where column 4 means
  two things in different rows, and it still parses.
  `bench-results/sat-core-gate-b-20260905/` is **untouched**; it keeps its
  BatSat column forever, because that is what was measured that day.
- **`xor_cdcl_curated_measure`** re-points at `solve_with_native_core_timeout`.
  It asks whether CDCL(XOR) decides what the *shipping* engine cannot, and since
  ADR-1703 the shipping engine is the native core — the old form was asking
  about a solver no route used. It also drops the second feature gate, so a gate
  can compile it for the first time.
- **`cnf_core_bench`** loses its BatSat column and nothing else.

## 5. Gates run, with their counts

| gate | result |
|---|---|
| `cargo clippy --workspace --all-targets -- -D warnings` | exit **0** |
| `cargo clippy --workspace --all-targets --all-features -- -D warnings` | exit **0** |
| `cargo check --workspace --all-targets` | exit 0 |
| `cargo test -p axeyum-cnf --lib` | **623 passed**, 0 failed |
| `cargo test -p axeyum-cnf --tests` (all 15 integration suites) | all passed; `external_sat_referee` 4/4 |
| `cargo test -p axeyum-solver --lib --features full` | **1695 passed**, 0 failed |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | **2 passed** |
| `scripts/check-external-sat-referee.sh` | exit 0, 4 tests, **524** comparisons |
| `./scripts/check-links.sh` | exit 0, "all links ok" |
| `scripts/check-merge-hygiene.sh` | exit 0, `PASS` |
| `python3 scripts/check-admission-limit-basis.py` | exit 0 — 173 declarations, every basis resolves |
| `scripts/tests/test-admission-limit-basis-control.sh` | exit 0, `PASSED` — including "deleting one checker guard must un-catch EXACTLY ONE mutant", all four branches |

The control suite was run because this lane edited that checker's prose, and a
lane that edits a checker reporting the checker green is precisely what its
control suite exists to distrust.

## 6. Two gates that are red, and are NOT this lane's

Checked rather than assumed, because a red gate is not evidence until you check
its own query.

- **`scripts/check-shell-antipatterns.sh`** fails on
  `scripts/tests/test-prepush-l0-gates.sh` (three `grep -q` uses in a pipeline
  under `pipefail`). That file exists on `main` with the same three uses; this
  lane did not touch it.
- **`python3 scripts/check-parity-docs.py`** fails on three items, all about
  `crates/axeyum-smtlib/examples/ingest_shape_probe.rs` being absent from
  `docs/reference/examples.md` and two count markers. That example is committed
  on `main` (`0855f7db4`) and is already missing from `examples.md` there, and
  the tracked example count is **253 both before and after** this lane's changes
  (`git ls-files 'crates/*/examples/*.rs' | wc -l`, and the same count against
  `main`'s tree) — this lane removed a `[[example]]` *manifest block*, not an
  example *file*, and the checker counts files. Left alone: the fix touches
  `PLAN.md`, which is generated and which no lane edits.
- **`scripts/check-aggregate-scope.sh`** reports 9 steps on one side only. The
  new `external-sat-referee` step is **not** among them (0 matches in the
  divergence output) — it runs on both sides. The 9 are pre-existing and
  unrelated.

## 7. Checks this note did not run

Reported as "did not run", never inferred:

- The full `./scripts/check.sh` or `just check` aggregate. Individual steps were
  run by name; the aggregate was not.
- The `z3`-gated differential fuzzes. `z3` is not installed on this host
  (`~/.local/bin` has no z3 and none is on PATH), so they would have compiled to
  zero tests and exited 0 — the exact silent-inertness trap, and reporting that
  as a pass would be worse than reporting it as not run.
- `progress_frontier`. Nothing here touches dispatch or a decider, and the
  ratchet is load-sensitive on a shared box.
- Whether `IncrementalBvSolver` is still `!Sync`, i.e. whether
  `#[pyclass(unsendable)]` in `crates/axeyum-py/src/solver/core.rs` is still
  *required* rather than merely stale in its justification. R-B recorded this as
  unmeasured and it is still unmeasured; the comment there already says the
  BatSat justification is obsolete, so nothing this lane did made it more wrong.
- The 13 "live and wrong" `docs/` items from R-B §6. Those are phase A2, which
  landed separately. Four now-wrong Rust doc comments **were** fixed here,
  because removing the adapter made them false in a new way:
  `crates/axeyum-solver/src/sat_bv_backend.rs:4`,
  `crates/axeyum-solver/tests/sat_bv.rs:4`,
  `crates/axeyum-solver/src/backend.rs:570`, and
  `crates/axeyum-cnf/examples/native_core_sweep.rs:8`.
