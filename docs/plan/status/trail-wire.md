# Lane: trail-wire — the two ADR-2102 gaps in the trail's wire format, closed (ADR-2105)

<!-- plan-section: lane-status -->

**Lane trail-wire (`DONE`, trail-wire, 2026-09-15).** Continuation of Phase 3
of
[docs/plan/dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md),
closed by
[ADR-2105](../../research/09-decisions/adr-2105-the-trail-carries-the-typed-name-and-the-construct-set.md).
ADR-2102 shipped `decline_names` and `features` columns and said plainly that
both were unfinished: `to_json` wrote `detail` with no `name` member (empty
on all 220 committed rows), and `features` lived in a process-global
`AtomicU32` read by a separate `; features` prose line — the exact
string-report/grep-consume shape ADR-2101 closed for everything else. Both
are now trace members.

Branch base: `git merge --no-ff main` picked up local `main`'s
`f11879df3` (ADR-2102) at start, then `9340fd07b` (config-registry
EXEMPT-row fix for `UNSET_CONSTRUCTS`, from a coordinator note mid-lane) at
commit `025c4117d`.

## What changed

**`crates/axeyum-solver/src/route_trace.rs`** — `RouteTrace::to_json` emits a
per-attempt `"name"` member (ADR-2104's typed variant name) beside `"detail"`
for the three typed-detail decline reasons, and a top-level `"features"`
member: the construct set of the first genuinely-outermost dispatch scan,
now recorded ON the trace (`RouteTrace::record_features`, first writer wins;
`RouteTrace::absorb` merges the same way) instead of in a process-global.
Schema bumped 2 → 3. Every existing byte-stability test extended, not
loosened.

**`crates/axeyum-solver/src/auto.rs`** — `route_ownership` loses
`LAST_QUERY_CONSTRUCTS`, `record_query_constructs`, `reset_query_constructs`
and the two now-dead `ConstructSet::bits`/`from_bits` helpers; its one call
site in `check_auto_dispatch_inner` hands the rendered construct set to the
recorder already in scope via `with_recorder` (a no-op for every nested
sub-solve). Diff kept to the `route_ownership` module and this one call site,
per the brief, so as not to collide with lane QUANT-LADDER-OWNERSHIP editing
the same file's `q:*` rungs.

**`crates/axeyum-bench/examples/smtcomp_cli.rs`** — the `; features` line is
now a rendering of `RouteTrace::features()` on both the decided and watchdog
paths; the old `axeyum_solver::last_query_constructs()` global read is gone.

**`scripts/route_trace_reader.py`** — `KNOWN_SCHEMA_VERSIONS` gains 3;
`RouteTrail.features` is new (`Attempt.name` was already wired, ADR-2101
having anticipated it). 15 of 15 control tests (was 12).

**`scripts/outcome_ledger.py`** — `features_from_capture` reads the JSON
member from schema 3 on, falling back to the `; features` prose line for
schema 1/2 captures. 44 of 44 control tests (was 43), fixtures moved to
schema 3 by default with one retained schema-2 fixture proving the fallback.

**`crates/axeyum-solver/src/config_registry.rs`** — dropped the EXEMPT row
for `UNSET_CONSTRUCTS` once the sentinel it named was deleted (coordinator
note; `config_registry::tests`, 18 tests, green both ways).

## Numbers

| | |
|---|---|
| `grep -c LAST_QUERY_CONSTRUCTS crates/` | **0** |
| `route_trace.rs` lib tests (`--lib --features full route_trace`) | **25** (was 21) |
| `tests/route_trace.rs` | **13** (was 12), incl. the end-to-end first-writer-wins proof |
| `smtcomp_cli` example unit tests | **21** |
| `decline_detail_typed.rs` | **6** |
| `corpus_regression` | **2** |
| the 19 `dispatch/reason:` suites (`hooks/pre-push`) | **all green** |
| `cargo check -p axeyum-solver -p axeyum-bench --all-targets` (default features) | **clean** |
| `route_trace_reader.py` control suite | **15** (was 12) |
| `outcome_ledger.py` control suite | **44** (was 43) |
| mutation (`trail-typed-name-and-features`) | **1 registered, 1 killed**, exactly the one named test |
| `--check-anchors` | **stale=0** (1060 anchors, 136 suites) |
| positive-control row, `decline_names`/`features` | **both non-empty** (`QF_LRA/2017-Heizmann.../_array1...smt2`, this lane's release build) |

## What was left undone

Nothing named in the brief. `scripts/lane-push.sh` was not run (out of
scope: "do not push, do not merge to main").
