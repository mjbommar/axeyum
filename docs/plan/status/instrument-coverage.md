# Lane: instrument-coverage — exposing what already exists and timing what nothing measured

<!-- plan-section: lane-status -->

**Landed (`WIP`, instrument-coverage, 2026-09-07).** Follow-on to
`bench-divisions` (`docs/research/12-performance/bench-divisions-2026-09-07.md`),
which measured `smtcomp_cli --trace` covering only 15.6% of sampled wall
clock across 12 divisions, with QF_ABV/QF_BV/QF_IDL/QF_RDL/QF_UFLIA at
**0.0%**. Full writeup:
[`docs/research/12-performance/instrument-coverage-2026-09-07.md`](../../research/12-performance/instrument-coverage-2026-09-07.md).

**Four new opt-in, off-by-default, thread-local instruments, all wired to
the existing `--trace`/`AXEYUM_TRACE=1` flag (no new CLI surface):**

1. `BvLayerStatsGuard` / `last_bv_layer_stats()` — publishes the `sat-bv`
   backend's already-computed `BvLayerStats` (bit-blast/CNF-encode/CNF-inprocess/
   solve/model-lift/model-replay), which existed but was wired to no CLI
   flag. Covers QF_BV directly, QF_ABV via array elimination's reduction to
   the same backend.
2. `FrontDoorStatsGuard` / `last_front_door_stats()` — cumulative parse time
   at the SMT-LIB front door's single parse call site. Universal (every
   division's front door parses).
3. `DlOnlineStatsGuard` / `last_dl_online_stats()` — total wall time inside
   the whole `dl-online` difference-logic probe call, timed at its single
   call site. Covers QF_IDL and QF_RDL, whose dominant route never enters
   the generic CDCL(T) driver at all.
4. A methodology fix found while wiring (1): `sat_bv_backend.rs`'s
   `model_lift` timer was stamped AFTER the soundness-gate replay call
   returned, silently including replay-check cost in a field named "lift."
   Split into separately-timed `model_lift` / `model_replay`.

**Non-additivity guard**: `bench-results/instrument-coverage-2026-09-07/scripts/aggregate.py`
asserts per-file `traced_ms <= wall_ms * 1.15` and exits 1 (not a warning) on
violation; `test_aggregate_guard.py` mutation-checks the guard itself
(a synthetic impossible-sum fixture must fail it, an honest one must pass).

**Coverage before/after — the exit criterion**: **15.6% -> 38.1%** (222.3s
-> 555.7s traced of 1422.8s -> 1457.8s sampled wall clock, same 93-file
sample across the same 12 divisions, re-run on s4 with
`bench-results/instrument-coverage-2026-09-07/scripts/{sweep.sh,aggregate.py}`).
**Non-additivity guard: 0 violations across all 93 files** (max single-file
fraction observed: 99.6%). Four of the five previously-zero-coverage
divisions now have real coverage: QF_BV 0.0%->80.5%, QF_IDL 0.0%->96.2%,
QF_RDL 0.0%->48.2%, QF_ABV 0.0%->11.2%; QF_UFLIA only reaches 10.7%
(parse-only — its population resolves via dispatch-decline, the one gap
this lane did not close). Full per-division table and the small
run-to-run host-contention caveat (QF_LRA/UF): diary's "Re-run: coverage
after" section.

**"Which gate bound the query" vs. "which gate printed last" (the QF_NRA
finding)**: honestly, this lane's four instruments do NOT close that gap —
they answer "how much wall clock did stage X cost," one level of
granularity above "which of several admission checks inside a stage's
dispatch declined the query." The tool that WOULD answer it already exists
(`crate::route_trace::RouteTrace`, which records the full ordered sequence
of dispatch attempts and each one's decline reason, not just the last
message printed) but is reachable only through `check_auto_explained`, a
function `solve_smtlib` does not call and which CLAUDE.md's Gotchas already
document diverging from the shipped front door on 134/397 benchmarks.
Making that safe to wire into `--trace` is the concrete next step this
finding sharpens — see the diary's "Does this instrument …" section.

**Not done** (see the diary's "What remains untraced" section for why):
generic (non-`sat-bv`) rewrite/preprocessing timing (no single funnel point
across ~7 call sites); generic (non-`sat-bv`) model-replay timing at the
other ~6 call sites; dispatch-decline / admission-decline timing for the
QF_UFLIA class and the QF_NRA-class misattribution above (the existing
`RouteTrace` instrument is reachable only through a function `solve_smtlib`
does not call, and CLAUDE.md's Gotchas already document that alternate
entry point diverging from the shipped front door on 134/397 benchmarks —
wiring it into `--trace` without first resolving that divergence was
judged out of this lane's scope).

**Gates run**: `cargo clippy --workspace --all-targets --all-features -- -D
warnings` clean; `cargo test -p axeyum-solver --lib --features full` — 1475
passed, 0 failed; `cargo test -p axeyum-solver --features full --test
corpus_regression` — 1 passed, 0 failed.
