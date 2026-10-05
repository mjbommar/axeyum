# Lane: route-attribution — which route decided the file, and which route bound it

<!-- plan-section: lane-status -->

**Goal.** Make route attribution available from the SHIPPED front door
(`solve_smtlib`, as `smtcomp_cli` runs it), separate "which route decided" from
"which route bound", add a route column to the sweep, and measure the virtual
best over our own routes.

**Why.** We have 19+ dispatch routes and could not say which one decided any
file we solve. `route_trace.rs` existed but was reachable only through
`check_auto_explained`, which runs the flat assertion view — the path CLAUDE.md
records as disagreeing with the shipped front door on 134 of 397 benchmarks. So
the one instrument that could answer "which route" gave answers that do not
transfer.

### Status

- **S1 — front door carries attribution: DONE.** `RouteAttributionGuard` in
  `axeyum-solver` (opt-in, off by default, thread-local, wired to the existing
  `--trace` flag, no new CLI surface — the same shape as `FrontDoorStatsGuard` /
  `BvLayerStatsGuard` / `DlOnlineStatsGuard`). `smtcomp_cli --trace` now prints
  `; route decided_by=… bound_by=… last=… bound_ms=… total_ms=… attempts=…`
  plus the full `; route-trail <json>`.
- **S2 — decided-by vs bound-by separated: DONE.** `RouteTrace::decided_by()`
  (last decisive entry) and `RouteTrace::bound_by()` (most expensive segment)
  are computed from different fields — position vs timing — and
  `bound_by_is_separable_from_printed_last` pins that they can disagree.
- **S3 — sweep route column: DONE.** `bench-results/route-attribution-2026-09-07/`
  — 1,200 files, 12 divisions, columns `decided_by / bound_by / last / bound_ms
  / trace_total_ms / attempts`.
- **S4 — virtual best over our own routes: MEASURED. The portfolio answer is
  no.** 24.9% of in-dispatch time on decided files is recoverable (a projected
  1.33x), but on the 350 losses the binding route already holds a **median 84%**
  of the trail and over 90% on 166 of them — there is no queue in front of it to
  remove. Those files need a better route, not more cores. Twenty distinct
  routes decide the 754 decided files, so the routes are NOT redundant; route
  diversity and portfolio value simply turn out to be different questions.

### Measured findings

| finding | number |
| --- | --- |
| losses where `bound_by` ≠ `last` | **348 of 350 (99.4%)** — every one misclassified by a last-message census |
| distinct deciding routes | 20; largest decides 21% of what we decide |
| QF_SLIA decided outside `check_auto` | 63 of 97, by two front-door stages the flat view cannot see |
| files bound by `fd:parse` (ingest, not any route) | 26 |
| recoverable share on decided files | 24.9% → projected 1.33x |
| median binder share on losses | 84% |
| **blind spot** | 96 of 1,200 printed no route line, **all `unsolved`** — the watchdog path |

### Known gaps

- **The watchdog blind spot is not closed.** The worker's thread-locals are
  unreadable from the main thread, so hard timeouts carry no trail. Only the
  *silence* is fixed (`; route unavailable: <reason>`), so an aggregation counts
  what it cannot attribute instead of shrinking its denominator. Closing it
  needs a cross-thread collector.
- **No strict virtual best.** `SolverConfig` has no route-selection knob, so
  "each route alone on each file" is not measurable. The deciding-route
  distribution is therefore an upper bound on route diversity; the recoverable
  wall time is exact.
- `check_auto_explained` still lacks the `memory_budget_decline` entry guard.
  `check_auto` now runs it ahead of the delegation so the shipped path is
  correct, but the two functions still differ, and `tests/route_trace.rs`'s
  invariance corpus never sets `memory_limit_mb`.

### Landed changes

| what | where |
| --- | --- |
| attribution collector, `decided_by`/`bound_by`, `absorb` | `crates/axeyum-solver/src/route_trace.rs` |
| outermost-dispatch publish | `crates/axeyum-solver/src/auto.rs` |
| front-door stage attribution | `crates/axeyum-solver/src/smtlib.rs` |
| `--trace` route lines | `crates/axeyum-bench/examples/smtcomp_cli.rs` |
| verdict-invariance + anti-vacuity gate | `crates/axeyum-solver/tests/route_attribution.rs` |
| decision record | `docs/research/09-decisions/adr-1760-*.md` |
| measurement | `docs/research/12-performance/route-attribution-2026-09-07.md` |
