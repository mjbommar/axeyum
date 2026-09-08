<!-- plan-section: route-attribution -->
## Lane: route-attribution

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
- **S3 — sweep route column: DONE.** `bench-results/route-attribution-2026-09-07/`.
- **S4 — virtual best over our own routes: measured, see the diary.**

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
