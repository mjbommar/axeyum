# Lane: trace-api — the trace is the API, the prose is a rendering

<!-- plan-section: lane-status -->

**Lane trace-api (`DONE`, trace-api, 2026-09-15).** Phase 2 of
[docs/plan/dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md),
closed by [ADR-2101](../../research/09-decisions/adr-2101-the-trace-is-the-api.md).
No census, gate or lane under `scripts/` reads a `; route` line any more; they
read `RouteTrace`.

Branch base: `git merge-base main HEAD` is `bb58b0bc2`, which **is** local
`main`'s HEAD at the time of the merge.

## What changed

**Completeness is a field.** `RouteTrace` carries
`partial: Option<PartialReading>`; the JSON carries `"partial"` and, on a
partial reading, `in_flight_after` and `open_segment_ns`. The `; partial `
prose prefix is byte-unchanged and is now derived from the field by
`route_attribution_report_lines` rather than applied from outside. Schema
bumped **1 → 2** so a reader can tell a v1 object (completeness absent,
unknown) from a v2 one that states `false`.

**The 32 route labels are a type.** `Route`, declared through one macro that
emits the enum, `as_str`, `ALL` and `from_wire` from a single list. The 32
`pub const` in `front_door_stage` / `quant_rung` are now defined as
`Route::X.as_str()`. `auto.rs` untouched. 33 variants: the 32 declared
constants plus the `"probe"` label `record_probe` hardcodes and nothing
declared.

**One reader.** `scripts/route_trace_reader.py`, with a 12-test control suite
whose exit status is the finding.

## Numbers

| | |
|---|---|
| consumers under `scripts/` parsing route prose | **before 7, after 0** |
| live defects the migration found | **3** |
| reader vs the CLI's own prose, on committed logs | **251 of 251 agree** |
| re-derivations matching the corrected ADR figure | **21 of 21** |
| `bench-results/` consumers left on the prose (dated receipts) | 17 files / 29 sites |
| route-trace `DeclineReason` producer sites still emitting a free-string detail | **44**, counted and NOT typified |

The three live defects: `qf-nia-sat-inslice-budget.py` and
`portfolio-oracle.py` both anchored on `^; route-trail `, which the watchdog
path never prints, so a file killed mid-search read as "no route cost
anything"; `euf-online-atoms-sweep.sh` searched the TRAIL line for `bound_by=`,
a field that only appears on the PROSE line, so `bound_by` has been empty on
every row that sweep has ever written.

## Corrections to inherited text

- The brief's seven-consumer list named
  `bench-results/silent-hang-20260915/split.py`. It reads a TSV **column**, not
  a log, and never parsed route prose. The seventh real consumer is
  `scripts/euf-online-atoms-sweep.sh`.
- ADR-2075's *"Fourteen lines."* (line 51) is attributed to
  `UFNIA/sledgehammer/Hoare/z3.850818.smt2`, whose committed receipt took a
  `ResourceLimit` give-up path and prints **0** `; partial ` lines. The receipt
  on disk printing exactly **14** is `prof/fp-mqueue`. The number is right; the
  file it points at is not.
- `SimplexDecline` has grown from ADR-2060's 6 variants to **7**, so the typed
  give-up vocabulary is **23** across five enums, not 22.

## Left undone, named

- **The 44 free-string decline details are not typified.** The classification
  axis (`reason` + `kind`) is already typed and survives to the reader; the
  detail is not. Typifying it is a compiler-enumerated refactor across the
  solver of ADR-2060's size — a lane, not a slice of one. Counted in ADR-2101
  so it is a backlog rather than an assumption.
- **Dispatch rung labels are still `&'static str`.** No declaration exists to
  derive an enum from; that is Phase 1's surface.
- **`bench-results/` consumers are not migrated**, deliberately: they are dated
  receipts of completed measurements, and editing them would change published
  evidence.
