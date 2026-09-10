# ADR-1907: A `RouteTrace` segment's cost is movable; a rung's verdict is not — one primitive pair, no new record kind, no schema bump

Status: accepted
Index-summary: `q:mbqi` read 0 ms on every file because `RouteTrace` charges a segment to whoever records NEXT, and the terminal quantified arm deliberately records MBQI LAST so it owns the trail's final word. Cost attribution and last-word attribution want opposite orderings, and recording at both points double-counts. Decision: keep ONE record kind and make the cost movable — `RouteTrace::take_open_segment` REMOVES the open segment and hands the caller its duration; `record_result_with_elapsed` re-attaches it to an attempt recorded later. A move, not a copy, so `total_elapsed()` is invariant by construction and only the distribution changes. Rejected: two record kinds (breaks the `attempts.len() == elapsed.len()` alignment every consumer relies on), explicit duration alone (double-counts), record-twice (`decided_by` takes the LAST decided, so a duplicate silently moves it), and document-and-leave (the number has already been withdrawn once). `ROUTE_TRACE_JSON_SCHEMA_VERSION` stays at 1: no field is added, renamed or removed — the numbers move, the shape does not, and a reader that rejected on version would be rejecting the correction it wants. A second defect found at the same site is fixed with it: `q:uf-fmf-full` was recorded as `declined` on the MBQI-`unsat` path, where the finder never runs at all.
Date: 2026-09-10

## Context

Roadmap item 1.8 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md).

### The instrument's recording model

[`RouteTrace`](../../../crates/axeyum-solver/src/route_trace.rs) keeps two
index-aligned vectors — `attempts` and `elapsed` — and a single `last: Instant`.
Every `record_*` method pushes an attempt and then calls `tick()`, which pushes
`now - last` and sets `last = now`. So:

> **A segment is charged to whoever records NEXT.** A route's cost is not
> measured by the route; it is the gap between the previous record call and this
> one.

That is a reasonable model — it needs no cooperation from the routes, and it
cannot lose time, because consecutive gaps tile the interval exactly. Its price
is that **the order of the records fixes the attribution**, and it holds only
while every recorder records in the order it ran.

### Where the model broke

`finish_quantified_solve`'s terminal `other =>` arm
(`crates/axeyum-solver/src/auto.rs`) runs two passes and records them in the
opposite order:

1. `prove_unsat_by_mbqi` runs — and records **nothing**.
2. `find_uf_finite_model` (the full rung) runs.
3. `record_quant_rung_declined(UF_FMF_FULL, …)` fires — its segment spans
   **both** passes.
4. `record_quant_rung_result(MBQI, &other)` fires — its segment is what is left,
   which is ~0.

Result: `q:mbqi` reads **0 ms on every file**, and `bound_by=q:uf-fmf-full` has
always meant "MBQI plus the full finite-model finder", never the finder alone.

**This is not a typo.** Step 4's own comment states the intent:

> The ladder is out of rungs above ℕ-induction; record the MBQI family's own
> `unknown` against MBQI rather than leaving the trail's last word to a declined
> probe.

That intent is right. `RouteTrace::last()` is printed as `last=` on every
`--trace` line, and a trail whose final word is "a finite-model probe declined"
on a file whose verdict came from the MBQI family names the wrong thing. So:

- **timing attribution** wants MBQI recorded immediately after its pass;
- **last-word attribution** wants MBQI recorded last;
- **recording at both points double-counts**, because both records tick.

Three orderings, and under the one-record-kind-plus-tick model no ordering
satisfies both readers. That is a design question about the instrument, not a
bug in the call site, which is why it is here and not only in a commit message.

### Why it is worth the ADR rather than a shrug

The consequence is not academic. Lane U1 inherited **56.2%** — "the share of the
UF budget spent on rungs that cannot produce `unsat`" — computed as
`q:uf-fmf-probe + q:uf-fmf-full` off this trail. `q:uf-fmf-full`'s term contains
the whole MBQI pass, and MBQI, unlike the two finite-model rungs, is perfectly
capable of `unsat`. The corrected figure is **52.4%**
([`where-the-uf-clock-goes-2026-09-10.md`](../03-measurements/where-the-uf-clock-goes-2026-09-10.md)).
A published number has already been withdrawn over this defect, and `bound_by`
is the field this repository tells readers to trust on an undecided file.

### A second defect at the same site

`prove_unsat_by_mbqi` returning `CheckResult::Unsat` also falls into the
`other =>` arm. The finite-model block is guarded by
`matches!(other, CheckResult::Unknown(_))` and is therefore skipped — but the
`record_quant_rung_declined(UF_FMF_FULL, NotApplicable)` immediately below it is
**not** inside that guard. So on an MBQI refutation the trail records a rung that
never ran as having declined, and charges it MBQI's entire wall clock. Both
halves of that entry are false. It is the same confusion — a record placed by
control flow rather than by what actually executed — so it is decided here too.

## Decision

**`RouteTrace` separates a segment's COST from a rung's VERDICT, by making the
cost MOVABLE rather than by adding a second record kind.** One primitive pair is
added to the existing model:

```rust
/// Closes the currently open segment, REMOVES it from the running clock, and
/// returns its duration. The caller now OWNS that duration and is obliged to
/// charge it to exactly one attempt.
pub fn take_open_segment(&mut self) -> Duration;

/// Pushes an attempt carrying a CALLER-SUPPLIED elapsed instead of ticking.
pub fn record_result_with_elapsed(&mut self, route, result, elapsed: Duration);
```

They are one feature, not two. `take_open_segment` restarts the clock, so the
duration it returns is no longer inside any future tick; `record_result_with_elapsed`
puts it back on the attempt that earned it. The total is invariant **by
construction**: every nanosecond is either inside exactly one tick or inside
exactly one taken segment, and a taken segment is re-attached exactly once.

Two thread-local sinks expose the pair to the ladder, matching the existing
`record_front_door*` shape and gated on `attribution_collecting()` so a default
run reads no clock and allocates nothing:

```rust
pub(crate) fn take_attribution_open_segment() -> Duration;
pub(crate) fn record_quant_rung_result_with_elapsed(route, result, elapsed);
```

The terminal arm then reads:

```rust
let mbqi_result = prove_unsat_by_mbqi(arena, assertions, &mbqi_config)?;
let mbqi_elapsed = route_trace::take_attribution_open_segment();  // MBQI's own cost
…
// (the full finite-model rung runs here and ticks only its own segment)
route_trace::record_quant_rung_declined(UF_FMF_FULL, …);
route_trace::record_quant_rung_result_with_elapsed(MBQI, &other, mbqi_elapsed);
```

MBQI keeps the last word **and** its seconds. `q:uf-fmf-full` keeps its own
segment and only its own.

The second defect is fixed by moving the `UF_FMF_FULL` decline record **inside**
the `matches!(other, CheckResult::Unknown(_))` guard, so the rung is recorded
exactly when it ran. On the MBQI-`unsat` path the trail is now
`… q:mbqi decided unsat` with MBQI's real cost, and no `q:uf-fmf-full` entry at
all — which is what happened.

### Why not the alternatives

**Two record kinds — a cost record and a verdict record.** Rejected. It breaks
the `attempts().len() == elapsed().len()` alignment that `decided_by`,
`bound_by`, `render_json` and every external consumer index on, and it makes the
JSON carry attempts with no outcome, which *is* a shape change and *would* need
a schema bump. It also does not describe the situation: MBQI is one pass with one
cost and one verdict. Nothing about it is two events.

**An explicit duration on the record, without `take_open_segment`.** Rejected —
this is the trap, and it is worth naming because it is the obvious half of the
fix. Handing MBQI its measured duration while the intermediate `UF_FMF_FULL`
record still ticks over the same interval charges MBQI's seconds **twice**:
once inside the finder's segment, once on the explicit record. `total_elapsed()`
inflates, and `total_ms=` is the denominator every published share divides by. A
fix that moved the distribution *and* the total would be indistinguishable, in
the artifact, from a fix that worked. The taking is what makes it a move.

**Record eagerly and let the last verdict win for `bound_by`.** Rejected. It
needs either two MBQI entries in the trail — a trail that says a rung ran twice —
or `bound_by` and `last` disagreeing about which index is MBQI. And
`decided_by()` deliberately returns the **last** `Decided` entry, so a duplicate
silently changes which attempt is reported as the decider on the `Sat` paths that
already record MBQI correctly.

**Leave it and document the trail as "cost is charged to the next recorder".**
This was a live option — it is at least honest, and it costs nothing. Rejected
because the honest description does not help the reader who is looking at
`bound_by=q:uf-fmf-full` and drawing a conclusion. The already-withdrawn 56.2%
was produced by someone who had read the caveat: the source document states the
defect 120 lines above the number that depends on it. A caveat three links from
the field it qualifies has been tested here and it did not hold.

## Consequences

### What breaks — the JSON schema does NOT

**`ROUTE_TRACE_JSON_SCHEMA_VERSION` stays at 1.** No member is added, renamed or
removed. `to_json` is byte-identical (it never carried timing).
`to_json_with_timing`'s `elapsed_ns` keeps exactly the meaning it documents —
"this attempt's own cost" — and now delivers it. What changes is *which* attempt
a given number lands on: a value change, not a shape change. The version field
exists so a consumer can reject a rendering it cannot parse; every consumer can
still parse this one, and a reader that rejected on a bump would be rejecting the
correction it wants.

Who reads the rendering, and what each sees:

| reader | what it reads | effect |
|---|---|---|
| `crates/axeyum-bench/examples/smtcomp_cli.rs` (`; route …`, `; route-trail …`) | `decided_by` / `bound_by` / `last` / `bound_ms` / `total_ms`, then `to_json_with_timing` | `bound_by` and `bound_ms` change on files where MBQI dominated. `total_ms` does not. This is the fix. |
| `bench-results/route-attribution-2026-09-07/scripts/aggregate.py` + `run_division.sh` | the `; route` fields as TSV | recorded numbers are historical; re-running gives corrected ones |
| `bench-results/parity-losses-20260908/scripts/abv-ab.sh` | `bound_by=` | same |
| `bench-results/uf-arith-overbound-20260908/scripts/analyze.py` | `bound_by=` | same; its subject is `uf-arith-online`, not touched |
| `crates/axeyum-solver/src/span_log.rs` | `RouteTrace::elapsed`, `bound_by`, `open_segment` | unchanged mechanism; the spans it emits carry the corrected split |

Committed artifacts under `bench-results/` are **not** rewritten. They are dated
measurements of the instrument as it was, and are labelled where they are read.

**Published shares move.** Every figure derived from `q:uf-fmf-full`'s segment on
the UF population overstates it, and every `q:mbqi` figure understates it. The
sweep and the corrections are the accompanying note under
`docs/research/03-measurements/`.

**`elapsed` stops being chronologically monotone with respect to `attempts`
order** at the one site that takes a segment. `elapsed[i]` remains "attempt `i`'s
own cost" — which is what it has always been documented as, and what every
consumer uses it for — but the *intervals* are no longer in trail order. Nothing
reads them as an ordered timeline; `bound_by` maximises, `total_elapsed` sums,
and `render_json` emits per attempt. Documented on `take_open_segment` so the
next reader is not surprised.

### What does not change

**No verdict changes.** Every new call is a statement-level side effect between
two existing statements, gated on `attribution_collecting()`, and none appears in
a branch condition — the same structural argument the module already makes for
its verdict-invariance contract. Confirmed empirically on the UF parity slice
rather than asserted.

### The obligation this creates

`take_open_segment` hands the caller a duration that is no longer accounted for
anywhere. A caller that takes a segment and then drops it **silently loses time
from the total** — the one failure mode this design admits that the old one
could not have. The guard is the total: a test pins that a take/re-attach pair
leaves `total_elapsed()` equal to the un-taken run, and the accompanying
measurement checks the trail total against the whole solve before and after.
Any future use of `take_open_segment` owes the same check.

### Still open, deliberately not decided here

`q:egraph` records `DeclineReason::NotApplicable` rather than the instantiation
loop's own `UnknownReason`, so the trail cannot distinguish "the e-graph was not
applicable" from "the e-graph saturated". That is the second of the two recording
defects named in
[`instantiation-strategy-gap-2026-09-10.md`](../03-measurements/instantiation-strategy-gap-2026-09-10.md);
it is a decline-*vocabulary* question, not a cost/verdict one, and it does not
move any clock share. It stays open.
