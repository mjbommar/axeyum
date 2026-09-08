# Route attribution from the front door (2026-09-07)

Lane `route-attribution`. Working diary; measurements appended as they land.

## The gap

19+ dispatch routes, and no way to say which one decided a file we solve. We
recorded causes only for files we LOSE, and those causes were wrong repeatedly:

- a census classified 403 files by the last route's message and was refuted on
  67 of 70 in two divisions;
- an admission bound was found to be the message rather than the constraint on
  25 of 62 files;
- one division's "23 admission declines" turned out to be timeouts.

`route_trace.rs` already had `RouteTrace` / `RouteAttempt` / `RouteOutcome` /
`DeclineReason`. The problem was reachability: it hung off
`check_auto_explained`, which decides the **flat assertion view**, and that path
disagrees with the shipped front door on 134 of 397 benchmarks.

## Why the flat view disagrees (read from the source, not assumed)

Reading `solve_smtlib_at_string_bound`, the front door decides in **thirteen**
places, only one of which is `check_auto`:

`fd:parse` -> `fd:word-only-fallback` -> `fd:source-fp-prefix` ->
`fd:source-string` -> **`check_auto` (the flat view)** -> `fd:string-gate` ->
`fd:source-string-semantic-unsat` -> `fd:word-route` -> `fd:online-string` ->
`fd:membership` -> `fd:lex-order` -> `fd:length-lia` ->
`fd:source-string-sat-probe` -> `fd:bounded-completeness-unsat`

Every one of those can supply the file's verdict on its own. Classifying from
`check_auto_explained` therefore answers a question about a different decision
procedure. That is the whole explanation of the 134/397 divergence, and it is
why the fix had to be at the front door rather than in a wider `explain_corpus`.

## Design

`RouteAttributionGuard` — opt-in, off by default, thread-local, restoring on
drop — following `FrontDoorStatsGuard` / `BvLayerStatsGuard` /
`DlOnlineStatsGuard` exactly (no fourth style, no new CLI surface; it composes
onto the existing `--trace`).

Two halves:

1. **Dispatch.** When the guard is live, the OUTERMOST `check_auto` takes its
   result from `check_auto_explained` and absorbs that call's trace. Verdict
   invariance is not a new claim: those two agreeing for every query is the
   invariant `route_trace` already exists to uphold, pinned by
   `tests/route_trace.rs`. Nested `check_auto` calls (IMC, PDR, quantifier
   instantiation, the refuters) take the unchanged plain path — a depth counter
   keeps them out, because otherwise a file's trail is dominated by whichever
   route recursed the most.
2. **Front door.** Each of the thirteen stages above records its own outcome and
   its own wall time. A second-chance stage is only credited or charged when it
   ran against an `unknown` — otherwise every file would be attributed to
   whichever pass-through stage came last in the ladder, which is exactly the
   error being fixed.

Cost with the guard off: one thread-local `Cell<bool>` read per site, no clock
read, no allocation. The one `format!` on the parse stage sits **inside** the
collecting test on purpose — `record_front_door` would discard the string, but
building it would still allocate.

## decided_by vs bound_by

These read different fields, which is what makes them separable:

- `decided_by` = the **last** `Decided` entry (position). Last, not first,
  because the ladder legitimately re-decides — measured on a UFLIA query below,
  three rounds decided `sat` and were superseded by a final `unsat`.
- `bound_by` = the **most expensive** segment (timing). On an undecided file
  this is the route a portfolio would have to beat.
- `last` is reported alongside both, so a consumer never infers one from the
  other. `last` is the field that was wrong on 67 of 70.

## First end-to-end measurement

`smtcomp_cli --trace` on a UFLIA query, front door, release build:

```
; route decided_by=lia-dpll bound_by=dl-online last=lia-dpll bound_ms=0 total_ms=1 attempts=29
```

29 attempts across **four** top-level dispatches: the quantifier loop above
`check_auto` re-dispatches the whole query once per instantiation round
(`uf-arithmetic` decided the candidate `sat` three times, then `lia-dpll`
decided `unsat`). `decided_by` correctly names the last one. This is the case
that justifies "last decided" over "first decided", and it was found by an
assertion of mine being wrong, not by the code being wrong.

## A divergence this work surfaced: the memory-budget entry guard

Delegating to `check_auto_explained` rests on the two functions being verdict-
identical. Checking that claim rather than assuming it found that they are
**not**, on one axis:

`check_auto` runs `memory_budget_decline(config, "check_auto entry")` before
dispatching. `check_auto_explained` does not. So a query under a memory budget
that `check_auto` declines at the door would, under naive delegation, run the
whole dispatch instead — a real verdict change on exactly the axis
`smtcomp_cli --memory-limit-mb` exercises.

This is **pre-existing**, not introduced here. `tests/route_trace.rs` claims
verdict invariance between the two functions, but its differential corpus never
sets `memory_limit_mb`, so it passes on this axis without testing it — a gate
green for the reason a gate is green when it does not look.

Repaired by running the entry guard in `check_auto` **ahead of** the attribution
branch, so both paths are gated by it, and pinned by
`route_attribution_is_verdict_identical_under_a_memory_budget`, which carries a
positive control so a budget too large to decline cannot make it agree
trivially. `check_auto_explained` itself is left alone: making it carry the
guard would change `explain_corpus`'s behaviour under memory limits, which is a
separate decision with its own consumers.

The general lesson is the one CLAUDE.md already states, met head on: an
inherited invariant is a claim, and the corpus that pins it may be silent on the
axis you are about to use it for. Check which axes the pinning population
actually varies.

## Gate

`crates/axeyum-solver/tests/route_attribution.rs`, over the committed 152-file
regression corpus:

- `attribution_does_not_change_any_verdict` — 152 files, 0 mismatches.
- `attribution_is_not_vacuous` — the anti-vacuity guard. "No verdict changed" is
  satisfied perfectly by an instrument that records nothing, so the invariance
  test alone cannot detect a dead collector.
- `nothing_is_recorded_with_the_guard_off` — carries its own positive control,
  so its negative result cannot be vacuous.
- `bound_by_is_separable_from_printed_last` — asserts on a constructed trace
  that the two can name different routes. A corpus-only version would pass
  vacuously on a corpus where they happen to coincide.
- `decided_by_agrees_with_the_returned_verdict`.
- `nested_dispatch_does_not_flood_the_attribution`.
