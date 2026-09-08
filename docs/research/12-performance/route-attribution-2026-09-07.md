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

## The sweep: 1,200 files, 12 divisions

`bench-results/route-attribution-2026-09-07/`. First 100 files of each committed
parity list, 24 s wall, 8 GiB `ulimit -v`, one process per division on an idle
16-core host.

Parity lists rather than the loss-census lists, deliberately: they carry files
we win as well as files we lose, and a loss-only population has no deciding
routes to distribute — which is the entire question.

| | |
| --- | --- |
| files | 1,200 |
| with a route trail | 1,104 |
| **without a trail** | **96 — all `unsolved`** (see the blind spot below) |
| decided | 754 |
| unsolved | 350 |
| distinct deciding routes | **20** |

### Finding 1 — "printed last" was wrong on 348 of 350 losses

On files we lose, the route that **consumed the budget** is not the route that
**printed last** on **348 of 350** (99.4%).

Every one of those would be misclassified by a last-message census. This is not
a re-litigation of the earlier refutations (67 of 70 in two divisions, the 23
"admission declines" that were timeouts) — it is the same error measured
directly, at population scale, by an instrument that reports both fields.

The binding routes are also not the ones a last-message reading would name:

```
dl-online 95   nia-linearize 49   nra 41   uf-arith-lazy-overbound 30
int-blast-ladder 28   euf-online 28   fd:parse 26   fd:string-gate 17
uf-arith-lazy-overbound-pre-lia 16   qf-bv 7   lia-simplex 5 …
```

`fd:parse` binding **26** files is worth stating on its own: those files spent
more time in ingest than in any route, so no route was ever the constraint. No
instrument in this tree could have said that before, and a census classifying by
dispatch messages would have attributed all 26 to a solver route.

### Finding 2 — no route dominates, and 63% of QF_SLIA is decided outside `check_auto`

20 distinct routes decide the 754 decided files, and the head is flat:

```
dl-online 161   euf-online 133   qf-bv 90   nra 69   fd:source-string 53
abv-online-cdclt 50   lia-dpll 47   lia-simplex 38   array-fast-path 32
int-blast-ladder 31   fd:string-gate 10   uf-arith-online 10 …
```

The largest single route decides 21% of what we decide. There is no one engine
carrying the system.

Two of those labels — `fd:source-string` (53) and `fd:string-gate` (10) — are
**front-door stages that `check_auto_explained` cannot see at all**. In QF_SLIA
they account for 63 of 97 decided files. That is the 134/397 divergence made
concrete: on that division, a flat-view instrument is blind to two thirds of the
decisions.

### Finding 3 — the virtual best, and why the portfolio answer is NO

**Method and its limits.** A strict virtual best runs each route alone on each
file. `SolverConfig` has no route-selection knob, so that is **not measurable**
and is not claimed. What a sequential trail gives, per file, is three-valued:
every route before the winner is a measured NO, the winner is a measured YES,
every route after it is UNKNOWN. So the deciding-route distribution above is an
**upper bound on route diversity** — a file credited to route R might also have
fallen to a later route that never got a turn. Redundancy could be higher than
20 routes suggests; it cannot be lower.

The recoverable wall time, by contrast, is exact.

On the **754 decided files**:

| | |
| --- | --- |
| sequential in-dispatch time | 1,394 s |
| shared preamble (parse + fragment probe) | 39 s |
| spent in routes that declined before the winner | **347 s** |
| the winning route's own time | 1,009 s |
| **recoverable share** | **24.9%** |
| projected portfolio time (preamble + winner) | 1,048 s |
| **projected speedup** | **1.33x** |
| winner was not the first route tried | 701 of 754 (93%) |

Shared preamble is excluded because every arm of a portfolio pays it. Counting
it as recoverable is a mistake the first draft of `aggregate.py` made, and it
inflated QF_SLIA from 63% to 84%.

On the **350 lost files** — where the real prize would be — the binding route
**already holds a median 84% of the in-dispatch time**:

| | |
| --- | --- |
| binder held >90% of the trail | **166 of 350 (47%)** |
| binder held <50% | 52 of 350 (15%) |
| mean binder share | 76% |

**The answer to the strategic question is no.** A portfolio over 16 idle cores
is not the largest available win:

- On files we already decide it buys **1.33x wall time** — real, but a constant
  factor on work that already succeeds.
- On files we lose, the binding route is already single-threaded and already
  holds nearly all the budget. Handing it 15 more cores hands it nothing. For
  the 166 files where the binder held over 90%, parallelism is arithmetically
  incapable of helping: there was no queue in front of it to remove. Those files
  need a better route or a better algorithm inside the binding route.
- The honest upper bound on new decisions from parallelism is the **52 files
  (15% of losses)** whose binder held under half the trail and would get more
  than 2x its time. Whether any of them would then decide is not measured — a
  route given 2x budget is not a route that succeeds.

The routes are **not** largely redundant — 20 of them decide disjoint work, and
that is a genuinely good answer for the dispatch design. But route diversity and
portfolio value are different questions, and the second one comes out negative
because the losses are bound by single-route depth, not by queueing.

### The blind spot, stated rather than absorbed

**96 of 1,200 files printed no route line, and every one was `unsolved`.**

That is the watchdog-timeout path: the worker thread's thread-locals are not
readable from the main thread when `recv_timeout` gives up, the same limitation
the other three `--trace` instruments carry. So the instrument is blind on
exactly the population it most exists to explain — the hard losses.

This is not closed here; closing it means making the collector cross-thread.
What is fixed is the **silence**: the watchdog path now prints
`; route unavailable: <reason>`, so an aggregation can count what it cannot
attribute instead of quietly shrinking its own denominator. A coverage number
that drops files it never saw is how a stable number becomes a wrong one.

Every figure above is therefore over the 1,104 files with a trail, and the 96
are reported, not dropped.

## "No measurable cost with collection off" — measured, not asserted

The gating argument (one `Cell<bool>` read, no clock, no allocation) is a claim
about the code. It is now a claim about the binary:
`bench-results/route-attribution-2026-09-07/cost_ab.{sh,py,tsv,txt}`.

Two prebuilt release `smtcomp_cli` binaries — baseline at `9d40c1ec8`
(pre-attribution) and new at `4853ad9fd` — over the same 60 files (first 30
`QF_BV` + first 30 `QF_LIA` of the parity lists), 3 repetitions, **alternating
arms** so machine drift is shared rather than accumulating on the second arm,
and **no `--trace`** on either: the question is the default path.

| | |
| --- | --- |
| total baseline | 172,829 ms |
| total instrumented | 172,740 ms |
| ratio | **0.9995** |
| median per-file delta | **+0.0000%** |
| verdict | no measurable cost (3% threshold) |

The scorer also cross-checks verdicts between the two binaries and refuses to
report any timing number if they ever disagree — a second, independent
confirmation of verdict invariance, taken from the shipped binary rather than
the library. It did not fire.

**And the instrument was shown able to see a regression.** `--self-check`
injects a synthetic 5% slowdown into the new arm and requires the verdict to
flip: it reads +4.55% and reports REGRESSION. Without that, "no measurable
cost" would be indistinguishable from an instrument too blunt to measure
anything — which is exactly the failure this repository keeps finding.

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
- `route_attribution_is_verdict_identical_under_a_memory_budget` — the axis the
  corpus sweep is silent on (above).

## What this lane did not do

Stated plainly so the next reader does not have to infer it from absence.

- **No strict virtual best.** Each route run alone on each file is not
  measurable without a route-selection knob on `SolverConfig`, and adding one is
  a dispatch change with its own soundness surface, not an instrumentation
  change. The recoverable-time figures are exact; the diversity figure is an
  upper bound.
- **The watchdog blind spot is not closed**, only made audible. 96 hard-timeout
  files still carry no trail.
- **`check_auto_explained` still lacks the memory-budget entry guard.** The
  shipped path is correct because `check_auto` now runs it ahead of the
  delegation, but the two functions still differ and `explain_corpus` still
  inherits the difference.
- **Whether the 52 recoverable-headroom losses would actually decide with more
  budget is not measured.** A route given 2x its time is not a route that
  succeeds, and claiming those 52 as portfolio wins would be exactly the kind of
  inherited-number error this lane exists to stop.
