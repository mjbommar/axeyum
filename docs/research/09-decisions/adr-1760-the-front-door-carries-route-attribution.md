# ADR-1760: The front door carries route attribution, and "bound by" is a separate field from "printed last"

Status: accepted
Index-summary: Route attribution moves from the diagnostic path to the shipped front door. `RouteTrace` existed but was reachable only through `check_auto_explained`, which decides the FLAT ASSERTION VIEW — the path that disagrees with the front door on 134 of 397 benchmarks, because `solve_smtlib` decides in thirteen places and only one of them is `check_auto`. `RouteAttributionGuard` is opt-in, off by default, thread-local and composed onto the existing `--trace` flag (the fourth guard of the same shape, not a fourth style); with it off the cost is one `Cell<bool>` read per site, no clock, no allocation. Verdict invariance is inherited, not newly claimed: the outermost `check_auto` takes its result from `check_auto_explained`, whose agreement with `check_auto` is the invariant `route_trace` already exists to uphold; a depth counter keeps nested sub-solves out. `decided_by` (last decisive entry, positional) and `bound_by` (most expensive segment, timed) are separate fields computed from separate data, because classifying a file by the route that spoke last was refuted on 67 of 70 files in two divisions and turned 23 "admission declines" into timeouts.
Index-status: accepted
Date: 2026-09-07

## Context

We ship 48 labelled dispatch routes and could not say which one decided any file
we solve. Causes were recorded only for files we **lose**, and those causes have
been wrong repeatedly and expensively:

- a census classified 403 files by the last route's message and was refuted on
  **67 of 70** in two divisions;
- an admission bound was found to be the message rather than the constraint on
  **25 of 62** files (ADR-1751);
- one division's "23 admission declines" turned out to be timeouts.

The instrument that should have answered this already existed. `route_trace.rs`
has carried `RouteTrace`, `RouteAttempt`, `RouteOutcome` and `DeclineReason`,
exported from `lib.rs`, with a verdict-invariance contract and a differential
gate. The problem was never the data model. It was **reachability**: the only
way in was `check_auto_explained`, and `explain_corpus` — the consumer built on
it — disagrees with the shipped front door on **134 of 397** benchmarks. Its own
banner says it is diagnostic-only.

## The measured reason the two disagree

Reading `solve_smtlib_at_string_bound`, the front door decides in **thirteen**
places, and `check_auto` is one of them:

```
fd:parse
fd:word-only-fallback          -- source-first word-only parse fallback
fd:source-fp-prefix            -- FP prefix monotonic fold
fd:source-string               -- source-level string ladder, first refusal
check_auto                     -- THE FLAT ASSERTION VIEW
fd:string-gate                 -- StringGate confirmation
fd:source-string-semantic-unsat
fd:word-route                  -- flat word-equation second chance
fd:online-string               -- online CDCL(T) string second chance
fd:membership                  -- regex-membership second chance
fd:lex-order                   -- lexicographic-order second chance
fd:length-lia                  -- length-to-LIA second chance
fd:source-string-sat-probe     -- bounded concrete source-witness probe
fd:bounded-completeness-unsat  -- bounded-completeness unknown -> unsat upgrade
```

Each of those can supply the file's verdict on its own. So attribution read off
`check_auto_explained` is not a noisier answer to the same question — it is an
answer to a different one, about a decision procedure we do not ship. That fully
explains the 134/397 divergence, and it is why the fix has to be at the front
door and cannot be a better `explain_corpus`.

## Decision

**1. Attribution is available from the front door, opt-in and off by default.**

`RouteAttributionGuard::enable()` is a thread-local guard that restores the
previous setting on drop and clears its accumulator on enable —
byte-for-byte the shape of `FrontDoorStatsGuard`, `BvLayerStatsGuard` and
`DlOnlineStatsGuard`, which landed this week. It is wired to the **existing**
`--trace` / `AXEYUM_TRACE=1` flag in `smtcomp_cli`, adding no CLI surface. This
is deliberately not a fourth style: three guards of one shape is a convention,
and a fourth variant would be the beginning of a mess.

With collection off, each recording site costs one thread-local `Cell<bool>`
read. No clock is read and nothing is allocated. The single `format!` on the
parse stage sits **inside** the collecting test rather than relying on
`record_front_door` to discard its argument, because the discard happens after
the allocation.

**2. Verdict invariance is inherited, not newly asserted.**

When the guard is live, the **outermost** `check_auto` takes its result from
`check_auto_explained` and absorbs that call's trace. Those two returning the
same verdict for every query is precisely the invariant `route_trace` exists to
uphold and `tests/route_trace.rs` already pins. Nothing about the dispatch is
re-plumbed to make attribution work.

`check_auto` is called recursively from a dozen routes (IMC, PDR, quantifier
instantiation, the conjunct/disjunct refuters, the finite-domain splitter). A
depth counter keeps those on the unchanged plain path. Without it a file's trail
is dominated by whichever route recursed the most and "which route decided this
file" becomes unanswerable — the failure mode is not noise, it is inversion.

The end-to-end property is still checked directly rather than argued:
`tests/route_attribution.rs` solves the committed 152-file regression corpus
with the guard off and on and requires identical verdicts. Measured: 152 files,
0 mismatches.

**3. `decided_by` and `bound_by` are separate fields computed from separate
data.**

This is the substantive half of the decision, and it is a direct response to the
three refutations above.

- `decided_by` is the **last** `Decided` entry — a **positional** read. Last and
  not first because the front-door ladder legitimately re-decides: measured on a
  UFLIA query, the quantifier loop re-dispatches once per instantiation round and
  three rounds decided `sat` before a final round decided `unsat`. The first
  decisive entry would have named the wrong verdict's route.
- `bound_by` is the **most expensive** segment — a **timed** read. On an
  undecided file this is the route that consumed the budget, which is the route
  a portfolio would have to beat and the one that says whether more budget, a
  better route, or parallelism is the fix.
- `last` is reported **alongside** both, never instead of either. It is the
  field that was wrong on 67 of 70, and a consumer that wants it should have to
  ask for it by name rather than receive it under another name.

All three are printed on every file, so no consumer ever has to infer one from
another. `bound_ms` and `total_ms` accompany them, so "one route ate the whole
budget" is distinguishable from "the budget was spread over twenty cheap
declines" — two situations with opposite implications for a portfolio.

## Consequences

The per-division parity sweep gains route columns
(`bench-results/route-attribution-2026-09-07/`), so a normal parity run now
records which route decided each file rather than requiring a bespoke census.
Every past census that classified by the last route's message can now be
re-derived from data instead of re-argued.

The gate carries an explicit **anti-vacuity** test. "Enabling attribution
changed no verdict" is satisfied perfectly by an instrument that records
nothing, so the invariance test alone cannot detect a collector that silently
went dead; `attribution_is_not_vacuous` fails if coverage, deciding-route
naming, or label diversity collapses. Likewise the guard-off test carries its
own positive control, so its negative result cannot be vacuous.

What this does **not** provide is a way to run a single route in isolation.
`SolverConfig` has no route-selection knob, so a strict virtual-best over our
own routes — each route run alone on each file — is not measurable from this
change. What the sequential trail does support is stated with its bounds in
`docs/research/12-performance/route-attribution-2026-09-07.md`: for every file,
each route tried before the winner is a measured NO, the winner is a measured
YES, and every route after it is UNKNOWN. Route diversity read off the deciding
route is therefore an **upper bound**, and any portfolio claim must be stated
as such.

## Alternatives rejected

**Widen `explain_corpus`.** It classifies from the flat view by construction and
its own banner calls it diagnostic-only. Making it more accurate about the wrong
decision procedure does not make its answers transfer.

**Thread a `&mut RouteTrace` through the front door.** The recorder is already
threaded through `check_auto`'s dispatch that way, so the symmetry is tempting.
It would change the signature of `solve_smtlib` and every function between it
and the thirteen stages, for a diagnostic that is off by default — and the three
guards that landed this week established the thread-local convention precisely
to avoid that.

**One `route=` column instead of three.** This is the option that produced every
refutation in the Context section. A single column forces the consumer to decide
what it means, and the historical answer has been "the route that printed last",
which is a message rather than a constraint.
