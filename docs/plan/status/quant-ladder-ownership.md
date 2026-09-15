# Lane: quant-ladder-ownership — the other ladder, and the budget its continuation needs

<!-- plan-section: lane-status -->

**Lane quant-ladder-ownership (`IN PROGRESS`, quant-ladder-ownership,
2026-09-15).** The second half of Phase 1 of
[docs/plan/dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md),
closed by
[ADR-2103](../../research/09-decisions/adr-2103-quantified-ladder-ownership-and-bounded-continuation.md).
[ADR-2100](../../research/09-decisions/adr-2100-typed-route-ownership.md) typed
the quantifier-free dispatch ladder and measured that **482 of 643 undecided
Tier 1 rows — 75 % — never reach it**, ending instead on the `q:` rungs of the
quantified ladder in `solve`; it named typing that one as the obvious next
slice and published **two stable losses** it declined to trade the rule for.
This lane is both.

Branch base: `7d922fe58`, local `main` at ADR-2100's merge.

## The sizing, first and unflattering

**The ceiling over the 482 is ZERO — for every possible ownership table**, not
just the one this lane ships. No row in the population had its ladder ended by a
rung's non-decision at all: **211 ran out of rungs and 271 ran out of clock**.
The ADR says so up front rather than implying a gain, and the lane's value is
the bug class, exactly as the dispatch plan frames Phase 1.

| division | rows | candidate | clock | watchdog | exhausted |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 67 | 1 | 12 | 0 | 54 |
| AUFLIRA | 20 | 0 | 16 | 1 | 3 |
| UF | 108 | 48 | 19 | 6 | 35 |
| UFDTLIRA | 50 | 1 | 0 | 0 | 49 |
| UFLIA | 107 | 3 | 68 | 7 | 29 |
| UFNIA | 130 | 0 | 80 | 9 | 41 |
| **total** | **482** | **53** | **195** | **23** | **211** |

The 53 candidates are the clock too, refuted from the **wall clock** rather than
from another record: all 53 between 24,015 and 24,950 ms against a 24,000 ms
budget, 0 under 90 % of it.

**Three corrections the sizing's own runs produced**, each of which would have
been a published claim:

- `RouteTrace::record_result` maps `Unknown` to `record_declined`, so testing
  `outcome != "declined"` for a terminal unknown returned **0 of 482** — what a
  detector that cannot fire prints.
- **Six rungs record nothing when they decline**, so their absence from a trail
  is not evidence of a skip; treating it as one reports all 482 as candidates.
- The candidate list was **capped at 40**, and the checker verified 40 of 53
  while printing "EVERY".

**The finding worth more than the ceiling.** Those 53 rows exit through the one
budget exit in the quantified ladder that **records nothing** —
`finish_quantified_solve_or_induct`'s `config_with_remaining_timeout` guard,
where every other exit goes through `quantified_timeout`. 11 % of the
population, and 48 of `UF`'s 108, were invisible to the `q:timeout` sink. It
records now.

## What changed

`quant_ownership::QuantRoute` — seventeen rungs, `owns`/`kind`/`route`
exhaustive, reusing `Construct`, `ConstructSet`, `RouteKind`, `Ownership` and
`DispatchError` rather than a parallel mechanism. Labels delegate to ADR-2101's
`route_trace::Route`, so the wire strings have one source.

`solve`'s body moved to `solve_inner` over the typed error channel;
**`rustc` named 29 sites**.

The live defects closed, none of them in the sizing's population (which is
`stopped_by_unknown` and so excludes every query whose ladder ended in an error):

- **`q:checked-fast-path` had eight bare `?`s** — a probe's fragment refusal
  became `solve`'s ERROR with the whole ladder below unreached, ADR-1927's
  defect with eight live instances in one function. Its five refutation searches
  were also a `||` chain that **short-circuits**, so one probe declining skipped
  the four below it too.
- **`q:egraph` asked what another route could do.** `mbqi_source_shape_supported`
  is deleted; a refuter owns nothing and its refusal is a decline.
- `q:nat-induction` swallowed every error; `q:eq-partition` and
  `q:unsat-universal` recorded nothing when they declined.

`OWNERSHIP_CONTINUATION_SHARE` — the rungs below a converted non-decision get a
quarter of the remaining clock, **only inside a quantified rung's sub-solve**,
because at the outermost dispatch the continuation is the answer and capping
there would pay for ADR-2100's two losses with its two gains. Its nesting signal
is a **new unconditional counter**: `route_trace`'s is gated on attribution, so a
budget policy keyed on it would branch one way under `--trace` and the other
without.

## Nine red assertions, and every one was this lane's bug

The first patch turned **nine** assertions red in five suites — ADR-1966's
experience, one suite wider. The message was the finding: the four
quantifier-free HAND-OFFS are ladder **tails**, so routing their `check_auto`
through the decline funnel broke ADR-1980's `propagate` lever and replaced its
sentence with an invented `"quantified solve time budget exhausted"` — a message
simply false about what happened. Reclassified as propagation, **all nine came
back and no assertion was weakened.**

## Landed changes

| commit | what |
|---|---|
| `531a593eb` | the sizing: 0 of 482, per division, and the five scripts, before any Rust |
| `2d7ecb967` | `quant_ownership`, the 29 typed sites, the deleted cross-route predicate, the bounded continuation |

<!-- /plan-section -->
