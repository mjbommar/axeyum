# ADR-1941: `attempts=` alone cannot classify a census row — the open segment is the discriminator

Status: accepted
Index-summary: ADR-1936's `attempts=` test needs a second field: a census row is UNCLASSIFIED when the budget is in an unattributed OPEN SEGMENT, not merely when `attempts=` is below the division's maximum, because ladder length is query-dependent.
Index-status: accepted
Date: 2026-09-12

## Context

[ADR-1936](adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md)
requires a blocker census to record `attempts=` per file and to mark
`UNCLASSIFIED` any row whose dispatch did not reach the end of the ladder. It
also says, concretely: "record the ladder length the division's dispatch reaches
when it completes."

The `board-fpbv` lane took that rule literally on three divisions
([board](../../../bench-results/fpbv-divisions-headtohead-20260912/README.md))
and hit the question the rule leaves open: **how do you know the ladder length?**
The only thing a census can observe is the maximum `attempts=` it saw. Using
that maximum as the ladder length is what this lane did first, and on `QF_UFBV`
it produced a result that is stable, reproducible, and wrong:

| division | rows | max `attempts=` | UNCLASSIFIED by the max rule |
|---|---:|---:|---:|
| QF_ABVFP | 21 | 14 | 20 |
| QF_UFBV  | 87 | 18 | 77 |

The `QF_ABVFP` number is right. The `QF_UFBV` number is not, and the two are
distinguished by a field that was already being printed:

- On `QF_ABVFP`, the 20 rows stop at `attempts=3` or `5` and every one carries a
  `; route-open ms=24982 after=dl-online attributed_ms=17` line. **24.98 s of a
  25 s budget is in a segment no route attempt covers.** The dispatch did not
  finish; something it entered never returned.
- On `QF_UFBV`, the 77 rows stop at `attempts=14` or `15` and **87 of 87 rows
  have no `route-open` line at all**, with `bound_ms` ≈ `total_ms` (median
  770 ms of 829 ms at `attempts=14`). The budget is fully attributed to recorded
  attempts. Those dispatches ran to the end — of a **shorter ladder**.

Ladder length is query-dependent: a query whose fragment admits fewer rungs
reaches fewer rungs, and `check_auto` is a ladder over fragments, not a fixed
list every query walks. `QF_UFBV` rows at `attempts=14` and at `attempts=18`
end on the **same** give-up reason (the `MAX_THEORY_ATOMS` cap), which is not
what a truncated-versus-complete pair looks like.

Marking those 77 `UNCLASSIFIED` is conservative in the sense ADR-1936 intends —
it never promotes a bad row — but it is not free. It hid a finding that the
corrected reading makes obvious: **84 of 87 winnable `QF_UFBV` files are stopped
by exactly two hardcoded constants**, 53 by `MAX_THEORY_ATOMS = 1_024` and 31 by
`MAX_INPUT_DAG_NODES = 16_384`. A rule that renders that as "77 unrankable" is a
checker that cannot distinguish "we did not measure this" from "we measured it
and the answer is a constant".

## Decision

**A census row is `UNCLASSIFIED` when its budget is in an unattributed OPEN
SEGMENT — not merely when `attempts=` is below the division's observed maximum.**

Concretely, extending ADR-1936's four steps rather than replacing them:

1. Record `attempts=` on every row, as ADR-1936 requires. It stays.
2. **Also record whether the row carries a `; route-open` line, and its
   `ms=` / `after=`.** This is the discriminator and it needs no new instrument
   — `route_attribution_report_lines` already prints it.
3. A row with a `route-open` segment covering a material share of its budget is
   `UNCLASSIFIED`. Its give-up reason describes the dispatcher and must never be
   ranked. This is the `QF_ABVFP` case and ADR-1936's original target.
4. A row with **no** `route-open` line and `bound_ms` ≈ `total_ms` ran to the end
   of *its own* ladder and **may be ranked**, even when its `attempts=` is below
   the division maximum. This is the `QF_UFBV` case.
5. `attempts=` below the maximum with no open segment is still **reported** — as
   the ladder length that query reached — because a division whose rungs vary
   widely is itself worth knowing. It is a column, not a disqualification.
6. When a census publishes a partition, it publishes **both** readings when they
   differ, and says which one it ranks by and why. The `attempts=`-only reading
   is evidence, not an error to be hidden.

## Consequences

- The rule stays falsifiable in the direction that matters. `QF_ABVFP`'s 20 rows
  are still `UNCLASSIFIED` under this ADR, for a reason that is now stated as a
  measurement (24.98 s unattributed) rather than as an inequality between two
  numbers.
- It costs one more column. Like ADR-1936's, the field is already printed.
- **It does not weaken ADR-1936; it makes it checkable.** ADR-1936 says "compare
  against the ladder length" and leaves the census to guess that length. This
  says what to observe instead of guessing.
- A census that reports only `attempts=` is now incomplete rather than wrong.
  Existing censuses should be re-read for whether their `UNCLASSIFIED` rows
  carried open segments; where they did, the conclusion stands unchanged.
- The `route-open` line's own wording already carries the warning this ADR
  formalises: *"bound_by is NOT the answer: most of the budget is in the open
  segment."* That note was being printed and not read, which is the same failure
  mode ADR-1936 describes for `attempts=`.

## Alternatives considered

- **Make the ladder length a known constant per logic and compare to it.** This
  is the reading ADR-1936 most naturally suggests, and it is the right long-term
  answer *if* the dispatcher exposes it. It does not today, and a census cannot
  wait on that: the way you discover the ladder is query-dependent is by taking a
  census and noticing the rows disagree. Same inversion ADR-1936 rejects when it
  declines to require a fix before a measurement.
- **Take the maximum `attempts=` as the ladder length and accept the
  conservatism.** What this lane did first. It is sound but lossy, and the loss
  is not uniform: it scales with how much rung count varies across a division,
  so the divisions it damages most are the heterogeneous ones where a census is
  most valuable. On `QF_UFBV` it would have suppressed a 61 % single-constant
  finding.
- **Rank everything and note the caveat in prose.** This is what ADR-1936 exists
  to forbid, and the `QF_ABVFP` rows in this same lane are a live example of why:
  their give-up reason is `Watchdog`, which is a fact about the harness.
- **Use `bound_ms`/`total_ms` alone without `route-open`.** Nearly equivalent on
  the data here, but it degrades silently when a row's dispatch is fast and
  entirely unattributed, whereas the absence of the `route-open` line is a direct
  statement by the instrument. Both are recorded; the line is the primary test
  and the ratio corroborates it.
