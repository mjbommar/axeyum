# ADR-1950: a ROUND budget and a CLOCK budget are different findings — a census must not merge them

Status: accepted
Index-summary: A blocker census must split "budget exhausted" by WHICH budget — a round/iteration COUNT or the wall clock — and publish the remaining-budget distribution beside the count, because the two have different remedies and the merged bucket reads as the one that is wrong.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1936](adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md)
says which census rows may be ranked;
[ADR-1941](adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md)
says how to tell a finished dispatch from a truncated one. Neither says anything
about what a ranked reason *means*, and the `board-six` lane hit a case where
the ranking is correct under both ADRs and still points the next lane at the
wrong lever.

That lane censused 390 winnable files across six divisions
([board](../../../bench-results/six-divisions-headtohead-20260912/README.md)).
Its brief predicted the dominant blocker would be `quantified solve time budget
exhausted after e-matching` — a wall-clock exhaustion — and asked whether it was
one finding or five. The prediction was reasonable and it was wrong, in a way
that a reason-string ranking cannot show:

| reason | n | median budget REMAINING at give-up |
|---|---:|---:|
| `e-matching instantiation did not refute within the round budget` | 177 | **23,994 ms of 24,000** |
| `quantified solve time budget exhausted after e-matching` | 24 | 51 ms **over** budget |

Both read, in a ranked list, as "we ran out of budget". They are opposite
findings. The 177 rows — **45 % of the whole winnable set, spanning four
divisions** — stop against an iteration COUNT with the clock essentially
untouched: raw rows read `attempts=19 bound_ms=0 total_ms=3`, nineteen dispatch
rungs tried and declined in **three milliseconds** of a twenty-four second
budget. The 24 rows genuinely burn the clock.

The remedies do not overlap. Raising a wall-clock budget on the 177 buys
nothing, because the clock was never binding. Raising a round count on the 24
buys nothing, because they never reach the cap. And the harm is asymmetric: the
larger population is the one that reads, from its reason string alone, as the
smaller one's problem — so the default reading sends a lane to raise a limit
that is not binding on 177 files.

This was caught only because the census already records `total_ms`. It was not
caught by reading the reasons, and the lane's own brief — written by someone who
had read a previous census — got it backwards.

## Decision

**A census that ranks a "budget exhausted" reason MUST publish, beside the
count, the distribution of budget REMAINING at give-up, and MUST classify the
reason by which budget bound it.**

1. Every ranked family carries a `kind`, assigned from what actually stopped the
   row, not from the word "budget" in its message:
   - **CLOCK** — the wall-clock deadline bound it. Remedy: more time, or a
     faster search.
   - **ROUND** — an iteration or round COUNT bound it, with clock left. Remedy:
     a different constant, and an A/B is required before touching it.
   - **SHAPE** — the route declined a fragment. Neither budget helps.
2. Publish `min / median / max` of `budget − total_ms` per family. This is the
   evidence for the `kind`, so a family mislabelled `ROUND` that actually burns
   the clock is visible as a median near zero and gets reclassified **by the
   data**, not by the message.
3. A census MUST NOT merge ROUND and CLOCK rows into one ranked line, even when
   their give-up strings both say "budget".
4. The measuring lane states the lever and its size; it **does not raise the
   cap**. A cap converts a slow `unknown` into a fast one, and only an A/B over
   the pinned winnable population can say whether removing it decides anything.

## Consequences

- One derived column per family. The input (`total_ms`) is already recorded by
  every census `--trace` run, so this needs no new instrument — the same
  property ADR-1941 has.
- The classifier is a small table of matchers and is itself a checkable
  artifact (`census-crossdiv.py`), not prose. Its `kind` assignment is falsified
  by its own `ms_left` column whenever the two disagree.
- It makes a cross-division roll-up meaningful. Five per-division censuses each
  ranking "e-matching" tell you e-matching is weak everywhere; the same five
  split by `kind` tell you 177 files stop at a round count and 47 at a clock,
  which is a different sentence with a different next action.
- It does not change ADR-1936 or ADR-1941. Those decide which rows may be
  ranked; this decides what a ranked row is allowed to claim.
- Existing censuses that ranked a "budget" reason without the remaining-budget
  distribution are **incomplete rather than wrong** — their counts stand, their
  implied remedy does not, and re-reading them is cheap because `total_ms` is in
  the committed TSVs.

## Alternatives considered

- **Fix the give-up strings so the message names the budget.** Better in the
  long run and worth doing, but it is a solver change, and a census must not
  require one before it can report — the same inversion ADR-1936 declines. A
  message is also a claim: this ADR requires the *measurement* beside it, which
  stays true even if a string is wrong. The `e-matching ... round budget` string
  here is in fact accurate; the failure was in reading a ranked list, not in the
  string.
- **Report `total_ms` per row and let the reader judge.** This is what the
  previous censuses did, and the field went unread — the same failure ADR-1941
  records for the `route-open` line, which was being printed with its own
  warning attached and was still missed. A ranking is what gets quoted, so the
  distinction has to be in the ranking.
- **Split only when the counts are large.** The threshold would itself need
  defending, and the cost of always splitting is one line per family.
- **Treat a fast decline as UNCLASSIFIED.** Wrong direction: these rows ran to
  the end of their dispatch and carry no open segment, so ADR-1941 says they are
  rankable, and they are the largest actionable finding on the board. The
  problem was never that they should not be ranked — it is what the ranking
  claimed.
