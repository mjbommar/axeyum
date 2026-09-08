# Binary clauses were not the cost, and I ranked the work on an inference

Measured 2026-09-08. Recorded because the reasoning error is more reusable than
the result.

## What I briefed, and on what basis

The CDCL survey said binary clauses dominate watch traffic on bit-blasted
formulas and that keeping them inline in the watch list is what makes a large
clause database affordable. **That claim was tagged `[I]` — the lane's own
inference, not a measurement.** I promoted it to the ranked justification for a
lane, describing it as "the highest-leverage item left".

The tagging convention worked exactly as designed. I did not read the tag.

## What the measurement says

Binary share of watch visits: **6.8-14.1%** on bit-blasted fixtures, **1.1-3.4%**
on hard combinatorial instances.

The mechanism, once measured, is obvious in hindsight: a binary clause's watches
never relocate and are visited only when one of its two literals is falsified. A
long learned clause's watch migrates and is revisited — and a tier database is
full of long learned clauses. **The very policy that made the database large is
what makes binaries a small share of it.**

## The structural point that kills the direction

The blocker on shipping the tier policy is that a 2.2x larger database costs
**28% more watch VISITS**. Inlining binaries does not reduce the visit count at
all — it reduces the arena work *inside* a visit. It is the wrong quantity.

R9 is real and correct (1-4% of modelled ticks, and **trajectory-identical**:
conflicts, decisions, propagations and watch visits match to the digit, only
`clause_visits` falls). It is simply not the lever for this blocker. The levers
are a smaller database, better blocking literals, or a genuinely narrower watch
entry.

## Two further measurements worth keeping

- **The instrumentation cost more than the change saved.** The hot-path counter
  added ~3% against a ~1-4% tick saving. Now branchless and opt-in. A throughput
  change measured with a clock on a shared box is not measurable at this size:
  two min-of-5 interleaved sweeps disagreed (1.053 vs 1.036) while the *base*
  timings moved 2x between them. The deterministic tick total is the number to
  quote.
- **R10's in-place reduce sweep was measured and rejected.** The whole sweep is
  under 1% of propagation traffic, and in-place needed MORE conflicts on seven of
  eight instances (+1.3% to +6.3%). There is a mechanism: a rebuild leaves lists
  in clause-id order, putting short input clauses ahead of long learned ones and
  refreshing each blocker. Rebuild stays the default; the scan half
  (`first_reducible`) is trajectory-preserving and stays on.

## The rule

**Read the provenance tag before ranking work on a claim.** `[C]` read from
source, `[P]` from a paper with numbers, `[I]` inference — the surveys carry
these on every line precisely so a reader can tell. An inference is a hypothesis
to test cheaply first, not a premise to build a lane on.

The cheap test here existed and was one measurement: count binary versus long
watch visits on a bit-blasted fixture. It would have cost an hour and redirected
the lane.
