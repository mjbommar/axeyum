# The 67.6% was 98.8% an artifact, and the quantifier blocker is architectural

Recorded 2026-09-09. A lane built the instance-selection filter I briefed,
measured six arms, and decided **0 of 32 files** in every one. The negative is
worth more than the build would have been.

## The number I built a brief on was measuring itself

The UF attribution lane reported **67.6% of admitted instances are already TRUE
under the current congruence** — the headline that made "stop admitting TRUE
ones" look like the obvious first move.

The census read retained instances against the **final** congruence, and the
matcher's e-graph merges every top-level positive equality in the ground set. So
**an instance that IS such an equality reads TRUE by its own admission.**

Split: `self_merged` **134,856** / `by_others` **1,639**. The actionable
population is **0.83%, not 67.6%.** Eviction confirms it from the other side —
846,617 examined, 1,368 evicted, 0.16%.

## And the filter I briefed was already shipped

`lazy_clause_batches` already evaluates every candidate against the round's
congruence and drops `ClauseValue::True` into `redundant`, admitting it to no
pool, re-classified fresh each round. **Nothing counted it.** It now does:
**528,561 candidates declined against 198,231 admitted — 2.7 rejected per
admission.**

So target 1 was "build the thing that is already there, against a number that
was measuring an artifact."

## Six arms, zero verdicts

| arm | criterion | scored | declined | evicted | reordered | decided |
|---|---|---:|---:|---:|---:|---:|
| shipped | — | 0 | 0 | 0 | 0 | **0/32** |
| narrow | equality | 290,116 | 8,259 | 0 | 2,534 | **0/32** |
| evict | equality | 294,293 | 0 | 1,368 | 2,345 | **0/32** |
| full | equality | 294,645 | 8,259 | 1,368 | 2,345 | **0/32** |
| entail | bool units | 259,562 | 0 | 0 | 11,877 | **0/32** |
| entail-narrow | bool units | 259,562 | 5,585 | 0 | 11,877 | **0/32** |

The funnel proves the route ran — `scored` and `reordered` are nonzero where
shipped's are zero, on the same files. This is the counter-gated discipline
working: an agreement tally would have read identically across all six.

## Why it cannot work here, which is the actual finding

**1. There is no far-from-conflict traffic to filter.** The residual band on
every reading of every file is **1 to 4 open literals**. Nothing is more than
four facts from conflicting, and `clause_false = 0` everywhere. The pool is
*adjacent* to a refutation and never arrives at one. A relevance filter removes
distant candidates; there are none.

**2. The criterion is blind on 84% of what it ranks.** 245,828 of 287,077
scored candidates carry a literal the equality classifier cannot value —
deferred by **default**, not by judgement. Ranking their widths ranks noise.

## The `ieval` comparison, and why earliness was not the axis

I relayed cvc5's `ieval` — evaluate under the **partial** substitution, abandon
the match before the tuple completes — as the sharper version of this build.

The lane made the criterion a policy parameter and measured the axis. Widening
equality-only to Boolean-units moved blindness **85.6% → 84.1%** and reordered
4.7x more rounds. Still 0/32.

**That 1.5 points is the finding. These files do not assert their predicates as
ground units.** cvc5 can value a predicate atom because a CDCL(T) search has
**decided** that literal into the equality engine — the value comes from the
current assignment. Our loop instantiates **outside** any search: it accumulates
a ground set and re-checks from scratch, so when it judges a candidate there is
no assignment to judge against.

**So the blocker is the criterion, not the earliness.** Building the incremental
version on this evaluator prunes early against an oracle that cannot speak:
post-hoc gains 0, incremental-same-criterion gains 0 faster.

## What this redirects to

- **Target 4 (new, and the real one):** the loop already builds an
  `OnlineQuantifierClauseSession` and **discards its assignment**. Judging
  candidates against a live assignment is the architecture `ieval` depends on.
- **Target 2 (restart with a pruned pool) needs re-scoping before it is built** —
  "pruned" has no definition this layer can compute.
- **Target 3 (trigger selection) is the only original target the measurements
  still support.** 19 of 32 files carry no `:pattern` at all.

## The rule

**A headline percentage can be measuring its own construction.** The 67.6%
survived a lane report, my brief, and a summary to the user before anyone asked
what the denominator contained. The question that broke it — "could an instance
be true *because* we admitted it?" — cost one query and would have redirected a
day.
