# Glaurung constraint-cache opportunity on the accepted six-cell traces

Date: 2026-07-20

This is a read-only structural analysis of ADR-0272's accepted four-driver,
five-repetition ordered traces. It asks whether enough real query reuse exists
to justify PLAN item 9's GREEN-style engine-cache experiment before building
that cache.

## Result

Yes: the opportunity is material, but strongly workload-dependent.

| Driver | Checks/process | Exact hits | Implication-only hits | Structural hits | Structural rate |
|---|---:|---:|---:|---:|---:|
| DptfDevGen | 603 | 240 | 39 | 279 | 46.27% |
| vwififlt | 5,182 | 1,879 | 1,122 | 3,001 | 57.91% |
| IntcSST | 2,309 | 1,095 | 158 | 1,253 | 54.27% |
| SurfacePen | 4,808 | 2,654 | 1,376 | 4,030 | 83.82% |
| **One four-driver pass** | **12,902** | **5,868** | **2,695** | **8,563** | **66.37%** |

The exact-query ceiling is 45.48%. Sound structural implication adds 20.89
percentage points: 1,955 cached-SAT-superset opportunities and 740
cached-UNSAT-subset opportunities per pass. The remaining 4,339 checks require
a solver under this abstraction.

Every driver's five repetitions have byte-identical logical query sequences and
identical cache classifications. The committed [result](opportunity.json)
therefore contains 64,510 process-local check occurrences, but the table reports
one 12,902-check pass rather than treating repeated processes as new formulas.

## Method

[`analyze-glaurung-constraint-cache-opportunity.py`](../../scripts/analyze-glaurung-constraint-cache-opportunity.py)
reconstructs each path's active assertion stack from the immutable ordered event
stream and validates event/index hashes, scope operations, check counts, the
accepted report set, and the ADR-0272 driver denominator. Each process starts
with an empty cache.

The classifications are logical and sound:

1. an exact content-hash hit reuses the prior decided result;
2. a prior SAT conjunction that is a superset of the new constraint set proves
   the weaker query SAT with its retained model; and
3. a prior UNSAT conjunction that is a subset of the new constraint set proves
   the stronger query UNSAT.

The analyzer fails if either implication contradicts the recorded oracle
outcome. Five focused tests cover exact versus implication accounting, both
wrong-implication directions, exact-verdict conflict, and forked-scope
isolation.

Inputs are the committed ADR-0272 registration and reports:

- registration SHA-256
  `61df225250db48caf1c9bb0dfe8810b55ffc009eea0901ec573423fb0d2612f9`;
- Dptf report SHA-256
  `f89f28b935b4e55840c3240e6ef0db78ae5c9db861eefa1f542a3b8ffa62aacc`;
- vwififlt report SHA-256
  `f774645080431a60d33512e14e1ee61ab88ad9ca3edeb1caadecb7296634376e`;
- IntcSST report SHA-256
  `ffac9498972876b26e8b376903646c563f5166829672071bd663a7f4525a00fa`;
- SurfacePen report SHA-256
  `1e89b36af22a6d42b7c659909b8e7942c87af034bcf7261ba0c064395356dc67`;
  and
- opportunity result SHA-256
  `1dc2f5459f61bef118b1b52842f7d6e9768964b815a0f821e4c412f09a5fe062`.

## Claim boundary and next experiment

This is an **unbounded structural opportunity ceiling**, not a cache result. It
assigns zero cost to lookup, model storage, model replay, eviction, and
concurrency. It does not implement GREEN/GreenTrie, time a cached solver, or
show that engine-level caching subsumes—or is additive with—Axeyum's retained
solver state. The accepted traces also had Axeyum's separate internal replay-SAT
cache enabled; this analysis does not relabel that solver-internal mechanism as
an engine cache.

The next experiment should therefore be a fixed-query-stream factorial, not a
two-cell headline: `{cold, warm} x {engine cache off, engine cache on}` for each
in-process backend. Cache-on must report exact, SAT-superset, UNSAT-subset,
miss, replay-failure, eviction, entry/model-value, and lookup-time counters.
Cache hits must replay SAT models against the current expression pool; any
failure falls through to the selected solver and is retained as a failure
counter. A bounded capacity and all timing/variance gates must be frozen before
the first measured row.
