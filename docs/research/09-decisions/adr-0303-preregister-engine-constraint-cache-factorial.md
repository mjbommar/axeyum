# ADR-0303: Preregister a bounded engine-cache versus warm-solver factorial

Status: accepted
Date: 2026-07-20

Result state: implementation/runner/analyzer/registration frozen with zero
cache timing rows; prior immutable-trace opportunity analysis selects the
experiment

## Context

PLAN item 9 asks whether Axeyum's retained solver-internal state is additive
over, or largely subsumed by, the constraint caching long established in
symbolic execution by GREEN, GreenTrie, and counterexample caches. The layers
are distinct:

- Glaurung's experimental engine cache stores complete query results above the
  backend and may avoid a solver call; while
- Axeyum's warm path retains translated AIG/CNF, SAT state, learned clauses,
  lifted models, and a replay-SAT cache inside a path-owned solver.

ADR-0272 supplies a clean comparison substrate: four real drivers, five exact
ordered repetitions each, fixed source-owner topology, 64,510 checks, and
agreement across cold/warm Z3, Axeyum, and Bitwuzla cells. Its raw native
assertion packs remain available.

The disclosed read-only
[opportunity analysis](../../../bench-results/glaurung-constraint-cache-opportunity-20260720/README.md)
reconstructs those streams without implementing a cache. Exact query reuse can
answer 45.48% of one four-driver pass. Sound cached-SAT-superset and
cached-UNSAT-subset implications raise the unbounded structural ceiling to
66.37%, ranging from 46.27% on DptfDevGen to 83.82% on SurfacePen. This is
enough opportunity to warrant a timed implementation. It says nothing about
lookup cost, capacity, model replay, memory, or additivity.

## Decision

Build an opt-in, Glaurung-owned engine cache and replay the immutable ADR-0272
streams in six independently launched modes:

1. cold Axeyum, cache off;
2. warm Axeyum, cache off;
3. cold Axeyum, exact cache;
4. warm Axeyum, exact cache;
5. cold Axeyum, exact plus structural implication cache; and
6. warm Axeyum, exact plus structural implication cache.

Each of the four drivers contributes its five already accepted trace
directories to every mode, for 120 fresh replay processes. Each process starts
with an empty cache and solver state. No process pools drivers, modes, or
repetitions. The recorded cold-Z3 outcome remains the oracle; replay does not
drive live exploration or consume a cached model choice downstream.

This Axeyum-only factorial answers the stated mechanism question. Repeating the
same cache matrix around Z3 or Bitwuzla would double or triple the campaign
without changing whether Axeyum warm state remains useful after an engine
cache. The cache surface must remain backend-neutral and use only Glaurung's
`Solver`/`SolveResult` contract; a later neutral-backend repeat is permitted but
is not part of this result.

### Cache identity and sound reuse

One assertion identity is the SHA-256 of its deterministic SMT assertion bytes,
including truth polarity and symbol widths. One query identity is the sorted,
duplicate-elided set of assertion identities. Removing duplicates is sound
because conjunction is idempotent. `ExprId` and pool pointer identity never
cross a cache boundary.

The exact policy reuses only an identical query identity. The structural policy
tries exact first, then these two monotone rules:

- cached `SAT(C)` answers `SAT(Q)` only when `Q` is a subset of `C` and the
  cached model evaluates every current assertion with its expected truth value;
- cached `UNSAT(C)` answers `UNSAT(Q)` only when `C` is a subset of `Q`.

SAT models are stored by stable symbolic ID and full `u128` value. A missing
symbol, width error, evaluator failure, or false assertion is a replay failure:
the cache does not answer, the selected solver runs, and the failure counter is
retained. `Unknown`, `NoSolver`, and `Error` are never cached. An exact or
implication result opposite to the recorded Z3 outcome rejects the run.

The structural implementation uses an inverted index for SAT supersets and a
constraint trie for UNSAT subsets. A linear scan may be kept as a test oracle,
not as the measured implementation.

### Frozen capacity and eviction

Each worker owns a deterministic LRU bounded simultaneously by:

- 4,096 decided entries;
- 524,288 retained assertion-identity references;
- 262,144 retained model values; and
- 256 model values in any one entry.

Insertion evicts least-recently-used entries until every aggregate bound holds.
An individually oversized result is counted and not cached. Exact and
implication hits update recency. The accepted single-worker denominator has at
most 3,303 distinct exact queries and 2,573 distinct constraint sets per
process, so the entry bound exceeds the observed denominator without becoming
unbounded product state. Assertion/model gauges and evictions remain required
outputs; the measured result, not this estimate, determines whether another cap
binds.

### Warm interaction

On a warm-cache hit, the solver check is skipped. The retained solver is not
credited with synchronization it did not perform. Its source retain marker
stays at the last synchronized prefix; the next miss must safely catch up from
that marker or rebuild through the existing fallback. Cache lookup, SAT replay,
index maintenance, eviction, warm catch-up/rebuild, and miss solving all remain
inside the measured wrapper. This is essential: measuring lookup alone would
hide the integration cost that determines additivity.

### Frozen source and inputs

- Trace producer/base: Glaurung `2961d7c1bca03f14b77b12fb852d193413207982`,
  with accepted replay-validation descendant
  `dc06a3740d989f5a71f3a1cef4ba5111c5188f36` as the implementation base.
- ADR-0272 registration SHA-256:
  `61df225250db48caf1c9bb0dfe8810b55ffc009eea0901ec573423fb0d2612f9`.
- Opportunity result SHA-256:
  `1dc2f5459f61bef118b1b52842f7d6e9768964b815a0f821e4c412f09a5fe062`.
- Driver order and hashes remain exactly ADR-0272's DptfDevGen, vwififlt,
  IntcSST, and SurfacePen rows.
- Toolchain remains `rustc 1.97.0-nightly (f53b654a8 2026-04-30)` and all Rust
  work uses one Cargo job under the aggregate 4 GiB cgroup.

The implementation commit, clean tree, executable and dynamic-library hashes,
runner/analyzer hashes, exact environment, and report schema must be added to a
versioned registration and committed before the first timed replay. That later
freeze may correct a pre-observation implementation defect but may not change
the six modes, inputs, capacities, soundness rules, or acceptance logic here.

That freeze is now complete:

- isolated Glaurung `8b53c5038b50f3b717ad59970830b0c9bf54cdb8`
  implements the cache, warm interaction, and v2 report against tracked-clean
  Axeyum `da24b016543d1843f25019eba3675228c853f892`;
- the Axeyum-only release replay executable is
  `fbde4ee8dfa6681a6d8068adfb8aa31a03d736c2ae998b952271b5bd760a0d84`;
- Axeyum tooling commit `14834d2f3b7df1cd077988409a3216bfd8388041`
  supplies the fail-closed runner and analyzer; and
- the exact 20 inputs, executable/libraries, scripts, six modes, environment,
  4 GiB cgroup, CPU, and statistical gates are bound in the
  [zero-row registration](../../../bench-results/glaurung-engine-cache-factorial-20260720/registration.json).

Read-only preflight accepts every registered identity without invoking the
replay executable. Seventeen focused producer tests and seven tooling tests
pass. These are implementation and protocol facts, not timing observations.

### Required telemetry

Every process reports:

- recorded and actual SAT/UNSAT/unknown/error populations;
- exact-SAT, exact-UNSAT, SAT-superset, UNSAT-subset, and miss counts;
- SAT replay attempts, successes, failures, and missing-symbol failures;
- entries, assertion references, model values, per-entry oversize bypasses,
  evictions, and peak gauges;
- cache lookup, model replay, index update/eviction, backend miss, and complete
  wrapper nanoseconds;
- warm created/retained/fallback classes, synchronized misses, cache-hit
  unsynchronized returns, catch-up assertions, rebuilds, and final live-owner
  gauges; and
- process wall time and high-water RSS.

Stage times must be non-overlapping and sum to no more than wrapper time. Cache
hits have zero backend-miss time. No counter may silently classify a replay
failure as a hit.

### Analysis and acceptance

The analyzer first requires exact input/check identity across all six modes and
five repetitions per driver. It then reports these paired ratios, always as
numerator/denominator with values greater than one favoring the denominator:

- `cold-off / warm-off`;
- `cold-off / cold-exact` and `warm-off / warm-exact`;
- `cold-exact / warm-exact`;
- `cold-off / cold-structural` and `warm-off / warm-structural`;
- `cold-structural / warm-structural`; and
- `cold-exact / cold-structural` and `warm-exact / warm-structural`.

As in ADR-0272, collapse each check across repetitions by geometric mean,
report a deterministic 10,000-sample bootstrap 95% interval, nearest-rank
latencies, per-process geomean CV, and never use a ratio of sums. Report each
driver separately; do not pool a headline speed scalar.

A driver's correctness/work gate passes only if every mode and repetition:

1. consumes the exact recorded check stream and matches every recorded decided
   outcome with no unknown, error, opposite decision, or SAT replay failure;
2. leaks no cache entries across processes and ends with no live warm owner;
3. preserves exact cache classifications from the committed opportunity result
   when the registered bounds do not evict or bypass an entry; otherwise reports
   the bounded delta explicitly; and
4. completes all telemetry invariants.

A timing contrast is conclusive only when both modes pass that gate and its
per-process geomean CV is at most 3%. Warm state is **additive under a cache
policy** only when `cold-cache / warm-cache` has a bootstrap interval wholly
above one. It is **not shown additive** when that interval includes one, and is
negative when wholly below one. Separately report whether cache-on improves the
cold and warm modes. These labels characterize the interaction; they do not
authorize a general speed headline.

## Zero-row boundary

The cache implementation, registration, runner, and analyzer now exist and are
committed, so the preregistered experiment is executable. No real trace has yet
been replayed through any cache mode: timing rows, ratios, confidence intervals,
and driver conclusions remain empty. The only observed workload result remains
the disclosed read-only structural opportunity artifact. Unit fixtures exercise
semantics, counters, and fail-closed analysis without becoming benchmark rows.

## Alternatives

- Compare only warm-off against cold-cache: rejected because it cannot reveal
  whether cache and warm state combine better than either mechanism alone.
- Run cache-on during live exploration: rejected because a cached SAT model can
  change concretization and the future query stream.
- Count only exact hashes: rejected because it ignores the monotone reuse that
  distinguishes GREEN/GreenTrie-style caching from memoization.
- Reuse SAT without replay: rejected because returned models are consumed by
  symbolic execution and must satisfy the current original expressions.
- Use an unlimited cache: rejected because it makes the memory/performance point
  non-product-like and hides eviction behavior.
- Time all modes in one process: rejected because cache and warm high-water RSS
  would contaminate later modes.

## Consequences

PLAN item 9 now has an executable scientific boundary. The implementation is a
Glaurung experiment, not an Axeyum core feature, unless measured additivity and
another ADR justify promotion. A negative result is valuable: if cold plus a
bounded engine cache matches or beats warm plus the same cache, the paper must
not frame solver-internal reuse as an independent SE advantage. A positive
result supports only the measured drivers and policies.
