# ADR-0174: Bounded internal positive-AND flattening

Status: deferred
Date: 2026-07-15

## Context

ADR-0173 finds that definitions own 71.75% of the bounded native-lineage CNF
and that local AND-tree shapes own 53.89% of emitted implication halves. Direct
positive-root fusion is already saturated, so it selects one narrower
experiment: replace a positive internal implication `v -> tree` by direct
clauses from `v` to the conjunction leaves while preserving ordinary helper
definitions for later reuse.

This transformation is logically exact for the implication at the time it is
installed. It does not, however, prove that bypassed helpers remain unused in a
growing AIG. A retained path can later reference the same helper under another
root, selector, or polarity and force its ordinary definition into the
monotone SAT database. The acceptance boundary therefore requires cumulative
clause reduction and lower unprofiled native time, not just a local clause
calculation.

## Decision

Keep the implementation explicit and off by default; defer it after the first
real-client gate.

The candidate:

1. scans only when structural profiling or
   `SolverConfig::incremental_positive_and_flattening` is enabled;
2. descends through positive AND edges while leaving XOR/XNOR and not-ITE
   families opaque, rejects any already-emitted positive helper, and falls back
   after a deterministic 64-node bound;
3. applies only when direct leaf clauses are fewer than the primitive clauses
   required by all currently fresh positive halves;
4. marks only the requested half as emitted, leaving every bypassed helper
   available for ordinary future definition;
5. reconstructs all AIG node values from input bits and preserves the existing
   original-term replay path; and
6. reports opportunities, opportunity nodes, applications, and **immediate
   primitive clauses avoided**. The last name is deliberate: it is not a claim
   about the final retained CNF.

Glaurung `74c7759` exposes the candidate only through
`GLAURUNG_AXEYUM_INTERNAL_AND_FLATTENING=1` and advances the opt-in warm profile
to v3. Axeyum's summarizer accepts historical v1/v2, validates the exact v3
field set and opportunity/application invariants, and aggregates only a
homogeneous gate schema.

Do not enable the candidate by default and do not tune the current freshness or
node-count thresholds. A successor must predict retained future reuse, replace
earlier direct clauses when helpers become shared, or otherwise prove a
cumulative rather than immediate reduction.

## Evidence

Focused CNF tests cover exact clause reduction on the intended shape, all 32
input assignments, causal opportunity/application counters, and later
opposite-polarity reuse through selector scopes. A public solver test proves
that the off-by-default configuration reaches the incremental encoder. All 297
`axeyum-cnf` tests, four public incremental-attribution tests, and strict
all-target/all-feature Clippy for `axeyum-cnf` and `axeyum-solver` pass under
the 4 GiB wrapper.

The bounded real gate uses the 561-check Dptf path-owned stream because a
necessary structural failure there is sufficient to reject a full three-driver
run. Both control and candidate decide and agree 561/561 with Z3; every one of
131 paths closes; exact/prefix/add/pop traffic is identical; and fallbacks,
resets, deadline hits, disagreements, and unknown splits remain zero.

| Profiled Dptf metric | Control | Candidate | Change |
|---|---:|---:|---:|
| observed opportunities | 3,642 | 2,597 | state-dependent |
| opportunity nodes | 106,850 | 86,141 | state-dependent |
| applied halves | 0 | 2,597 | +2,597 |
| immediate primitive clauses avoided | 0 | 83,544 | +83,544 |
| cumulative added clauses | 429,432 | 505,090 | **+17.62%** |
| profiled CNF time | 119.805 ms | 129.616 ms | **+8.19%** |
| profiled internal total | 318.639 ms | 322.928 ms | +1.35% |

The control and candidate opportunity counts differ because applying one
flattening changes which later halves are still fresh. The decisive result is
the final retained database: later helper reuse more than gives back every
immediate reduction and adds 75,658 clauses overall.

Three alternating unprofiled control/candidate runs preserve the same 561
checks and root traffic. Axeyum control times are 239.0, 240.0, and 239.6 ms
(239.5 ms mean); candidate times are 248.0, 246.5, and 250.3 ms (248.3 ms
mean), a **3.65% regression**. Z3 timing drifts in the opposite direction, so
the raw Axeyum regression is the conservative comparison. The structural gate
already fails, and the real-client timing agrees; a wider run cannot authorize
the policy.

## Alternatives

Treating 83,544 locally avoided clauses as savings was rejected because the
monotone final database grows by 75,658 clauses. Enabling only below a smaller
node cap was rejected because the failure is future reuse, not traversal size.
Using current AIG fanout was rejected as an unproven fix: later assertions can
increase fanout after clauses are irreversible. Removing bypassed helper
variables or definitions was rejected because later polarity/scope reuse and
model lifting require their semantics. Running the full three-driver gate was
rejected after both necessary Dptf acceptance conditions failed.

## Consequences

ADR-0173's bounded CNF candidate is closed as a deferral. The implementation
and v3 counters remain explicit for reproducibility and future cumulative-use
research, but production behavior is unchanged. The profile also teaches that
local gate shape and immediate clause arithmetic are insufficient cost models
for a monotone incremental encoder.

Move the leading GQ5 task to AIG construction cost per added node: separate
structural-hash lookup, successful reuse, node allocation/copy, and lowering
bookkeeping on the same native lineage stream. Return to internal CNF fusion
only with retained-future-use evidence or a replacement mechanism. SAT remains
third, GQ4 stays off, and GQ7 memory admission/GQ10 widening remain open.
