# ADR-0172: Native lineage phase attribution

Status: accepted
Date: 2026-07-15

## Context

ADR-0171 accepted explicit path-owned warm reuse as the fastest bounded native
Glaurung policy, at 0.746x the same-stream Z3 time in repeated unprofiled runs.
It did not explain the remaining 5.537-second Axeyum median. Earlier one-shot
attribution and standalone corpus measurements could not be substituted: live
lineage changes arena lifetime, root traffic, retained AIG/CNF state, learned
SAT state, and model replay.

Axeyum already exposes opt-in cumulative `IncrementalBvStats` and
`delta_since`; ordinary constructors deliberately do not pay phase-clock or
gate-scan overhead. The downstream adapter needed to preserve that boundary
while binding every delta to the exact client query and explicit path owner.
Glaurung remains an external, untrusted workload and does not define Axeyum's
formal solver architecture.

## Decision

Accept an opt-in exact-query warm profile and its first three-driver
attribution with these consequences:

1. keep the ordinary path on `IncrementalBvSolver::with_config`; select
   `with_config_and_profiling` only when the existing profile-directory opt-in
   is present;
2. emit one `glaurung-axeyum-warm-profile-v1` JSONL record per warm check,
   carrying the exact SMT-LIB SHA-256, path owner/creation, prefix/add/pop root
   traffic, session creation, incremental phase deltas, structural deltas,
   outcome, and explicit unattributed time;
3. validate streams fail-closed: exact schema, monotone process sequence,
   first-occurrence path creation, nonnegative structure, added-root/encoding
   agreement, exact phase-sum reconciliation, expected record count, and 100%
   decided outcomes;
4. never use profiled wall time as a production performance claim—query
   rendering and JSON output are intentionally excluded from internal totals
   but included by the client timer, while phase clocks themselves also cost;
5. prioritize measured warm CNF gate/root attribution next, then AIG
   construction per node; keep SAT tuning third and do not reopen GQ4; and
6. retain the pre-parsed cold, native cold, external replay, unprofiled native
   lineage, and profiled lineage bars as distinct measurements.

## Evidence

Glaurung `13f4bbe` adds the schema using Axeyum's existing incremental stats.
The profile writer shares one monotone process-local sequence across cold and
warm records. Query rendering/hashing occurs before `total_nanos`; JSON output
occurs after it. Operational errors still produce incomplete/error records and
fail the validator rather than disappearing from the stream.

Axeyum's `summarize-glaurung-warm-profile.py` independently validates and
summarizes the artifact. Its focused tests cover duplicate hashes, path
creation order, structural totals, phase shares, and exact rejection of a bad
phase sum.

One clean release process per driver uses Z3-authoritative shadow execution,
explicit lineage reuse, a 30-second exploration deadline, a 20,000-check
budget, and a 60-second solve bound. All processes finish without deadline
hits, cap fallbacks, warm resets, disagreements, or unknown splits.

| Driver | Records | Unique queries | Paths | Internal total | CNF | Bit blast | SAT |
|---|---:|---:|---:|---:|---:|---:|---:|
| `win10-vwififlt` | 4,753 | 3,476 | 1,487 | 6.264 s | 44.40% | 23.79% | 16.29% |
| `sqfs-intel-DptfDevGen` | 561 | 377 | 131 | 0.315 s | 37.05% | 12.66% | 34.51% |
| `windows-update-intel-audio-IntcSST` | 1,672 | 1,272 | 485 | 0.526 s | 40.49% | 17.92% | 21.06% |
| weighted bounded sum | 6,986 | 5,102 | 2,103 | 7.106 s | **43.78%** | **22.86%** | **17.45%** |

The remaining weighted shares are replay 5.79%, translation 3.74%, model lift
3.41%, unattributed adapter work 2.70%, session creation 0.21%, and Glaurung
model extraction 0.04%; configured word rewriting is zero. The stream adds
88,476 roots, 8,758,247 AIG nodes, 8,848,809 CNF variables, and 11,734,335 CNF
clauses while retaining 206,617 assertion-prefix occurrences.

The three client timers report 9.441 seconds of profiled Axeyum time. The
validated internal records total 7.106 seconds because exact query rendering,
hashing, locking, serialization, and file output are deliberately outside
`total_nanos`. Both exceed ADR-0171's 5.537-second repeated unprofiled median;
therefore neither profiled number replaces the production ratio.

## Alternatives

Always enabling phase clocks was rejected because profiling changes the cost
being measured and the ordinary solver API promises no diagnostic overhead.
Aggregating only process totals was rejected because it cannot reconcile exact
query identity, duplicates, path creation, or missing/error checks. Reusing the
one-shot profile schema was rejected because warm deltas, retained gauges, and
path ownership have different invariants. Treating translation or session
construction as the primary remaining gap was rejected by their 3.74% and
0.21% weighted shares. Leading with SAT tuning was rejected because CNF plus
bit-blast owns 66.65% of the measured internal total, versus SAT's 17.45%.

## Consequences

GQ1 native-lineage phase partitioning is complete for the bounded three-driver
tier. GQ5 is again the leading implementation lane: extend the profile with
causal incremental CNF gate/root-family deltas, identify the 11.73-million-
clause dominant patterns, and accept changes only on lower unprofiled native
time with identical decisions, replay, scopes, and resource identity. AIG
construction per node is second. GQ6 SAT tuning remains material but follows
those measured construction costs. GQ7 still needs memory-limit calibration;
GQ8 and GQ9 remain behind replay-safe cache and non-regressing admission gates.
