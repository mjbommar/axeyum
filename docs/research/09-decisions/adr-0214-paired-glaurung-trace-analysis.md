# ADR-0214: Paired Glaurung trace analysis

Status: accepted
Date: 2026-07-17

## Context

ADR-0213 requires paired per-query statistics, decided-population separation,
and explicit warm/fallback attribution before a Glaurung performance result can
be a paper claim. Historical ordered trace v1 artifacts record independent Z3
and Axeyum timings, but only the Z3-authoritative outcome and an aggregate warm
synchronization flag. They cannot identify `{both-decided, z3-only,
axeyum-only, neither}` per occurrence or assign an individual latency to an
assertion-cap/path-cap fallback.

The first publication-methodology increment therefore needs a producer schema
that captures facts at solve time and a consumer that refuses to reconstruct
missing facts from aggregate footers.

## Decision

Accept Glaurung's additive
`glaurung-ordered-check-measurement-v1` trace extension and Axeyum's
`scripts/analyze-glaurung-paired-traces.py` as the fixed-work paired-analysis
mechanism.

Every newly marked check binds:

- the independently timed Z3 and Axeyum result classes;
- the independent positive timing for each backend; and
- one closed Axeyum execution class: cold one-shot, snapshot warm, newly
  created warm, retained warm, timeout cold retry, or a named missing-path,
  auto-probe, path-cap, assertion-cap, or invalid-delta class.

The producer validator requires timing/outcome/execution presence to agree and
rejects unknown execution classes. Historical trace v1 remains valid when the
extension marker is absent, but it is ineligible for this analysis.

The analyzer requires at least five fresh-process traces with identical driver,
source/configuration/environment, ordered check identity, query hash, and
execution-class membership. It rejects nonpositive timings, operational
results, decided disagreements, event/hash drift, and fixed-work drift. It
reports all four decided/nondecided buckets per repetition. The primary
population is the intersection of occurrences decided by both backends in
every repetition.

For each primary occurrence, compute the geometric mean of its paired
`z3_nanos / axeyum_nanos` ratios across repetitions. The headline scalar is the
geometric mean across those occurrence values with a deterministic bootstrap
95% confidence interval. Report per-backend p50/p90/p95/p99 over each
occurrence's median repeated latency, per-run geomean CV, execution-class
partitions, pure-warm and retained-warm execution rates, and optional CSV/PNG
CDFs. The report retains the normalized source/configuration/environment
identity that was compared across repetitions. Do not emit a ratio of sums.

The first real-driver mechanism exercise uses DptfDevGen and predeclares
fresh-process cells at `{1, 5, 60}` seconds, with five repetitions in each
cell. Each cell is analyzed independently under the same fixed-work and
fail-closed rules; the sweep is not pooled into a larger sample.

## Evidence

Glaurung `eb624c0` implements the marked trace fields, exact execution
classification, validator checks, and ADR-022. Five focused ordered-trace tests
cover SAT/UNSAT publication, native topology, wide truthiness, shared DAGs, and
a hash-repaired invalid execution-class mutation. The complete historical
85,449-event / 17,400-check dxgkrnl trace still passes the updated validator,
proving the additive compatibility boundary. A direct-delta test distinguishes
newly created, retained, and invalid sessions.

Seven Axeyum analyzer tests cover an exact 2x per-occurrence geomean and degenerate
bootstrap interval, the four outcome buckets, minimum repetition count,
fixed-work/query drift, execution-population drift, operational errors, and
CSV/PNG CDF production. Query-index and query-byte hashes are independently
verified, including a corrupted-query rejection test. The implementation uses
only the Python standard library except for optional plot rendering through
matplotlib.

The first clean real-driver exercise uses Glaurung `eb624c0`, Axeyum solver
`ee1bc306`, and DptfDevGen SHA-256
`074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b`.
Each predeclared `{1, 5, 60}`-second cell has five sequential fresh-process
repetitions and the same 561 checks. Every repetition buckets all 561 as
both-decided, with zero disagreement, nondecision, operational error, replay
failure, or fallback; execution membership is always 7 `warm-created` and 554
`warm-retained` checks.

| Timeout | Paired geomean Z3/Axeyum | Bootstrap 95% CI | Per-run CV | Z3 p50 | Axeyum p50 |
|---:|---:|---:|---:|---:|---:|
| 1 s | 5.9771x | [5.3341, 6.7167] | 1.8037% | 596.755 us | 95.393 us |
| 5 s | 6.0953x | [5.4429, 6.8513] | 0.7836% | 603.515 us | 95.194 us |
| 60 s | 6.0128x | [5.3662, 6.7548] | 1.5977% | 591.492 us | 97.234 us |

The exact reports and CDFs are committed under
[`bench-results/glaurung-paired-dptf-20260717/`](../../../bench-results/glaurung-paired-dptf-20260717/README.md).
The access-controlled raw traces reanalyze to byte-identical JSON. This is
mechanism evidence and a no-timeout control, not a fair solver headline: the
baseline is still cold one-shot Z3 over FFI versus warm Axeyum, the easy driver
never crosses a timeout boundary, and one workload does not establish
generality.

## Alternatives

- Infer backend outcomes from aggregate unknown counters: rejected because an
  aggregate cannot identify which latency or query was nondecided.
- Infer fallbacks from end-of-run cap totals: rejected for the same reason.
- Treat all trace v1 artifacts as if they had the new fields: rejected because
  absent evidence is not a negative observation.
- Pool every repetition/check as independent bootstrap samples: rejected
  because repetitions of one occurrence are correlated. They are collapsed to
  one paired occurrence value before resampling.
- Use the ratio of total times after reporting decided rates: rejected because
  a few hard queries dominate it and it still mixes populations.

## Consequences

The mechanism half of ADR-0213 item 1 and its first clean real-driver exercise
are complete. A timeout-sensitive driver and additional claimed workloads must
still be regenerated through the marked schema. ADR-0215 now supplies the warm
Z3 control; a neutral solver, authoritative finding parity/canonical model
selection, and multi-oracle assurance remain later gates.

The prerequisite for resuming GQ5 is satisfied: at least one real marked trace
set exercised the analyzer and failed none of its population gates. Existing
engineering-local ratios retain their original product-decision role but remain
non-publication evidence. The next publication-critical implementation was the
topology-equivalent warm Z3 cell, not promotion of the Dptf scalar; ADR-0215
completes that control and confirms why the old scalar could not be promoted.
