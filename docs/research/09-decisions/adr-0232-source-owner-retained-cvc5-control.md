# ADR-0232: Source-owner-retained cvc5 control

Status: accepted
Date: 2026-07-18

## Context

ADR-0222/0223 establish neutral cvc5 correctness and stable cold-reset external
SMT throughput on all 9,526 checks in the accepted four-driver Glaurung map.
They deliberately reset declarations, assertions, and learned state after each
standalone query. The reviewer checklist still requires a neutral warm or
topology-equivalent point before attributing the remaining word-level
representation/integration mechanism.

The accepted traces bind every check to exact standalone bytes and also record
the production warm owner, logical retain request, persistent/temporary
partition, source-prefix identity, and synchronization result. The native Z3
and Axeyum cells do not blindly trust the requested depth: both derive the
effective retain depth from the common persistent-prefix identity, then use the
temporary suffix as assumptions.

## Decision

Extend the existing cvc5 runner with an explicit `retained-lcp` policy while
leaving `cold-reset` as the compatible default. Require exact QF_BV command
shape, one consistent declaration per symbol, all prior trace/hash/verdict
checks, synchronized source warm metadata, and a valid persistent/temporary
partition.

For each contiguous source owner, emit one cvc5 solver session with one
declaration prelude. Transition persistent assertions by exact content-byte
longest common prefix using one push scope per assertion. Submit the recorded
temporary suffix with `check-sat-assuming`. At a source-owner change, issue a
full reset and a new prelude; reject a trace if that owner later reappears,
because the external batch could no longer reproduce its retained state.

Use the same official cvc5 1.3.4 libc++ static binary, 250 ms per-check bound,
model output, CPU 3, one unreported warm-up, and N=5 measured repetitions as
the cold-reset controls. Require all verdicts, response cardinalities, and
within-driver stdout bytes to be stable.

Classify this as **source-owner/topology-equivalent retained external SMT**.
It matches the solver-state ownership, prefix, scope, and assumption boundary;
it does not match the native in-process API/FFI boundary. Compare retained and
cold-reset cvc5 totals only as a within-protocol state-reuse diagnostic, never
as an Axeyum/Z3 solver ratio.

## Evidence

All five repetitions decide all 9,526 checks exactly: 6,801 SAT, 2,725 UNSAT,
zero Unknown, all 6,162 requested SAT value responses, and only the 2,608
expected post-UNSAT diagnostics. Complete stdout is byte-stable per driver.

| Driver | Owners | Retained median | Sample CV | Cold-reset / retained |
|---|---:|---:|---:|---:|
| DptfDevGen | 7 | 0.158184 s | 1.6132% | 16.3927x |
| vwififlt | 14 | 1.133353 s | 0.2764% | 57.0317x |
| IntcSST | 24 | 0.295296 s | 0.3739% | 21.0535x |
| SurfacePen | 43 | 0.283179 s | 0.4251% | 39.4795x |

The effective prefix telemetry is nontrivial rather than an alias for the
explorer request. Across the four streams, sibling identity makes some checks
retain slightly more or rewind slightly farther; the maximum difference is
four assertions. The runner derives the effective prefix independently from
the exact captured persistent bytes. It emits 7/14/24/43 owner sessions,
7,075 persistent pushes, 4,923 pops, and 2,078 temporary-assumption
occurrences.

The final cold-reset regression reproduces ADR-0222's exact Dptf batch SHA-256
`3955ce0ba0d6ebd76e8299babcf2d23e0d36789b6a9bfb1672cfcf2e59ef3ead`,
so the additive mode does not redefine the accepted cold artifact. Exact
reports are committed under
[`bench-results/glaurung-four-driver-cvc5-retained-20260718/`](../../../bench-results/glaurung-four-driver-cvc5-retained-20260718/README.md).

## Alternatives

- Keep full reset: rejected because it cannot answer the warm word-level
  mechanism question.
- Retain one solver across all checks: rejected because it leaks state across
  7--43 independent source owners.
- Treat the explorer's requested depth as the actual prefix: rejected because
  both native engines recompute identity LCP, and sibling rewind makes the two
  values observably differ.
- Push temporary assertions into persistent scopes: rejected because the
  source cells use assumptions and deliberately leave persistent state
  unchanged.
- Call the result in-process: rejected because cvc5 still consumes an external
  textual stream and serializes models.

## Consequences

The accepted four-driver map now has both a neutral cold-reset control and a
neutral source-owner-retained control. The large within-cvc5 reduction proves
that representation/session retention is a first-order mechanism, while the
external protocol boundary prevents a direct rank ordering against the paired
native cells. The paper can close the neutral-warm reviewer item without
reviving a blanket speed headline.

The next publication work is timeout-sensitive neutral and authoritative
coverage, deadline-aware real-query term-to-CNF faithfulness, independent fuzz
seeds/edge frequencies plus another neutral implementation, and
whole-certificate process isolation.
