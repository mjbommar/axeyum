# ADR-0223: Four-driver neutral cvc5 breadth

Status: accepted
Date: 2026-07-17

## Context

ADR-0222 adds exact cvc5 verdict parity and a stable cold-reset external-SMT
point for Dptf, but one losing Axeyum/Z3 driver cannot establish neutral breadth
or show whether the same regime ordering survives a third solver. ADR-0217's
accepted vwififlt, IntcSST, and SurfacePen traces contain all hash-bound query
scripts and exact occurrence order needed by the same runner.

## Decision

Replay the first accepted trace for each remaining driver with the exact
ADR-0222 contract: cvc5 1.3.4, one process per repetition, full reset after
every query, model output enabled, 250 ms per-check timeout, one unreported
warm-up, N=5 measured runs pinned to CPU 3, and fail-closed trace/query/verdict/
model-output validation.

Accept neutral verdict and external-SMT breadth only if all 9,526 four-driver
checks decide identically, complete output is byte-stable per driver, and every
timing series has at most 3% sample CV. Continue to prohibit division of these
aggregate external-protocol times into the in-process paired four-cell ratios.

## Evidence

All four drivers pass:

| Driver | Checks | SAT / UNSAT | Median batch | Sample CV |
|---|---:|---:|---:|---:|
| DptfDevGen | 561 | 317 / 244 | 2.593056 s | 0.4222% |
| vwififlt | 4,742 | 2,932 / 1,810 | 64.637115 s | 0.2162% |
| IntcSST | 1,672 | 1,270 / 402 | 6.217003 s | 0.1639% |
| SurfacePen | 2,551 | 2,282 / 269 | 11.179779 s | 0.3899% |

The combined result is 6,801 SAT / 2,725 UNSAT / 0 Unknown, with all 6,162
requested SAT value responses and only the 2,608 expected post-UNSAT
diagnostics. Complete stdout is byte-identical across repetitions within every
driver. Exact reports and hashes are committed under
[`bench-results/glaurung-small-drivers-cvc5-smt-20260717/`](../../../bench-results/glaurung-small-drivers-cvc5-smt-20260717/README.md)
and the ADR-0222 Dptf artifact.

cvc5's workload ordering does not mirror the Axeyum/Z3 warm map: vwififlt is
the most expensive cvc5 stream per check despite warm Axeyum/Z3 parity, while
IntcSST is the least expensive neutral stream per check and favors warm Axeyum.
This is further evidence against formula size or FFI cost as a universal causal
explanation.

## Alternatives

- Stop after Dptf: rejected because the consolidated review explicitly asks for
  the small-driver performance regime and a neutral comparator.
- Normalize aggregate seconds into a solver-speed headline: rejected because
  check populations, model work, and integration boundaries differ.
- Preserve cvc5 state across checks: deferred until a source-lineage-compatible
  cvc5 API path exists; full reset is the declared cold control.

## Consequences

Z3 is no longer the sole oracle on any check in the accepted four-driver map,
and every driver now has a stable neutral cold-reset performance point. The
paper may report this as correctness breadth and an external integration
control, not as topology-equivalent warm performance.

The remaining neutral performance blocker is a cvc5/Bitwuzla in-process or
source-lineage-equivalent warm cell. Correctness work now returns to the
standing well-typed multi-oracle fuzzer, while timeout-sensitive and
authoritative-finding gates remain open.
