# ADR-0222: Neutral cvc5 ordered SMT baseline

Status: accepted
Date: 2026-07-17

## Context

ADR-0221 shows that persistent Z3 Boolean does not beat persistent BatSat when
both consume Axeyum's ordered CNF. The native warm-Z3 win therefore moves to
the word-level representation/integration boundary. Z3 is nevertheless still
both the main oracle and the only word-level performance comparator in the
accepted Dptf artifact.

The accepted ADR-0215 trace already contains 377 content-hash-bound standalone
SMT-LIB scripts and the exact 561-check occurrence order. That order is
byte-identical to the later ADR-0221 capture, so a neutral solver can consume
the selected workload without rerunning or steering Glaurung.

## Decision

Add a fail-closed Axeyum benchmark runner for cvc5. It validates the clean trace
manifest, event and query-index hashes, query content hashes, occurrence
identity, source-cell verdicts, and model-output cardinality. It runs one cvc5
process per repetition and inserts a full `(reset)` after every standalone
query. This amortizes process startup while preventing declarations,
assertions, or learned state from crossing query boundaries.

Use the official cvc5 1.3.4 Linux x86_64 libc++ static binary, a 250 ms
per-check timeout, one unreported warm-up, and five CPU-pinned measured
repetitions. Keep `--produce-models`: model serialization is part of the
external SMT integration boundary. Require exact SAT/UNSAT outcomes, zero
Unknown, exact SAT value responses, only the expected post-UNSAT `get-value`
diagnostics, and byte-identical stdout across repetitions.

Classify this as a **cold-reset external SMT baseline**, not an in-process or
warm-topology-equivalent comparison. Do not form a paper ratio by dividing its
aggregate batch time by ADR-0215's paired per-occurrence geomeans.

## Evidence

All five repetitions preserve 317 SAT / 244 UNSAT / 0 Unknown across 561
checks. All 206 requested SAT value responses and 216 expected post-UNSAT
diagnostics are present. The 5.63 MB input batch and complete stdout are
byte-identical across repetitions.

CPU-pinned wall times are 2.594976, 2.588175, 2.609810, 2.579961, and 2.593056
seconds. The median is 2.593056 seconds; the mean is 2.593196 seconds with
0.4222% sample CV. Exact evidence is committed under
[`bench-results/glaurung-dptf-cvc5-smt-20260717/`](../../../bench-results/glaurung-dptf-cvc5-smt-20260717/README.md).

## Alternatives

- Spawn cvc5 once per query: rejected because process startup would dominate
  this small-formula workload and obscure the intended integration point.
- Preserve cvc5 state across queries: rejected for this first control because
  the standalone scripts redeclare symbols and the source lineage/delta
  contract has not been implemented for cvc5.
- Strip model requests: rejected because Glaurung consumes models on SAT and a
  verdict-only cell would undercount external integration work.
- Compare the aggregate cvc5 time directly with paired four-cell ratios:
  rejected because the measurement units and protocol boundaries differ.

## Consequences

Dptf now has a neutral third-party verdict oracle and a reproducible external
word-level SMT performance point. The result strengthens correctness evidence
but does not change the honest performance map or explain the warm Z3/Axeyum
reversal.

Next widen the same neutral replay across the accepted small-driver traces and
add a standing well-typed multi-oracle fuzzer. A neutral in-process or
topology-equivalent warm cell is still required before attributing the remaining
representation/integration mechanism. Timeout-sensitive and
finding-authoritative gates also remain open.
