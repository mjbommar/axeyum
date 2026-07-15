# ADR-0166: Untrusted Glaurung ordered-trace replay boundary

Status: accepted
Date: 2026-07-15

## Context

ADR-0164 demonstrates that retained incremental state can nearly halve
Glaurung's Axeyum time, but its snapshot bridge infers only consecutive
structural prefixes. GQ7 still needs explicit path lineage, scopes, repeated
checks, and exploration-driving model values before Axeyum can compare that
inference with per-lineage warm state. The deduplicated cold corpus erases
those facts.

Glaurung is a downstream source of real solver interactions, not part of
Axeyum's architecture. The trace must therefore remain an optional benchmark
artifact consumed as untrusted input by `axeyum-bench`; no Glaurung type,
lifetime, or execution policy enters the IR or solver API.

## Decision

Accept ordered trace v1 producer commits `7a11c29` and `32cabb0` in the
Glaurung integration branch as the T1 producer boundary. It records exact
content-addressed SMT-LIB, occurrence order, path parentage, push/assert/pop
scope state, all check outcomes, and the exact SMT-LIB expression plus symbol
declarations for every model value used by an exploration choice. Publication
uses a process-private temporary directory, content hashes, a bound query
index, and atomic rename. Its independent producer validator fails closed on
sequence, lineage, scope, hash, query-membership, outcome, and model-choice
inconsistency.

Add `axeyum-bench`'s `glaurung-ordered-trace` binary as the independent T2
consumer. It treats the artifact as hostile bytes and:

1. verifies manifest, event, index, and query-store identity;
2. reconstructs path lineage and every ordered scope stack, checking depths
   and digests at path start, assert, pop, check, and path end;
3. reconciles every check occurrence and outcome with the query index;
4. strictly parses every unique query as QF_BV with exactly one check;
5. re-solves every unique query through Axeyum with bounded timeout and
   original-assertion SAT model replay;
6. requires model reads to follow a same-path SAT check and be consumed
   exactly once by a matching choice; and
7. inserts each unique recorded expression/value equality into its exact
   query, declares any expression-only symbols, and independently requires the
   constrained query to remain SAT.

The replay artifact reports exact duplicates, same-lineage repeats, prefix
extensions and delta assertions, divergent checks, maximum scope depth, model
choices, solver policy, and phase times. Re-solving identical
query/expression/value triples once is sound because the exact bytes and value
constraint are identical; occurrence and consumption counts remain separate.

## Evidence

The Glaurung producer's synthetic lifecycle test covers a root and fork,
repeated check, nested scopes, a SAT model choice, and an UNSAT prune, and runs
the external Python validator before accepting publication. Focused Glaurung
tests and the dual Z3/Axeyum release build pass under the 4 GiB cap.

A bounded real `win10-vwififlt.sys` development trace has event SHA-256
`451af97784800b6ca14b97a58120c4e9b8af52ede65bf8543792ec3f5d6c45a0`. The
producer validator accepts 3,309 events, 235 paths, 508 unique queries, 784
checks, and 243 model reads. Glaurung's shadow run records 784/784 Z3/Axeyum
agreement with no unknown split.

The independent Axeyum T2 replay accepts the same bytes. All 508 unique scripts
strictly parse and decide: 197 SAT and 311 UNSAT, matching every recorded
occurrence. Original-assertion model replay is mandatory for every SAT result.
The 243 choices form 158 unique exact query/expression/value constraints, all
of which independently remain SAT. The trace contains 276 duplicate check
occurrences (35.2%), 156 same-lineage repeated checks, 271 prefix extensions
adding 420 assertions, 348 divergent-lineage checks, and maximum scope depth
45. Focused consumer tests pass under the same memory cap.

This bounded artifact was captured from a development worktree and is T1/T2
functionality evidence, not the reproducible multi-driver GQ10 publication or
a performance baseline.

## Alternatives

Trusting the producer validator alone was rejected because producer and
consumer bugs can agree. Comparing only verdicts was rejected because a
different valid model may steer exploration differently. Requiring complete
model equality was rejected because unconstrained bits legitimately differ;
the contract checks only values actually consumed by a named choice. Importing
Glaurung data structures into an Axeyum solver crate was rejected because that
would invert the product boundary.

## Consequences

T1 and T2 are implemented and independently exercised on a bounded real trace.
The measured duplicate and prefix rates justify proceeding to explicit
per-lineage warm replay, but they do not yet justify verdict caching or default
warm admission.

Next, capture clean ordered traces across the driver set, add deterministic
resource and memory identity to their publication gate, and implement T3 by
mapping each path's events to retained Axeyum solver state. Compare that path
against ADR-0164's snapshot inference with identical occurrences, original
query replay, controlled choices, p50/p95 latency, peak memory, and warm
break-even. GQ8 cache capacity and GQ9 policy remain downstream of those
measurements.
