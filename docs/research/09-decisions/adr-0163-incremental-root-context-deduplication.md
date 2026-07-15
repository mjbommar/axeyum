# ADR-0163: Incremental root-context deduplication

Status: accepted
Date: 2026-07-15

## Context

ADR-0162 reduces the pinned representative corpus from 782,716 to 615,537
incremental clauses, but leaves 69,632 clauses (12.75%) above the same-revision
one-shot encoder's 545,905. The proposed follow-up was deliberately
attribution-first: distinguish guarded roots, repeated assertions, negative
roots, exact clause duplicates, and tautologies before adding another default
data structure.

The opt-in profile finds 4,055 root assertions. None is guarded because this
deduplicated cold corpus creates a fresh base-frame solver for each query;
guarded-root cost therefore cannot explain this residual. There are 1,981
same-`(root literal, selector)` repeats. Of 203,562 root-clause attempts,
64,715 exactly duplicate an existing clause: 64,637 duplicate a prior root and
78 duplicate a constant or definition clause. There are no duplicate
definition clauses and no tautological clauses. Negative AND roots account for
657 fresh and 147 reused downward definitions, much less than the repeated-root
opportunity.

## Decision

Retain an exact deterministic set of installed `(AIG node, inversion,
selector)` root contexts in `IncrementalCnf`. Synchronize the growing AIG
first, then skip expansion when the same context is asserted again. Insert a
context only after its complete first encoding succeeds, so an encoding error
cannot make a retry disappear.

Include the selector in the key. A permanent assertion and a scoped assertion,
or assertions under two different selectors, remain distinct. Repeating a root
under one selector is redundant because the guarded clauses from its first
assertion remain in the monotone SAT database even after that selector is no
longer assumed. Popped selectors are never reused.

Keep exact clause-level duplicate attribution opt-in. Do not retain a
production clause fingerprint index: its structural result is stronger, but
its native client cost fails the acceptance boundary.

## Evidence

The profile is additive and overhead-free on the ordinary constructor. It
exports root assertion/context counts, root clause attempts and payload widths,
exact definition/root duplicates, root-vs-non-root overlap, tautologies, and
fresh/reused negative-root definitions. Focused tests cover same-context
deduplication, cross-selector separation, scoped activation/pop behavior,
negative-root attribution, monotone deltas, and zero ordinary diagnostic
counters.

The complete 4 GiB-capped `just check` gate is green: formatting, strict
workspace all-target/all-feature Clippy, all-feature tests and doctests,
warning-denied Rustdoc, the QF_BV feature profile, 31 Glaurung harness tests,
the pinned regular capture gate, foundational resources, generated-artifact
drift, and documentation links. The regular gate decides and manifest-matches
all 128 queries under raw and canonical policies with zero errors,
disagreements, or replay failures; this run's Axeyum/Z3 ratios are
1.222x/0.342x.

On the pinned 128-query representative corpus, all queries decide and agree
with both the manifest and in-process Z3, with zero errors, disagreements, or
model-replay failures. The AIG remains 450,498 nodes. Exact root-context
deduplication skips 1,981 assertions and reduces incremental clauses from
615,537 to 558,787 (-56,750, or 9.22%). The residual over one-shot falls from
69,632 clauses (12.75%) to 12,882 clauses (2.36%). The cheaper key deliberately
leaves 7,887 root clauses that duplicate clauses produced by a distinct root
context, plus 78 root clauses that duplicate non-root clauses.

The unprofiled native gate uses Glaurung commit `f56ffa8`, the same
Z3-authoritative `win10-vwififlt.sys` stream, and isolated release builds of
Axeyum baseline `81c6cde6` versus the candidate. Two interleaved pairs each
execute 13,126 identical queries with 13,126 agreements, zero unknowns, and the
same findings:

| Build | Axeyum mean | Z3 mean | Mean Axeyum/Z3 |
|---|---:|---:|---:|
| ADR-0162 baseline | 17.697 s | 6.346 s | 2.789x |
| exact root-context dedup | 17.325 s | 6.373 s | 2.719x |

Axeyum improves 2.10%; Z3 changes 0.41%; the mean per-run normalized ratio
improves 2.51%.

## Rejected alternative

A collision-safe exact root-clause index was implemented and measured before
the cheaper context key. It canonicalized and indexed each production root
clause, reduced clauses further to 550,900, and removed all 64,637 prior-root
duplicates while preserving every correctness gate. It nevertheless regressed
mean native Axeyum time from 17.715 to 18.098 seconds (+2.16%) and the mean
normalized ratio by about 1.59% across two interleaved pairs. Clause sorting,
hashing, and lookup cost more than the saved SAT work on this stream, so that
production index was removed. Its exact attribution counters remain useful
only behind `with_profiling`.

## Consequences

The default incremental encoder now avoids repeated assertion-tree traversal
and clause emission with one exact context lookup per asserted root. Scope
semantics, AIG/CNF variable maps, learned state, model lifting, and original-term
replay are unchanged.

This closes the large measured GQ5 incremental/one-shot clause residual: only
2.36% remains, and the largest directly attributed negative-root opportunity
is just 657 clauses. Do not add another default dedup/fusion structure from
that small count without a new native acceptance measurement. Move the primary
client effort to GQ1's multi-driver publication boundary and GQ7's ordered
warm-trace integration, where retained state can exploit the 46.18% duplicate
occurrences observed in the real driver stream.
