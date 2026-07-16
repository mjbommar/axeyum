# ADR-0190: Opt-in bounded replay-checked SAT cache

Status: accepted
Date: 2026-07-16

## Context

ADR-0189 authorizes only exact same-arena scalar SAT-model reuse with mandatory
original-term replay. GQ8 still needs a concrete public policy, deterministic
storage, scope identity, telemetry, and fail-closed implementation before the
ordered Glaurung stream can measure whether caching is useful.

## Decision

Implement ADR-0189 inside each `IncrementalBvSolver` as an explicit,
disabled-by-default replay-checked SAT cache with caller-supplied nonzero entry,
total scalar-model-value, and total Bool/BV payload-bit bounds.

The exact identity is strengthened to include:

- every original scalar assertion in active order;
- the cumulative end of every push/pop frame, including empty frames; and
- every one-shot assumption in caller order.

The cache stores exact vectors and compares them directly. No hash determines
equality. It uses a deterministic vector-backed least-recently-used policy:
successful probes and insertions receive a monotone logical timestamp; the
least timestamp, then lowest vector position, is evicted. Timestamp exhaustion
renumbers entries in the same total order. Entry count and total scalar model
values and payload bits are independently bounded. Models containing functions,
real-division witnesses, arrays, arithmetic values, or any other non-scalar
Bool/BV payload are ineligible.

Only a fresh `Sat(Model)` is insertable. An exact probe clones the model, runs
the solver's existing evaluator replay over all current original assertions and
assumptions, and becomes a hit only if replay succeeds. A false or non-Boolean
replay result evicts the entry and returns a soundness error. An evaluator
failure evicts the entry and returns `Unknown`. Fresh UNSAT, `Unknown`, and
oversized SAT models are counted but not inserted.

Enabling or reconfiguring clears entries and counters. Disabling drops all
entries and counters. Ordinary constructors and checks retain one disabled
branch and no cache allocation, query cloning, lookup, or telemetry work.

## Evidence

Focused tests cover:

- disabled-by-default behavior and successful original-model replay on a hit;
- exact assumption content/order and exact scope-frame boundaries;
- strict-extension misses followed by an exact hit after pop;
- repeated ordinary UNSAT and timeout `Unknown` misses with no entries;
- deterministic LRU entry eviction and independent model-value/bit refusal;
- explicit refusal of non-scalar model payloads;
- invalid zero bounds; and
- a deliberately corrupted private cache model that is evicted and returned as
  an error, never SAT.

The focused full and minimal `qfbv` integration suites pass, as does the
private corruption test. Strict all-target/all-feature Clippy, formatting, and
the documentation link checker pass. The all-feature solver library passes
876/876 tests. The corrected five-driver Glaurung representative gate decides
and agrees on 162/162 queries under both raw and canonical policies with zero
unknowns, errors, disagreements, replay failures, or rewrite decision changes.
The broader integration run remains green through its completed
proof/theory/differential binaries and was stopped only after reaching another
unrelated long-running oracle fuzz tier.

## Consequences

Axeyum now has an executable GQ8 mechanism without changing defaults or
weakening result assurance. Public cache statistics expose hits, misses,
insertions, evictions, replay failures, declined UNSAT/Unknown/oversized
results, and current entry/value/bit gauges. Glaurung can opt in per path-owned
solver and measure the 439 same-lineage duplicate occurrences without sharing
models across arenas or lineages.

This ADR does not authorize a Glaurung default. The next gate must record exact
traffic, cache counters, model/finding identity, Axeyum/Z3 agreement, per-check
latency, total time, and RSS under cache-off/cache-on controls. Ordinary UNSAT
and strict-prefix verdict reuse remain forbidden. Cross-arena reuse and
proof-carrying UNSAT reuse require separate decisions.

## Alternatives

Using the existing 64-bit structural digest as equality was rejected because
collisions cannot carry evidence. An unordered hash table was rejected for the
first bounded implementation because a small deterministic vector gives exact
comparison and an unambiguous eviction order. Ignoring frame boundaries was
semantically sufficient for active conjunctions but rejected because the GQ8
contract explicitly calls for scope identity. Caching UNSAT or `Unknown` was
rejected by ADR-0189.
