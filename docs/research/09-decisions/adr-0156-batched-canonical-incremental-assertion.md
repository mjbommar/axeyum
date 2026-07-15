# ADR-0156: Batched canonical assertion for cold incremental clients

Status: proposed
Date: 2026-07-14

## Context

Accepted ADR-0155 makes Axeyum's canonical v4 policy faster than Z3 on the full
Glaurung cold corpus: 5.625 versus 7.709 seconds. The benchmark canonicalizes
all top-level assertions with one `canonicalize_terms` memo before solving.
Glaurung's current one-shot adapter instead creates a fresh
`IncrementalBvSolver` and calls raw `assert` for every root. Its earlier attempt
to call `assert_configured` was slower because that singular API canonicalized
each root independently under the older rule set. The accepted benchmark win
therefore is not yet an ergonomic, matching integration path.

Calling `canonicalize_terms` in Glaurung and then raw `assert` would discard the
solver's explicit original-root replay boundary. Changing `assert_configured`
silently to defer work until `check` would also alter established incremental
semantics and complicate scope/error behavior.

## Proposed decision

Add two additive methods to `IncrementalBvSolver`:

- `assert_preprocessed_batch(&mut arena, terms)` canonicalizes every Boolean
  root with one shared memo, asserts canonical roots in input order, retains
  each original root for replay, and returns the lowered roots; and
- `assert_configured_batch` selects that route when `SolverConfig::preprocess`
  is enabled, otherwise asserts and returns the original roots.

Validate every root's Boolean sort before canonicalization, including when the
batch is empty or preprocessing is disabled. Encoding otherwise has the same
ordered partial-admission behavior as an explicit assertion loop: if a later
root errors, earlier roots remain active. Document push/pop as the caller-owned
rollback boundary rather than pretending persistent AIG/CNF work is atomic.

Do not change `assert`, `assert_preprocessed`, `assert_configured`, or
`SolverConfig::default`. The Glaurung adapter can make the policy explicit with
one batch call after translation.

## Acceptance gate

- focused tests prove exact equality with `canonicalize_terms`, original-query
  SAT replay/UNSAT behavior, raw configured behavior, empty-batch behavior, and
  pre-admission sort rejection;
- strict Clippy, docs, and the existing incremental/rewrite suites pass under
  4 GiB;
- a benchmark route reproduces Glaurung's fresh `IncrementalBvSolver` plus one
  batch call over all 128 representative queries, with 100% decisions, zero
  Z3/manifest disagreement, and zero original-model replay failures; and
- the batch API is non-worse than the accepted canonical one-shot policy before
  it is recommended to Glaurung. A regression retains the API as explicit
  plumbing but does not change the integration recommendation.

## Consequences

This closes the semantic/API mismatch between the accepted cold benchmark and
the consumer's incremental solver surface without conflating cheap exact
canonicalization with the larger configured reduction pipeline. It does not
replace GQ7: ordered warm traces and delta assertion remain required for true
cross-check reuse.
