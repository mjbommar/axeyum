# ADR-0379: Sequential isolated workers for corpus explanation

Status: accepted
Date: 2026-08-09

## Context

This closes the measurement question, “How should an ordered exact-list corpus
probe bound allocator retention without changing solver semantics or silently
weakening its resource envelope?” The A5 v1 QF_RDL capture ran the release
`explain_corpus` binary under an 8 GiB `RLIMIT_AS`, emitted 196 of 200 valid
records, and then exited 101. The failed row and the complete 21-row tail each
completed in smaller processes, ruling out a deterministic row-local failure.

An external `/proc/<pid>/status` diagnostic on the exact list then showed the
single process retaining allocator arenas between independent files. RSS fell
to about 98 MiB after an early 363 MiB peak, but rows 57--64 raised the retained
baseline through roughly 0.64, 0.97, 1.14, and 1.30 GiB. It remained pinned
near 1.39 GiB through row 85. Two glibc policy experiments did not reliably
release this memory: a 128 KiB mmap threshold retained about 1.17 GiB by row
63, and a 16 KiB threshold retained about 1.14 GiB across only the eight-row
57--64 slice. Allocator tuning is therefore not a portable safety contract.

The benchmarks are semantically independent. Reusing one address space across
them provides no solver-state contract, but makes the result depend on allocator
fragmentation and corpus history.

## Decision

`explain_corpus` runs each input in a fresh sequential child process, with one
active child at a time, while the original invocation remains the ordered
stream owner.

1. The parent freezes and validates directory/list order before launching any
   child. It passes one exact path, identity, timeout, and output mode to the
   same executable through an internal worker mode.
2. Children inherit the parent's environment and resource limits, including
   the 8 GiB per-process address-space cap. The query timeout and shipped solver
   configuration are unchanged. No workers overlap.
3. In JSON mode each successful child must emit exactly one UTF-8 JSON record
   whose `file` field equals the parent-supplied identity. Empty, malformed,
   duplicate, reordered, or identity-drifted output fails closed.
4. Any nonzero child exit or any child stderr fails the complete parent stream.
   The parent forwards validated stdout in order and flushes after every file.
5. Measurement metadata names this topology, the one-worker limit, and the
   inherited per-process memory scope. It must not claim an aggregate cgroup
   cap that is not enforced.

## Evidence

- QF_RDL attempt 001 retains the exact 196-row, exit-101, zero-stderr failure
  boundary and exact binary/list identities.
- Single-row, four-row, and 21-row tail controls all exit 0 with typed budget
  `unknown`, proving the failure needs earlier process history.
- The `/proc` measurements above demonstrate retained address-space growth and
  reject two allocator-tuning alternatives.
- Unit regressions require one matching JSON record and reject stderr, empty
  output, multiple records, and identity drift.
- The exact former 200-row QF_RDL trigger exits 0 under the unchanged
  24-second/8-GiB envelope with 64 SAT, 42 UNSAT, and 94 typed unknown records.
- Focused tests and strict example Clippy pass. Exact-commit repository gates
  remain mandatory before a credited V2 capture.

## Alternatives

- **Increase the 8 GiB cap:** rejected; it hides unbounded history dependence
  and changes the preregistered resource ceiling.
- **Tune glibc allocation thresholds:** rejected by the measured residual
  retention and by portability concerns.
- **Call `malloc_trim` through FFI:** rejected; it adds platform-specific
  unsafe code and still delegates correctness to allocator behavior.
- **Split or reorder the frozen list:** rejected; it changes population/order
  semantics and could conceal a row-history defect.
- **Continue after a failed child:** rejected; partial streams remain
  non-creditable and a panic is not a typed solver result.

## Consequences

- Per-file memory is reclaimed by process teardown, independent of allocator
  fragmentation, while solver answers, order, and query budgets remain intact.
- Process startup becomes part of wall-clock capture cost but not the internal
  solver timeout. Timing comparisons must identify the topology revision.
- The memory guarantee is per process, inherited from `RLIMIT_AS`; aggregate
  parent-plus-child memory is not claimed as cgroup-enforced.
- A5 v1 captures predate this topology and cannot be combined with v2. After
  acceptance, all three divisions restart from row 1 under a versioned v2
  preregistration.
