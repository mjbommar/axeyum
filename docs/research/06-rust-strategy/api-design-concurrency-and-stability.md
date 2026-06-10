# API Design, Concurrency, And Stability

Status: draft
Last updated: 2026-06-10

## Purpose

Decide the Rust-facing API questions that the performance notes do not cover:
ownership topology, thread-safety, cancellation, and stability policy. These
are one-way doors that are expensive to change after 0.1.

## Scope

In scope:

- Arena/handle ownership, Send/Sync goals, cancellation, error model,
  versioning policy.

Out of scope:

- Internal data layout (covered by implementation-principles).

## Core Claims

- Term handles should be plain `Copy` IDs with no lifetime parameter; validity
  is a runtime contract with the owning arena, optionally checked in debug
  builds via arena tags. Lifetime-parameterized handles (the z3.rs `'ctx`
  pattern) infect every downstream type and block portfolio parallelism.
- The arena should be usable as `&Arena` shared across threads for read-side
  work (rendering, evaluation, lowering), with term creation single-writer.
  An append-only design makes this natural.
- Long-running solves need cooperative cancellation from the start: a
  `should_stop` callback or atomic flag in the solver trait. Retrofitting
  cancellation into a blocking API is painful, and every real client
  (symbolic executors especially) needs timeouts.
- Determinism is a public API promise: same input, same config, same seed,
  same result and same statistics. Iteration order over hash maps must never
  leak into output.
- No panics on user input in library crates; panics are reserved for internal
  invariant violations.

## Ownership Topology

```text
Arena: Send + Sync (frozen or single-writer append)
TermId / SortId / SymbolId: Copy, no lifetimes
Query: owns TermIds + config, Send, cheap to clone
SolverInstance: !Sync, owned per thread, Send where the backend allows
Model / Proof / Evidence: fully owned, Send + Sync, serializable
```

## Stability Policy

- Pre-1.0: minor versions may break APIs, but evidence artifact formats get
  their own version field and an explicit compatibility note from the first
  serialized artifact onward.
- MSRV: pin a stated minimum Rust version per release; bump only on minor
  versions.
- The facade crate (if any) re-exports stable items only; research
  instrumentation lives in core crates behind `unstable-` features.

## Design Implications

- Backend FFI types (Z3 contexts, Bitwuzla terms) must be fully encapsulated
  inside backend crates; the solver trait deals only in Axeyum IDs and owned
  values.
- Native solver cancellation (Z3 interrupt, signal handlers) maps onto the
  cooperative flag inside backend crates.
- Cross-arena misuse (TermId from arena A used with arena B) should be a
  debug-mode panic with a clear message, not silent wrong answers.

## Risks

- `Send` solver instances are not guaranteed by all native backends; the trait
  may need to expose thread affinity as a capability.
- Debug arena tagging adds a word per handle if done naively; tag the arena,
  not the IDs.

## Open Questions

- [ ] Frozen-arena type-state (`Arena` -> `FrozenArena`) or runtime
      single-writer discipline?
- [ ] Should cancellation also support memory budget callbacks, not just time?
- [ ] Is an async wrapper worth offering, or do clients spawn blocking threads?

## Source Pointers

- z3.rs lifetime design (cautionary): https://github.com/prove-rs/z3.rs
- Rust API guidelines: https://rust-lang.github.io/api-guidelines/
