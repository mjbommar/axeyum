# ADR-0201: First-class incremental solver trait

Status: accepted
Date: 2026-07-16

## Context

Axeyum has two public interfaces with different operational meaning:

- `SolverBackend` is explicitly one-shot. Its `check` receives a complete
  assertion slice on every call.
- `IncrementalBvSolver` is a real arena-bound warm engine. It retains term-to-
  AIG lowering, CNF, SAT clauses, learned state, scopes, and replay metadata
  across `assert`/`push`/`pop`/`check`/`check_assuming` calls.

The generic `Solver<B>` facade provides stack-shaped ergonomics but currently
stores terms client-side and resubmits the complete active snapshot to a
one-shot backend. It is also part of the full feature profile rather than the
minimal native-free `qfbv` surface. A framework consumer therefore cannot
abstract over a genuinely retained solver without naming
`IncrementalBvSolver` directly or inventing a downstream trait. Glaurung did
the latter, then had to reconstruct path lineage from complete snapshots and a
side-channel path ID even though Axeyum's warm engine already implements the
required state transitions.

The latest real-client evidence makes this an architectural rather than merely
ergonomic gap. Retained warm solving is 2.8--4x faster than Z3 on the measured
path streams, while one-shot configured assertion is a measured loss. The
framework needs to distinguish genuine retained incrementality from an
interface-only assertion stack.

## Decision

Add an always-exported, object-safe `IncrementalSolver` extension trait with the
minimum assumptions-first lifecycle already accepted by ADR-0005/0009:

- `assert(&TermArena, TermId) -> Result<(), SolverError>` adds one Boolean root
  to the current frame;
- `push() -> Result<(), SolverError>` opens a frame;
- `pop() -> bool` closes the latest frame and reports underflow without
  mutating the base frame;
- `scope_depth() -> usize` exposes the logical stack depth;
- `check(&TermArena) -> Result<CheckResult, SolverError>` decides all active
  assertions; and
- `check_assuming(&TermArena, &[TermId])` adds non-persistent assumptions for
  one check.

Implement the trait for `IncrementalBvSolver` by delegating to its existing
inherent methods. The trait contract requires state retained across calls; do
not implement it for the snapshot-resubmitting `Solver<B>` facade or ordinary
`SolverBackend` merely because their observable verdict semantics match.

The trait remains arena-explicit and stores only lifetime-free `TermId`s. One
solver instance is bound to one append-only arena for its lifetime. It takes
exclusive `&mut self` for mutations/checks and provides no clone, fork, shared-
mutable-session, or cross-arena promise.

Keep preprocessing, memory simplification, profiling, caches, assumption cores,
and backend-specific counters on concrete extension APIs. In particular,
`assert_configured` remains a warm-oriented `IncrementalBvSolver` policy, not
the default behavior hidden behind the framework trait. The minimum trait must
not make a cold caller pay configured preprocessing.

## Required evidence

- A generic conformance test must drive base assertions, nested push/pop, a
  contradictory scoped assertion, a contradictory one-shot assumption, and a
  subsequent satisfiable check proving the assumption did not persist.
- The same sequence must run through `&mut dyn IncrementalSolver`, proving the
  API is object-safe for downstream backend selection.
- Non-Boolean assertion/assumption errors, pop underflow, `Unknown`, model
  replay, and scope behavior must remain those of the concrete solver.
- The default/full and `default-features = false, features = ["qfbv"]` profiles
  must compile and test under the 4 GiB wrapper with strict Clippy and rustdoc.
- The embedding guide must show a generic delta-driven path example and state
  that the trait means retained state, not snapshot resubmission.

## Consequences

Glaurung can extend its own solver boundary with a retained incremental session
and drive exact path deltas directly, without encoding Axeyum's concrete type
into the consumer-wide interface. The downstream migration and performance
gate remain separate work: adding a trait does not itself remove Glaurung's
snapshot adapter.

Other theories and backends can implement the same lifecycle only when they
really preserve state and satisfy the replay/evidence contract. A future
factory or capability-discovery layer may construct trait objects, but it is
not required for this first tranche and must not blur one-shot and retained
cost models.

## Implementation and evidence

Commit `1058cf84` adds the always-exported trait and delegates its implementation
to the existing `IncrementalBvSolver` methods without changing their code paths.
The dependency-minimal profile runs 19 library tests plus three new trait
conformance tests. The latter execute the complete lifecycle through both a
generic type parameter and `Box<dyn IncrementalSolver>`, and separately verify
non-Boolean assertion/assumption failures.

The full profile runs the existing 11-test incremental-BV suite plus all three
new tests. Strict Clippy and warning-denied rustdoc pass under both the full and
minimal `qfbv` profiles, formatting and repository link checks pass, and the
embedding guide documents generic delta-driven use. The minimal-profile gate
also exposed and repaired two stale full-only XOR test annotations and six
full-profile-only rustdoc links; no solver behavior changed in those repairs.

This accepts only the Axeyum framework contract. Glaurung still needs a
downstream trait/session migration and real stream gate before claiming that
snapshot reconstruction overhead has been removed.

## Alternatives

- **Add optional incremental methods to `SolverBackend`.** Rejected for this
  tranche: default methods would make snapshot emulation indistinguishable from
  real retention, while required methods would burden every one-shot oracle and
  theory backend.
- **Implement the trait for `Solver<B>`.** Rejected: its current implementation
  only resubmits an assertion vector and would violate the retained-state
  meaning selected here.
- **Expose `assert_configured` in the trait.** Rejected: preprocessing policy is
  backend-specific and a measured cold loss. Raw semantic assertion is the
  stable common boundary.
- **Tie the session to `&'arena TermArena`.** Rejected: this would reintroduce
  context lifetimes into consumer types and prevent append-only term building
  during exploration. The existing explicit same-arena runtime contract is
  retained.
