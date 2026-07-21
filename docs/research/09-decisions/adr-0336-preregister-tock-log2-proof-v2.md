# ADR-0336: Preregister Tock log2 proof v2 lock correction

Status: proposed
Date: 2026-07-21

## Context

ADR-0335 proof v1 closes before compilation or any target property query. Its
pushed runner validates the authenticated capture, canonicals, tools,
registration, and archived source, but Cargo rejects the committed workspace
lock under the frozen `--locked --offline` command. The lock omits the existing
workspace member `axeyum-cas`.

A clean archived-HEAD diagnostic without `--locked` adds exactly one seven-line
`axeyum-cas` package row. The resulting bytes are identical to the pre-existing
workspace lock edit, SHA-256
`e9da054b3407171fcf77aa140098d30dff85f67ec9c499acf6b903b52825181f`.
Commit `3903223c` contains only that lock synchronization plus status prose;
`cargo metadata --locked --offline --no-deps` accepts it. No target query ran.

## Decision

Create a thin proof-v2 policy wrapper over the frozen ADR-0335 runner. Change
only the authenticated source-lock hash, versioned registration/result schemas,
and output path. Preserve the exact canonical bytes, Rust test runner, property
and control families, solver configuration, trust/evidence rules, replay
oracles, row parser, identity projection, pushed-HEAD isolation, resource cap,
and atomicity rules.

## Frozen v2 gates

1. Commit and push this zero-result ADR before adding the v2 wrapper,
   registration, or focused tests. Commit and push those bytes before any
   archived compilation. V1 remains closed and is never rerun.
2. Pin and validate the v1 registration at SHA-256 `18372834...a741` and the
   exact negative at SHA-256 `8e1fbeb5...d5a`. Require v1 status `rejected`, one
   official invocation, one Cargo invocation, zero compilations/queries/rows,
   absent output, and no reported OOM-delta failure.
3. Reuse v1's authenticated capture identity `9ec0a0c3...84b9`, two canonical
   hashes, Rust runner SHA-256 `9af12692...072c`, eight property rows, six
   controls, pure-Rust QF_BV limits/toggles, exact Cargo command, four tool
   identities, archive policy, and resource scope without semantic change.
4. Replace only the registered `Cargo.lock` source hash `004d1441...d552` with
   committed SHA-256 `e9da054b...181f`. Root and `axeyum-verify` manifest hashes
   remain unchanged. The wrapper must not copy dirty worktree bytes.
5. Version the schemas as `axeyum.tock-log2-proof-v2-registration.v1` and
   `axeyum.tock-log2-proof-v2-result.v1`; write only beneath ignored
   `target/tock-log2-20260721/proof-v2`. V2 identity retains the same projection
   rule, excluding observations and per-row wall times.
6. Before an official query, use pushed HEAD and a fresh archived target to run
   only the exact non-authenticated test
   `independent_floor_log_spec_matches_native_small_rows` under
   `--locked --offline`. This is a build/cache/lock preflight, not a target
   property query. It must leave `proof-v2` absent.
7. After that preflight is recorded and pushed, verify local HEAD, tracking,
   and remote `main` equality and invoke the official v2 producer exactly once
   in the registered cgroup. Success requires exactly two functions, eight
   `PROVED`, six `REFUTED_REPLAYED`, zero `UNKNOWN`, and zero `DISAGREE`.
8. Any preflight failure may be corrected only in a new zero-result checkpoint.
   Any official v2 failure closes v2. Never weaken a solver/resource/trust/
   replay gate or rerun after target observation.

No authenticated target query, proof, countermodel, replay, scoreboard row, or
v2 output may exist before the v2 producer and registration are committed,
pushed, and pass their no-query archived compilation preflight.

## Pre-invocation implementation state

The thin wrapper delegates all runner behavior to ADR-0335 after validating the
exact v1 registration/negative lineage, then changes only the expected schemas,
default output, and registered lock hash. The compact v2 registration is
SHA-256 `47ac5872...c6f4`; wrapper SHA-256 is `82d31bcb...014c` and its focused
test SHA-256 is `9c9de094...e255`.

Five v2 tests plus all five v1 producer tests pass. They validate live lineage,
capture and registration inputs, mutation rejection, exact semantic/policy
equality with v1, schema/output separation, parser trust/replay controls,
identity projection, archive safety, and atomic cleanup. `proof-v2` remains
absent. Commit and push these bytes before the archived compilation preflight;
no authenticated target query or scoreboard row has run.

## Rejected alternatives

- **Rerun v1 after committing the lock.** Rejected: its single official
  invocation is observed and frozen.
- **Drop `--locked`.** Rejected: the pushed source snapshot must define the
  dependency graph rather than mutate it during the measured run.
- **Inject the dirty worktree lock into the archive.** Rejected: the corrected
  bytes are now committed and must enter only through pushed HEAD.
- **Broaden cache preparation after the full metadata diagnostic requested
  uncached `wasip2`.** Rejected: the exact targeted build preflight determines
  whether v2's selected package graph has all required cached sources.
- **Change the proof family while correcting dependency metadata.** Rejected:
  v2 isolates the pre-query lock defect only.

## Consequences

- The reviewer-facing proof use case remains semantically preregistered and
  auditable across the negative lineage.
- V2 can distinguish a dependency-snapshot defect from an actual solver,
  evidence, replay, or target-property result.

## References

- [ADR-0335](adr-0335-preregister-tock-log2-proof-scoreboard.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
- [Tock target selection](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md).
