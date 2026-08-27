# ADR-0593: Parallel proof-tree progress is root-ordered

Status: accepted
Date: 2026-08-26

## Context

Recursive Boolean-product proof trees can contain tens of gigabytes of textual DRAT and take
hours to replay. The file-backed checker previously emitted only a terminal verdict. A healthy
long check was therefore operationally indistinguishable from a stalled one without inspecting
`/proc` I/O counters. Parallel completion order cannot simply be printed as observed because
Axeyum promises deterministic output.

## Decision

Add `check_cube_refutation_reader_tree_parallel_with_progress`. Workers mark root children
complete under a small shared progress state. The callback fires only for the newly contiguous
root prefix, so every successful run reports `1, 2, ..., total` independent of scheduling.
The existing parallel API delegates to this route with a no-op callback and remains compatible.

The CLI emits each deterministic progress event to stderr. An event means only that checking
work for that root child terminated; it is not a proof verdict. Results are still sorted by root
index, the lowest failure is returned, and the root covering proof is checked only after every
child succeeds.

## Evidence

The recursive parallel positive control reports exactly `(1,2), (2,2)` and accepts the same
composition. The independent two-failure control still returns path `[0]`. Focused tests,
all-target warning-denied Clippy, and warning-denied Rustdoc pass.

The already-running 60 and 83 GB PRIMATEs-inverse trees use the previous binary and are not
restarted merely to gain progress output. Their `/proc` counters show continued reads, but they
remain mathematically uncredited until terminal acceptance.

## Consequences

Future long proof-tree checks expose monotone, deterministic progress without weakening or
reordering proof validation. A slow first root child can delay visible progress even if later
children finish; preserving deterministic order is preferred to schedule-dependent telemetry.
