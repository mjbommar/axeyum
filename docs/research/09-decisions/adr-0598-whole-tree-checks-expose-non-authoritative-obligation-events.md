# ADR-0598: Whole-tree checks expose non-authoritative obligation events

Status: accepted
Date: 2026-08-27

## Context

ADR-0596 deliberately reports only the largest contiguous completed prefix so parallel scheduling
cannot change the progress stream or authoritative first error. During the live 86.99 GB
`PRIMATEs^-1` proof-tree replay, that counter remained at 940/961 while one worker checked a
921,229,905-byte leaf and the other workers had already exhausted the later queue. Identifying the
active path required a separate recursive manifest walk. A multi-hour independent checker needs to
distinguish a large active proof from a dead worker without weakening deterministic verdicts.

## Decision

The whole-tree checker adds an opt-in event callback alongside its existing deterministic progress
callback. Every event identifies the zero-based obligation index, total, child-index path, leaf /
covering / structural kind, and either `Started` or `Finished { accepted }`. Events are explicitly
non-authoritative and scheduler-ordered. Results remain sorted by depth-first obligation index, the
contiguous progress callback is unchanged, and the same lowest-index failure is returned.

The Boolean-product tree command emits one parseable start and terminal event per obligation. This
is observability for long proof consumption, not a certificate format and not evidence by itself.

## Evidence

The existing whole-tree positive and two-failure controls pin deterministic progress and first-error
ordering. A focused event control pins exactly one start and finish for all five obligations, their
paths and kinds, and accepted terminal states independent of callback order. All-target/all-feature
Clippy for `axeyum-cnf` is the implementation gate.

## Consequences

Operators can identify the exact active proof path and distinguish queue exhaustion from checker
failure without process tracing or manual tree traversal. Event consumers must not infer proof
validity from starts, partial finishes, or event order; only the function's terminal result and the
deterministic progress stream carry checker authority.
