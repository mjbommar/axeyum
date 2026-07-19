# ADR-0250: Fail closed on Glaurung worklist stop telemetry

Status: accepted
Date: 2026-07-19

Result state: implemented in the Axeyum harness; Glaurung integration remains
owner-coordinated

## Context

ADR-0249 rejected prefix-15/site-hash-one because two Axeyum repetitions
reported the same outer 15-function boundary and the same 91/0 raw/high finding
population but different canonical-model work. Post-result instrumentation on
isolated Glaurung candidate `ff3c0a7` showed that one of 40 inner symbolic
worklists stopped at its wall deadline. The old outer function count therefore
did not prove a fixed inner work population.

This is the same methodology class as the reviewer's earlier warning about
apparent speedups caused by fast-erroring queries: output or verdict agreement
cannot make dropped or time-bounded work admissible. Future authoritative
finding evidence needs a machine-readable stop partition and an explicit
acceptance rule.

## Decision

Extend `scripts/measure-glaurung-authoritative-findings.py` with the opt-in
`--require-deterministic-worklists` gate. When selected, every process must
emit exactly one footer of this form:

```text
[exploration-limits] runs=N completed=N state_budget=N solve_budget=N timeout_budget=N deadline=N
```

The six counts must be nonnegative integers and the five stop classes must sum
exactly to `runs`. `timeout_budget` and `deadline` must both be zero. Declared
state and solve budgets remain admissible deterministic boundaries, but their
complete partition must reproduce within each backend across repetitions.
Availability drift or per-backend partition drift rejects the driver summary.

The harness records the partition in every run and a per-backend summary. It
also records `deterministic_worklists_verified`. Reports created with the new
required gate use schema
`axeyum.glaurung-authoritative-finding-parity.v6` and set
`deterministic_worklists_required=true`. Historical/default invocations retain
the v5 schema so preregistered v5 artifacts remain byte- and contract-stable;
merely observing an optional footer does not relabel old evidence as v6.

## Validation

The focused Python suite first failed on the missing parser and summary gate,
then passed 26/26 after implementation. It covers:

- exact parsing and optional legacy absence;
- required-footer absence;
- inconsistent stop accounting;
- deadline and timeout rejection;
- stable per-backend summary publication; and
- repeated partition drift rejection.

The actual Axeyum-only `ioctlance` binary built from isolated Glaurung
`ff3c0a7` was then run on the first reachable DptfDevGen function. The new
parser accepted its real footer:

```text
[exploration-limits] runs=1 completed=1 state_budget=0 solve_budget=0 timeout_budget=0 deadline=0
```

The general source-backed finding-population validator also rechecks v6 rather
than trusting its producer summary: missing/malformed/inconsistent partitions,
deadline/timeout stops, repeated drift, and summary/run disagreement reject.
Its eight tests pass together with the 26 producer-harness tests.
The existing v5 source-backed positive control also reproduces byte for byte at
SHA-256 `d068d3c2de89a1dbd29053caa3c137146e387be58d6d576f948178856be8b137`.

The full script discovery ran 154 tests: 144 passed, while the 10 existing
benchmark-recipe tests could not start because `just` is absent in this
environment. No recipe assertion ran or failed.

## Consequences

Future fixed-work authoritative campaigns should use v6 and cannot accept an
outer function prefix while silently dropping deadline- or timeout-terminated
inner work. State/solve budget stops remain visible rather than being confused
with completion, and their reproducibility is independently checked from
finding parity.

This decision does not rehabilitate ADR-0249, change its observed bounds, or
make a new performance/recall claim. The v6 gate becomes executable in a full
two-authority campaign only after the Glaurung owner coordinates integration of
the `ff3c0a7` stop-class instrumentation. The live dirty Glaurung checkout is
not modified by this Axeyum change.
