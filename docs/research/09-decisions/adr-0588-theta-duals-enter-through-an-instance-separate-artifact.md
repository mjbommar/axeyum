# ADR-0588: Theta duals enter through an instance-separate artifact

Status: accepted
Date: 2026-08-26

## Context

ADR-0560 checks an exact theta dual against an in-memory adjacency matrix, but the only
executable calibration constructs toy graphs and certificates in Rust source. The Krpan--Povh
targets require a durable boundary between an untrusted numerical producer, the independently
retrieved graph instance, and Axeyum's exact checker. A self-contained artifact that embeds its
own graph could be internally consistent while silently naming the wrong target.

This advances the open-problem artifact question in
[`research-questions.md`](../08-planning/research-questions.md#exploration-track-searched-bridge-composition-added-2026-08-01).

## Decision

Exact theta duals use schema `axeyum.theta-clique-dual.v1`, with canonical reduced rational
text and sparse zero-based non-edge multipliers. The graph remains a separate command-line
input. Axeyum strictly parses the archive's `n m` / one-based-edge format, rejects malformed,
duplicate, loop, out-of-range, missing, or trailing records, converts the artifact only after
schema and rational canonicality checks, and then delegates graph support and exact PSD to
ADR-0560/0557. Each input is capped at 512 MiB and graph order at 2,048 before quadratic
allocation.

The checker prints hashes of both independent inputs and exits 1 for a mathematical rejection,
2 for malformed or resource-declined input, and 0 only for an exact verified bound.

## Evidence

Six focused theta tests pass, including strict external-format positive and negative controls.
On the actual 850,123-byte `C500.9` graph (500 vertices, 112,332 edges), the universal empty-
multiplier certificate `t=500` verifies in 50.30 seconds / 70,500 KiB peak RSS with 499 positive
and one zero exact pivot. Changing only `t` to 499 exits 1 in 49.84 seconds at the exact final
PSD obstruction. This is an end-to-end target-instance calibration, not the published bound 73.

Searches through 2026-08-26 found extensive numerical theta implementations and SDP uses but
no basis for claiming this artifact format or checker is the first exact theta certification
route. No priority claim is made.

## Alternatives

- Embed graph edges in the dual JSON: rejected because instance identity would not be
  independently supplied.
- Accept decimal floating multipliers: rejected because the checker would inherit rounding
  policy rather than verify an exact weak-duality witness.
- Wait for a target dual before building interchange: rejected because format mistakes would
  then consume the expensive producer run.

## Consequences

Any MOSEK, CSDP, DSDP, or future Axeyum producer can now hand off exact rational data without
joining the trusted checker. The remaining target blocker is genuinely producer-side: obtain
and safely rationalize multipliers supporting 73, 115, and 168, including any reduction-trace
composition needed by the published calculation.
