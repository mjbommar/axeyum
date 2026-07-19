# ADR-0248: Preregister exhaustive source-backed policy-difference adjudication

Status: accepted
Date: 2026-07-18

Result state: population frozen; 54/54 labels pending

## Context

ADR-0247 closes the scalar sweep but does not establish a coverage winner. All
five policies preserve the exact 14-row validated set. Their raw positive-control
counts vary from 68 to 122, and tcpip diagnostics vary from 84 to 128, but every
varying row is outside producer-high confidence. Tcpip lacks public source ground
truth, so it is a poor first target for a coverage conclusion.

The nine-driver positive population has exact tracked source and binaries. Its
five-policy raw union has 122 rows, its intersection has 68, and the complete
difference is only 54 rows at 43 sites across seven drivers. Sampling would add
avoidable selection freedom.

## Decision

Freeze and exhaustively adjudicate all 54 source-backed varying rows. The
fail-closed freezer requires accepted, stable, exact Z3/Axeyum raw parity for
each policy and computes union minus intersection without accepting a caller-
selected subset. It binds every row to its policy membership, exact source and
binary identity, v3 report hashes, and accepted analysis hash.

The frozen population is
`corpus/glaurung-finding-populations/policy-difference-adjudication-v1.json`
(SHA-256
`3671540494b85b2a93af3bddbeb1cbad410b34961c65761f9f9799f43d49e999`).
It contains 37 arbitrary-read, six arbitrary-write, six null-dereference, and
five double-fetch rows. All carry only generic `Arg1` ancestry: 38 `**Arg1`, 14
`*Arg1`, and two `Arg1`. Every adjudication field is intentionally pending.

## Acceptance

Review every exact row against both source and the instruction at its recorded
VA. Each row must receive a classification, source-line range, and machine
evidence. No aggregate result is accepted with a pending row, identity drift,
or a row outside the frozen population.

Report separately whether a row is a real vulnerability primitive, ordinary
IRP/request plumbing, a duplicate presentation of an already validated sink,
or indeterminate. The result may justify a scalar default only if independently
validated findings differ. It may justify symbolic memory only if it exposes a
validated residual miss that scalar policy cannot close.

## Consequences

This is an exhaustive source-backed adjudication, not a representative
real-driver recall study. Tcpip remains retained unlabeled evidence. Symbolic
memory, BoundarySet, and DiverseEnum remain deferred while the 54 labels are
pending.
