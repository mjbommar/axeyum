# ADR-0248: Preregister exhaustive source-backed policy-difference adjudication

Status: accepted
Date: 2026-07-18

Result state: accepted; 54/54 labels complete

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

## Result

The exhaustive review accepts all 54 findings at all 43 sites with no identity
drift, missing row, extra row, or indeterminate classification. The validator
re-read the named source ranges and the instruction at each VA from IOCTLance
`905629a773f191108273a55924accd9f31145a8d`; all 14 source/binary files are
tracked, clean, and SHA-256 exact.

Thirty rows are ordinary fixed `IO_STACK_LOCATION`, IRP, or I/O-manager-owned
`METHOD_BUFFERED` request/response plumbing. Twenty-four are duplicate
presentations of already validated sinks: their value feeds or is emitted by a
validated operation, but the recorded fixed-buffer load/store or alternate
detector label is not a distinct vulnerability primitive. No row is an
independent real vulnerability primitive, and none is indeterminate.

Thus every scalar policy has zero independent validated primitives in the
varying population. There is no validated policy difference and no validated
residual coverage gap. The result does not select a new scalar default and does
not admit symbolic-memory work.

Exact identities:

- review SHA-256:
  `f61801fc770da5f6e79df4abc7818a31b5f29fe7c1dac2f74186f37703e57603`;
- validator SHA-256:
  `2f3ad18e187064308b35c836dc36659badd6faa2b20b8c9d2638dc174b4ac803`;
- accepted expanded result SHA-256:
  `18fe36e155506f201d7e2eba4404995afa76fd9cca6a602df4c6259200822df3`.

## Consequences

This is an exhaustive source-backed adjudication, not a representative
real-driver recall study. Tcpip remains retained unlabeled evidence. Symbolic
memory remains gated off because the exhaustive labeled difference has no
validated residual gap. BoundarySet and DiverseEnum remain optional settings of
the A0 policy surface that require bounded successor mechanics and new labeled
evidence; they are not follow-on research projects justified by this result.
