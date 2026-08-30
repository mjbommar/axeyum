# ADR-0811: Executable machine semantics precede machine proof

Status: accepted
Date: 2026-08-30
Index-summary: A dedicated pure-Rust machine-semantics crate owns A0, source-pinned RV64I/x86-64 slices, traces, and relations before solver formulas or Python projections may represent machine claims.
Index-status: accepted

## Context

The companion textbook requires complete A0 execution, constrained real-ISA
decoders and steps, cross-machine relations, and replayable evidence. Axeyum's
solver, certificate, kernel, and Python layers exist, but none owns executable
instruction-set semantics. Handwritten bit-vector formulas cannot fill that
gap because they do not establish decoding, state, memory, or exceptional
behavior.

## Decision

Add `axeyum-machine` as the pure-Rust semantic authority. Land one vertical
slice at a time: complete A0, pinned RV64I and x86-64 teaching slices,
cross-machine relations, solver queries derived from those semantics, then a
Python projection. The crate has no native-solver dependency. A Python method
may wrap a Rust operation but may not invent one, preserving ADR-0545.

Every public decoder and transition receives direct positive tests and a
nearby negative control. Traces retain every state and classify why execution
stopped. Later evidence manifests bind exact semantic-package and artifact
digests rather than trusting prose or ad hoc logs.

## Evidence

The first slice implements the canonical A0 contract: 8--64-bit modular words,
little-endian memory, immutable four-byte-aligned code, strict reserved-field
decoding, full arithmetic flags, explicit traps, and bounded traces. Its tests
exercise destination, flag, PC, byte-order, range, illegal-encoding, and
post-halt/post-trap controls.

## Alternatives

- Put machine examples in `axeyum-scenarios`: rejected because scenarios are
  solver workloads, not an architectural semantic authority.
- Begin at PyO3: rejected because ADR-0545 requires Python to project Rust.
- Encode each theorem directly in QF_BV: rejected because a formula can bypass
  missing decoder, state, memory, and trap layers.

## Consequences

The workspace gains one crate boundary exercised by three architectures and
their relations. Real-ISA claims remain unavailable until their exact source
revision and form list are pinned. Solver and certificate work consumes this
crate; it does not redefine machine behavior.
