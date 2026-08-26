# ADR-0571: Matrix-tensor orbits expose composable selectors

Status: accepted
Date: 2026-08-26
Index-summary: Expose typed first-factor orbit selectors for complete proof-carrying search covers

## Context

ADR-0568 gives the matrix-multiplication tensor encoder a complete first-summand
normalization under the tensor stabilizer. For a normalized encoding, the admitted
first-factor orbit is selected by internal CNF variables. Those variables were previously
private implementation details. A caller could therefore search one chosen orbit, but could
not construct a complete cube cover without duplicating and depending on the encoder's
variable-allocation order.

Cube-and-conquer and orbit splitting are established prior art. The architectural question
here is narrower: how a public Axeyum encoding exposes the exact semantic partition needed by
a generic, proof-carrying cover without exposing unrelated CNF internals.

## Decision

Each normalized `TensorRankEncoding` exposes an ordered slice of typed
`TensorFirstFactorOrbit` descriptors. A descriptor contains the canonical first-factor
support and the exact CNF selector whose truth means that the normalized slot-zero summand
uses that support. Generic tensor encodings expose an empty slice.

The selectors inherit the encoder's exactly-one constraint. Callers may construct the full
Boolean product of the selector literals with `axeyum-cnf`'s cube machinery. This deliberately
includes inconsistent Boolean leaves: the base formula refutes them, while the generic
covering proof establishes that the emitted cubes exhaust all assignments independently of
the base formula. A successful global UNSAT claim requires every leaf proof plus the covering
proof to check against the exact emitted formula.

The descriptor does not claim that normalization itself is complete. That mathematical
boundary remains ADR-0568; this decision makes its finite cases explicit and composable.

## Evidence

- The `<2,2,2>` normalized encoding reports the canonical supports `[0]` and `[0,3]` with
  their exact deterministic selectors. The resulting four Boolean-product cubes have a DRAT
  covering proof accepted by the independent checker.
- A generic tensor encoding reports no matrix-specific orbit descriptors.
- The `<3,2,4>` rank-19 encoding reports the same two support types and emits a four-leaf
  cover over selectors 495 and 496. The cover CNF and covering DRAT proof are retained with
  hashes in the bilinear open-problem package.
- Focused tensor-decomposition tests and all-feature Clippy pass. Mutation coverage rejects a
  missing cube through the generic covering checker and checks the exact support-to-selector
  mapping at the tensor boundary.

## Consequences

Search drivers can now split a normalized matrix-tensor problem by all admitted first-factor
orbits without copying private CNF layout. The same descriptors can feed local solvers,
distributed queues, or certificate manifests while retaining deterministic semantic labels.

The interface does not authorize a solver's status and does not turn an interrupted leaf
into evidence. UNSAT authority still comes only from checked leaf proofs and a checked cover;
SAT authority still requires model lifting and replay against the original tensor equation.
