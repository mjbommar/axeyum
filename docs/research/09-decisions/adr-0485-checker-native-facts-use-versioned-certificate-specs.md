# ADR-0485: Checker-native finite facts use versioned certificate specifications

Status: accepted
Date: 2026-08-18
Index-summary: Admit versioned JSON certificate-spec propositions to the fact ledger without inventing an SMT, kernel, or CAS-identity syntax

## Context

The dual-checked Lemire range through degree 400 is a settled finite
proposition, but the fact ledger cannot state it honestly. `smtlib2` and
`axeyum-ir` would imply a finite-field solver surface that ADR-0484 explicitly
defers. `lean4` would imply a kernel vocabulary and term that do not exist.
`cas-term` is explicitly the HyperTerm summation language; broadening it by
accident would make existing dispatch and route claims ambiguous.

Leaving the range outside `artifacts/facts/` is also wrong. The artifacts then
prove something no self-extension consumer can discover, while a future lane
could create an open universal fact and miss the already-settled finite base.

## Decision

Add `certificate-spec` as a fact formal language for checker-native propositions
whose statement is a versioned canonical JSON object. A certificate-spec must
contain non-empty `format` and positive integer `version` fields. It is not
automatically dispatchable: an operation must explicitly register the exact
format and a checker before the frontier may execute it.

The first format is `axeyum-gf2-half-degree-range-statement` version 1. It fixes
the field, inclusive degree endpoints, monicity, irreducibility, and the exact
`floor(n/2)` tail bound. The range checker reads the fact and compares the
parsed formal object to its own expected object before checking the complete
degree population and manifests. Thus changing prose, endpoints, strictness,
or algebraic property without changing the checker fails.

The finite fact uses `search-certificate`, not `cas-certificate`: it has one
checked witness per degree in a finite interval, rather than one algebraic
identity proving all degrees. Its footprint names the polynomial semantics,
Rabin criterion, and finite-range interpretation. The universal conjecture
remains a separate open result and receives no credit from this decision.

## Evidence

- The canonical range contains exactly one found row for every degree 1 through
  400, and the checker rejects missing, duplicate, non-found, or out-of-range
  rows.
- Every child artifact is replayed by both the bit-packed certificate checker
  and an algebraically separate dense-coefficient checker.
- The range checker now rejects a fact whose certificate-spec object differs
  from the exact finite statement it checks.
- The fact validator rejects malformed certificate-spec JSON, arrays/scalars,
  missing format/version fields, empty formats, and non-positive versions.

## Alternatives

### Add a finite-field SMT sort

Rejected. No solver consumer, term semantics, model lift, replay route, or
proof format exists; a fact-ledger syntax is not justification for a public
logic.

### Reuse `cas-term`

Rejected. That name already has a precise HyperTerm denotation and an
identity-certificate route. A finite witness family differs in both syntax and
assurance.

### Record only prose and artifact paths

Rejected. Evidence could then remain green while the proposition's range or
inequality drifted. The checker must bind the machine-readable proposition.

## Consequences

- Checked finite propositions can enter the ledger before a corresponding
  solver or kernel language exists, without impersonating either one.
- Each new certificate-spec format needs a versioned statement contract and an
  explicit checker binding; arbitrary JSON does not become executable.
- Autogenesis will ignore this language until a registered operation names the
  exact format, which is the fail-closed behavior.
- The degree-1-through-400 Lemire fact is discoverable as computed evidence,
  while the all-degree theorem remains unestablished.
