# ADR-7200: Statute source identities replay from bounded text snapshots

Status: accepted (bounded contract; final integration gates remain open)
Date: 2026-10-11

## Decision

Keep normalized official statutory section text in `sources/<index>.txt`, where
index is its zero-based position in the template manifest source list. Existing
manifest SHA-256 values and normalization descriptions remain the identity
contract. The offline template validator checks presence, nonempty UTF-8,
canonical collapsed whitespace, at most 64 KiB, and the exact digest of every
snapshot. Parsing is bounded before hashing. Manifest order changes require
matching snapshot movement; mismatched associations fail closed.

## Rationale and evidence boundary

Four fresh edition-pinned HTTPS downloads reproduce the existing Minnesota
manifest hashes. Keeping the bytes permits repeatable independent offline
identity checks instead of validating only hexadecimal syntax. Source retrieval
normalizes the section body before history, strips tags, unescapes entities,
collapses whitespace, and hashes UTF-8 without a trailing newline.

Snapshot identity does not authenticate statutory effectiveness, decide legal
applicability, certify a modeled interpretation, or establish calendar facts.
The finite deadline certificate and its checker remain separate. The existing
manifest effective interval remains explicitly not established.

## Validation

The committed template is a positive control. Missing source files, changed
source bytes or manifest digests, and noncanonical normalization reject. A
private snapshot removes the digest equality guard and must kill exactly one
source-identity test while leaving the other controls passing. No mutation runs
in a shared checkout. Gate results belong in the lane record.

## Adoption evidence — 2026-10-11

The implementation and negative controls were reviewed against this contract.
The fresh native consumer population includes the Date, pack metadata, pack
evaluation and deadline tests: 1166 passed, with one unrelated external SAT
checker test skipped. That external route passed separately with its configured
guarded checker. The offline validator controls were rerun at adoption: 20
tests passed; the recorded template validation checks four source snapshots
and replays one conditional certificate. Detailed provenance and private guard
controls remain in the [feedback completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md)
and [lane receipts](../../plan/notes/28-wide-real-smtlib-writer.md).

Acceptance adopts the stated bounded design, not a claim of legal applicability,
native Rust Date support, general theorem admission or completion of the full
feedback goal. The implementation branch still awaits final workspace checks
and integration into main.
