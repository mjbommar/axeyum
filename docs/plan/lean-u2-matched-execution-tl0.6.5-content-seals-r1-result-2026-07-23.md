# Lean U2 TL0.6.5 R1 result — exact paired-evidence content seals

Date: 2026-07-23  
Status: **accepted bounded schema correction; no execution or parity credit**  
Implementation checkpoint: `15e7ba1a`

## Result

TL0.6.5 now fails closed over the content of its paired evidence rather than
accepting well-shaped but declarative digests. The terminal registry validator
recomputes four domain-separated SHA-256 seals:

1. each official or Axeyum execution record seals all of its execution-local
   identity, metrics, state, and evidence;
2. each comparison cites the exact two execution seals and seals the
   normalization, contract, outcome, completion state, and evidence;
3. each paired cell seals its common subject/profile/layer identity, both
   execution records, and the comparison; and
4. each registered population authority seals the ID-sorted sequence of exact
   `(id, cell_sha256)` pairs in addition to its count and sorted-ID digest.

The last layer closes the remaining ID-only substitution path: changing a cell
and correctly recomputing its own seal still invalidates the frozen population
authority.

## Encoding contract

The internal v1 canonical encoding is compact UTF-8 JSON with sorted object
keys, original array order, retained non-ASCII, no insignificant whitespace,
and rejected NaN/infinity. The hash input is the ASCII domain, a NUL byte, and
the encoded JSON value. This is deliberately an Axeyum-owned encoding, not a
claim of full RFC 8785 compatibility.

| Object | Excluded self-field | Domain |
|---|---|---|
| execution | `record_sha256` | `axeyum-lean-paired-execution-v1` |
| comparison | `result_sha256` | `axeyum-lean-paired-comparison-v1` |
| paired cell | `cell_sha256` | `axeyum-lean-paired-cell-v1` |
| authority cell-seal list | none | `axeyum-lean-paired-cell-seals-v1` |

This follows the invariant-serialization requirement described by
[RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html) and the digest-bound
subject model in the
[in-toto Statement v1 specification](https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md),
while retaining a smaller repository-local contract that the Python validator
implements directly.

## Mutation coverage

Focused controls now reject:

- a changed official command under its old execution seal;
- a comparison that cites a different official execution seal;
- changed normalization under the old comparison seal;
- changed common profile identity under the old cell seal;
- a changed and correctly resealed cell under the old population cell-seal
  digest; and
- independently corrupted ID or cell-seal authority digests.

A fully sealed bounded synthetic pair remains valid and non-crediting.

## Validation

The implementation checkpoint passed:

- `python3 -m unittest scripts.tests.test_lean_complete_parity` — 20 tests;
- `python3 scripts/gen-lean-complete-parity.py --check`; and
- `git diff --check`.

The broader documentation, link, detached-root, and full parity gates are run
again at the final documentation checkpoint.

## Truth boundary

This correction does not create a comparison obligation, execute official
Lean or Axeyum, classify an outcome, register a paired cell, complete a paired
population authority, promote U2, satisfy an axis or gate, or grant parity
credit. TL0.6.5 still requires accepted complete TL0.6.3 and TL0.6.4 parents
before deriving its exact obligation authority or authorizing native work.

