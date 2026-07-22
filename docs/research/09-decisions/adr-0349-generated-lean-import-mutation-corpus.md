# ADR-0349: Generate and classify the complete TL1.4 Lean import mutation corpus

Status: accepted

Date: 2026-07-22

## Context

TL1.3 makes publication atomic with respect to the bytes the reader receives:
an error exposes no staging kernel. TL1.4 must now exercise the format boundary
systematically rather than accumulate hand-written examples. Its required
families are truncation at every record, duplicate IDs, forward references,
unknown fields, deep JSON, Unicode, integer boundaries, cycles, and version
drift.

The pinned official format has an initial metadata object followed by a
sequence of primitives and declarations. It defines no footer, expected record
count, root set, or end marker. Because every reference points backward, a
prefix ending exactly after a complete record is itself a syntactically and
topologically valid stream. The reader cannot distinguish “the producer
intended this prefix” from “transport truncated a longer export here” without
an authenticated external byte/count identity. TL1.4 must expose that boundary
rather than falsely claim every truncation rejects.

Primary format source:

- [`lean4export` NDJSON 3.1.0](https://github.com/leanprover/lean4export/blob/v4.30.0/format_ndjson.md)

## Decision

**Generate one deterministic in-tree corpus from the exact official flat
fixture and small purpose-built records. Classify every result by stable public
error variant plus unsupported code, require byte-identical repeated summaries,
and distinguish syntactic truncation from unsealed record-boundary prefixes.**

The corpus contains these families:

1. EOF before every record in the official flat fixture;
2. one-byte syntactic truncation of every individual record;
3. one unknown top-level field on every official record plus selected nested
   unknown fields;
4. duplicate name, level, and expression IDs;
5. name, level, and expression forward/self references plus a declaration
   self-cycle rejected by the kernel;
6. accepted bounded metadata nesting and recursion-limit-exceeding JSON;
7. raw and escaped valid Unicode, a lone surrogate, and non-ASCII Nat digits;
8. negative, floating, `u64` overflow/max, and narrowed-field integers;
9. missing, ill-typed, and unsupported format/exporter metadata;
10. multiple or unknown record discriminants.

Outcomes use these stable classes:

- `published-unsealed` for a well-formed EOF prefix that the bare format cannot
  authenticate as the producer's intended whole artifact;
- `published` for deliberate positive controls;
- `io`, `line-limit`, `record-limit`, `json`, `malformed`, `kernel`, or
  `unsupported:<code>` for rejection variants.

Every mutation has a unique stable ID and expected class. Running the complete
corpus twice must produce an identical ordered summary. No mutation may panic.
The exact family and outcome counts are recorded only after the implementation
passes.

## Completion-boundary rule

`CompletedImport` means “the delivered stream reached EOF and every delivered
record checked.” It does **not** mean “the bytes equal the producer's intended
export.” API documentation and the TL1.3 result must say this explicitly.

Record-boundary prefix acceptance is not fixed by inventing a nonstandard
footer in the 3.1 reader. Exact official artifacts already have retained
SHA-256 identities; TL0.3 must make one manifest drive those identities, TL1.6
must add completion-last checkpoint policy, and TL1.9 must publish large
closures content-addressably. A later authenticated reader may require an
external exact byte digest or record/count contract before granting artifact-
identity credit.

## Exit gates

TL1.4 is complete only when:

1. every specified family above is generated deterministically;
2. every mutation returns its preregistered stable class without panic;
3. every official-record body truncation rejects;
4. every record-boundary prefix is counted explicitly as empty rejection or
   `published-unsealed`, never silently credited as the full fixture;
5. valid raw/escaped Unicode forms agree and invalid Unicode/numerals reject;
6. bounded nesting succeeds while excessive nesting rejects without stack
   failure;
7. the declaration self-cycle reaches independent kernel rejection;
8. two complete runs yield the same unique-ID ordered summary;
9. PLAN, STATUS, result documentation, and the TL1.3 completion wording all
   retain the upstream no-footer limitation;
10. importer tests, warning-denied Clippy/rustdoc, doctest, compatibility,
    resource, and link gates pass.

## Alternatives

### Require a nonstandard footer in every imported stream

Rejected. It would no longer accept official format 3.1 bytes directly and
would conflate Axeyum's artifact envelope with the upstream interchange.

### Treat every EOF prefix as a detected truncation

Rejected as impossible from the bytes alone. Many prefixes are valid streams
under the documented grammar and backward-reference topology.

### Call every accepted prefix a successful full artifact

Rejected. Parser success is not source-identity evidence. The outcome is named
`published-unsealed` and receives no exact-fixture or dependency-root credit.

### Hand-write one case per family

Rejected. It misses record-specific key paths and does not prove deterministic
behavior across the actual fixture population.

## Consequences

- The wire reader gains broad adversarial coverage without changing supported
  Lean semantics.
- TL1.3 atomicity remains valid but its EOF scope is stated precisely.
- Exact fixture/hash provenance remains distinct from parsing/admission credit.
- TL1.5 can fuzz the same discriminants and paths; TL0.3/TL1.6/TL1.9 own
  authenticated artifact completion rather than hiding it in parser prose.
