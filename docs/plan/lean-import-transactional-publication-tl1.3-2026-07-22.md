# TL1.3 result — transactional Lean environment publication

Date: 2026-07-22

Status: complete

Decision: [ADR-0348](../research/09-decisions/adr-0348-owned-lean-import-publication.md)

## Result

The format-3.1 importer no longer mutates a caller-owned kernel. It stages the
entire stream in a private fresh `Kernel` and returns an owned
`CompletedImport` only after EOF, metadata validation, translation, independent
kernel admission, and exported-recursor comparison all succeed. Any error drops
the staging state and returns no environment or arena-relative handle.

This closes TL1.3's whole-environment publication requirement for the delivered
stream. The previous
documentation-only rule—“pass a fresh kernel”—is removed because it still let a
caller inspect earlier declarations after a late error.

Format 3.1 has no footer or expected record count. `CompletedImport` therefore
means every delivered record checked through EOF; it does not authenticate the
bytes as the producer's intended entire export. ADR-0349's TL1.4 corpus measures
record-boundary prefixes explicitly, while TL0.3/TL1.6/TL1.9 own external
digest/manifest and durable completion identity.

## Public contract

The public entry point is now:

```rust
pub fn import_ndjson<R: BufRead>(
    reader: R,
    limits: ImportLimits,
) -> Result<CompletedImport, ImportError>;
```

`CompletedImport` owns one matching pair:

- `kernel()` borrows the complete independently checked environment;
- `report()` borrows its import-time inventory and provenance;
- `into_parts()` explicitly transfers the `Kernel` and `ImportReport`.

The fields are private. Callers cannot manufacture a completed wrapper from an
unchecked kernel or mismatched report. There is no public stream-import
function accepting `&mut Kernel`.

Internally, record-by-record streaming admission remains unchanged and does not
duplicate the arena. Only the publication point moved: construction of
`CompletedImport` occurs after the private routine returns success.

## Why this shape

Snapshot-and-truncate rollback would have to repair the environment, name and
level interners, segmented expression arena and metadata, 64 expression-
interner shards, collision lists, inference/WHNF caches, and generated
inductive declarations together. Cloning a large kernel would add peak memory
and blur ownership of arena-relative IDs. An owned staging result needs neither
operation and makes partial publication unrepresentable through the public API.

This slice deliberately does not merge a stream into an arbitrary pre-existing
kernel. That requires authenticated environment/dependency identity and a
handle-safe composition contract. Silent replacement would invalidate existing
IDs, while in-place extension would recreate the partial-publication problem.

## Positive evidence

All existing exact fixtures preserve their prior results through the new
publication type:

- flat fixture: eight admitted declarations with axiom `P`;
- direct-recursive fixture: eleven declarations with zero axioms;
- projection fixture: nine declarations and the same selector computation;
- Nat-literal fixture: ten declarations with zero axioms and reduction to `37`;
- repeated imports retain identical reports and declaration debug projections.

The dedicated publication test verifies that the borrowed and consumed kernel
environment length matches the report's admitted-declaration count.

## Negative evidence

The late-failure matrix reaches each distinct failure class after the staging
kernel has consumed some or all valid input:

- malformed JSON appended after the complete valid flat stream;
- kernel rejection in the final flat-fixture declaration;
- the quotient package after earlier dependency declarations;
- record-limit exhaustion one record before the flat stream completes;
- an injected I/O failure after every valid fixture byte has been delivered.

Every case returns `ImportError`; none has a `CompletedImport` branch. Existing
syntax, topology, safety, literal, projection, recursor, resource, and format
mutations retain their stable rejection classes.

## Validation

The focused importer gate passes 20 integration cases plus its example target.
A compile-fail doctest proves downstream code cannot forge private
`CompletedImport` fields. Warning-denied Clippy/rustdoc, 14
compatibility/prototype tests,
generated compatibility validation, the parity-prose checker,
foundational-resource validation, focused rustfmt, JSON parsing, and
documentation links pass under build concurrency capped at two.

## What this does not claim

- no persistent on-disk checkpoint or crash-resume protocol is added; TL1.6
  owns completion-last durable publication;
- no arbitrary existing kernel can be extended or merged;
- no new wire construct or Lean semantic fragment is admitted;
- TL1.4's exhaustive record-by-record mutation corpus has since landed;
  TL1.7's declaration dependency digests remain open;
- transactionality does not broaden the exact K0/K1 compatibility claims.

## Next action

TL1.4 subsequently generated and froze the 226-case mutation corpus against
this boundary. Resume the immediate queue at TL1.7 declaration content and
dependency digests.
