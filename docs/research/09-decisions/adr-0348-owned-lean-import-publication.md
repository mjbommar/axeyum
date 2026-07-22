# ADR-0348: Publish Lean imports only as owned completed environments

Status: accepted

Date: 2026-07-22

## Context

TL1.1-TL1.2 established a deterministic, streaming, fail-closed format-3.1
reader. Its public `import_ndjson` function nevertheless receives a caller-
owned `&mut Kernel` and admits each declaration as it is encountered. Kernel
admission is transactional for one ordinary declaration, but a later malformed,
unsupported, resource-limited, I/O-failed, or semantically invalid record can
return an error after earlier declarations have entered the caller's
environment. The crate documentation asks callers to supply a fresh kernel,
but that convention does not prevent them from observing the partial result.

TL1.3 requires whole-environment publication: a failed import must not expose
any partially checked world. Cloning or rolling back `Kernel` is a poor fit.
Its interned name, level, and expression handles are arena-relative; the large
expression arena is deliberately segmented; typechecking caches are revisioned;
and destructive truncation would have to repair every interner, collision
table, cache, and generated inductive declaration atomically.

## Decision

**Make the public import operation own its staging kernel. It returns a
`CompletedImport` containing the checked `Kernel` and `ImportReport` only after
the entire stream succeeds. On every error the private staging kernel is
dropped and the error contains no environment or arena handle.**

The public shape is:

```rust
pub fn import_ndjson<R: BufRead>(
    reader: R,
    limits: ImportLimits,
) -> Result<CompletedImport, ImportError>;
```

`CompletedImport` keeps its fields private and provides:

- `kernel(&self) -> &Kernel` for read-only inspection;
- `report(&self) -> &ImportReport` for provenance and counts;
- `into_parts(self) -> (Kernel, ImportReport)` for explicit ownership transfer.

The old caller-supplied-kernel entry point is removed rather than retained as a
public footgun. The internal streaming routine may still mutate its private
scratch kernel record by record. Publication is the construction and return of
`CompletedImport`, which happens only after EOF, metadata validation, and all
translation/admission checks succeed.

This is an API correction before TL1.10 stability, not a compatibility shim.
It deliberately does not support extending an arbitrary pre-existing kernel.
Such composition needs a versioned dependency/environment identity and handle-
safe merge design; silently replacing or mutating an existing kernel would
violate the same contract this decision closes.

## Exit gates

TL1.3 is complete only when:

1. every current positive fixture returns a `CompletedImport` with the same
   report, declaration order, computation behavior, and deterministic output;
2. a malformed record appended after a fully valid stream returns only an
   error;
3. late kernel rejection, unsupported quotient input, record-limit exhaustion
   after admitted declarations, and an injected late I/O failure each return
   only an error;
4. no public function accepts `&mut Kernel` for stream import;
5. private `CompletedImport` fields prevent construction of a false completed
   state outside the crate;
6. the example and all workspace consumers use the owned result;
7. warning-denied Clippy/rustdoc, doctest, importer tests, compatibility
   contracts, and documentation links pass under the existing resource policy.

## Alternatives

### Clone the caller's kernel and replace it on success

Rejected. `Kernel` is intentionally not `Clone`; copying a corpus-scale arena
would add peak memory pressure and make arena-relative handle ownership less
obvious. It would also imply support for extending arbitrary environments that
TL1.3 does not authenticate.

### Snapshot lengths and truncate on error

Rejected. Environment entries are only one part of the mutable state. Name,
level, expression, metadata, sharded interner, collision, inference, WHNF, and
generated-inductive state would all need exact rollback. A missed structure
would turn an untrusted parser error into kernel corruption.

### Keep the old API and document that the kernel must be fresh

Rejected. A convention is not a publication boundary. The caller still owns
and can inspect the partially mutated value after `Err`.

### Parse the complete stream into a second wire AST before checking

Rejected for TL1.3. It avoids partial kernel mutation but abandons streaming
and can duplicate large-input memory. Private streaming admission already works;
only its publication boundary is wrong.

## Consequences

- Failed imports cannot expose checked declarations or arena handles because no
  kernel crosses the error branch.
- Successful imports retain the same independent kernel and report; there is no
  second copy or replay pass.
- The public API communicates completion in its type rather than prose.
- Extending pre-existing environments remains an explicit future design rather
  than an accidental behavior.
- TL1.4 can now mutate every record knowing that an error result has no partial
  publication channel; TL1.6 separately owns checkpointed large-stream
  persistence and completion-last durable artifacts.
