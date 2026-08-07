# Lean kernel and import boundary

The Lean route is split into two crates so untrusted wire parsing does not
silently become part of the checking kernel.

## `axeyum-lean-kernel`

[`axeyum-lean-kernel`](../../crates/axeyum-lean-kernel/src/lib.rs) is an
independent, pure-Rust checker for a selected Lean core. It forbids unsafe code
and depends on no other Axeyum workspace crate. Names, universe levels, and
expressions are hash-consed into deterministic identifiers; a segmented arena
and sharded interner support large shared proof DAGs without changing identity
semantics.

The environment admits declarations only through checked gates. Type inference,
weak-head normalization, definitional equality, inductive checks, and prelude
construction live behind those gates. Callers cannot insert an unchecked
declaration and later present it as a theorem.

After `release_transient_tables_for_export`, an environment is export-only:
memory used by construction can be released, but further construction or
checking is rejected. That lifecycle transition is explicit rather than a
hidden performance mode.

## `axeyum-lean-import`

[`axeyum-lean-import`](../../crates/axeyum-lean-import/src/lib.rs) owns the
untrusted `lean4export` NDJSON boundary. It handles JSON parsing, format
versions, ordering, malformed input, resource limits, and identity manifests;
only successful kernel admission is trusted.

```mermaid
flowchart LR
    wire["lean4export NDJSON"] --> import["Untrusted importer"]
    import --> parse["Parse + validate + limits"]
    parse --> kernel["Kernel admission gates"]
    kernel --> complete["CompletedImport"]
    parse -->|error| fail["No partial environment exposed"]
    kernel -->|error| fail
```

The importer is fail-closed. A `CompletedImport` publishes the kernel and report
only after the full stream succeeds; an error does not expose a partially
admitted environment. Default limits bound line size and record count, and the
report records deterministic identity information for reproducibility. Those
defaults are 16 MiB per NDJSON record and 2,000,000 records per stream.

## Compatibility boundary

The current profile targets `lean4export` format 3.1.0 and selected Lean
constructs. It is not a claim to replace the full Lean implementation.
Nested and mutual inductives, recursors, quotient-related declarations, and
other features are admitted only as their explicit gates and regression
matrices mature.

Current coverage belongs in the generated
[support matrix](../reference/support-matrix.md) and
[trust ledger](../reference/trust-ledger.md). An unsupported or malformed
construct must be rejected; import success alone is never proof validity.
