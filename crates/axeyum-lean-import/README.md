# axeyum-lean-import

Fail-closed `lean4export` 3.1.0 NDJSON ingestion into
`axeyum-lean-kernel`. JSON parsing, version dispatch, resource limits, and
malformed-input handling remain outside the kernel; only a fully admitted
stream publishes `CompletedImport`.

The [crate documentation](src/lib.rs) specifies supported records, default
limits, publication, and identity manifests. See
[Lean kernel and import boundary](../../docs/internals/lean-kernel.md) for the
trust split.

```sh
cargo test -p axeyum-lean-import
cargo run -p axeyum-lean-import --example lean4export_import -- export.ndjson
```

Import success means the selected translated declarations were admitted; it is
not a claim of complete Lean compatibility or producer-stream authenticity.
The example also accepts `-` for standard input and prints an inventory; it does
not emit or validate an official Lean source file.
