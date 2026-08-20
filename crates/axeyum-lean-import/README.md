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
cargo run -p axeyum-lean-import --example lean4export_import -- export.ndjson Nat.example
cargo run -p axeyum-lean-import --example lean4export_composition -- \
  support.ndjson target.ndjson Nat.example
```

Autogenesis statement inputs use the stronger proof-isolated adapter boundary:

```sh
cargo run -p axeyum-lean-import --example statement_adapter_import -- \
  statement.ndjson Axeyum.Autogenesis.Statement.target
```

The target must be a transparent `definition : Prop := statement`. The entire
stream is rejected if it contains an axiom, theorem, opaque declaration, or
quotient primitive. Success publishes the definition value as a checked goal;
it does not add a proof of that goal.

Import success means the selected translated declarations were admitted; it is
not a claim of complete Lean compatibility or producer-stream authenticity.
The example also accepts `-` for standard input and prints an inventory; it does
not emit or validate an official Lean source file.

`lean4export_composition` is stricter: both imports must have empty axiom
inventories, every selected theorem is admitted into a private clone, the
completed receipt must replay exactly, and every added theorem must retain an
empty kernel-derived footprint. It prints the V5 receipt and never mutates an
input kernel or ledger.
