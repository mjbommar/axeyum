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
cargo run -p axeyum-lean-import --example nat_mod_invariant_specialization -- \
  nat-mod-invariant.ndjson target.ndjson
cargo run -p axeyum-lean-import --example nat_mod_invariant_specialization -- \
  nat-mod-invariant.ndjson target.ndjson --probe-dvd-gcd
cargo run -p axeyum-lean-import --example nat_fib_iterate_recurrence -- \
  --native-composition --stream r080.ndjson
cargo run -p axeyum-lean-import --example nat_fib_native_definition_probe -- \
  r082.ndjson
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

`nat_mod_invariant_specialization` exercises the receipt-backed theorem
specialization boundary on the real remainder proof. It composes the generic
proof and named native arithmetic helpers into a private target, applies those
checked declarations, replays the specialization receipt, requires an empty
footprint, and checks that the resulting `Nat.dvd_mod_iff` has the native
theorem's kernel type shape. Optional `--probe-dvd-gcd` additionally measures
the exact checked target-leaf frontier without publishing a failed private
clone or writing the ledger.

The two native-Fibonacci probes exercise the reverse composition direction.
Checked admission follows the source closure's dependency order across ordinary
definitions and atomic singleton packages, so typeclass and product support is
available before `Nat.fib`. The r080 mode reconstructs the already fixed
`Nat.fib_add_two` candidate without new search and composes it into the native
Nat kernel; the r082 probe composes the exact target-side `Nat.fib` definition.
Both operations replay their receipts, require empty theorem footprints, leave
their callers unchanged, and write no ledger state.
