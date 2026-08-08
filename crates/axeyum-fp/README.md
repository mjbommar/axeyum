# axeyum-fp

IEEE-754 floating-point formula builders over Axeyum's typed IR. The crate
constructs classification, comparison, arithmetic, rounding, and conversion
circuits; it does not by itself decide a formula or certify the complete
floating-point-to-bit-vector reduction.

The exact builders and format conventions are in the
[crate documentation](src/lib.rs). Current solving and evidence coverage is
authoritative only in the generated
[support matrix](../../docs/reference/support-matrix.md) and
[trust ledger](../../docs/reference/trust-ledger.md).

```sh
cargo test -p axeyum-fp
```
