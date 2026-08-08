# axeyum-bv

Typed Bool/bit-vector lowering from `axeyum-ir` terms to `axeyum-aig` wires.
The lowering retains term-bit and symbol-input maps for source-model replay and
offers one-shot, incremental, deadline-aware, and diagnostic demand variants.

Use the compile-tested example in the [crate documentation](src/lib.rs), and
read [Bit-blasting](../../docs/internals/bit-blasting.md) for the provenance and
least-significant-bit-first contracts.

```sh
cargo test -p axeyum-bv
```

Operator admission is explicit. Current end-to-end solver coverage belongs in
the generated [support matrix](../../docs/reference/support-matrix.md).
