# axeyum-lean-kernel

Independent pure-Rust checker for Axeyum's selected Lean core: interned
names/levels/expressions, type inference, reduction and definitional equality,
checked declarations, inductives/recursors, quotients, and deterministic module
export.

This is a kernel boundary, not Lean's parser, elaborator, tactic engine,
compiler, package manager, language server, or full compatibility claim. Read
[Lean kernel and import boundary](../../docs/internals/lean-kernel.md) and use
the compile-tested example in the [crate documentation](src/lib.rs).

```sh
cargo test -p axeyum-lean-kernel
cargo run -p axeyum-lean-kernel --example prelude_axiom_inventory
```
