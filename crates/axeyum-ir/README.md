# axeyum-ir

Typed terms and executable ground semantics for
[Axeyum](https://github.com/mjbommar/axeyum). The crate owns sorts, disjoint
user/internal symbol namespaces, a hash-consed append-only `TermArena`,
lifetime-free `Copy` term IDs, exact and wide values, sort-checked builders, and
the evaluator used for source-model replay.

Start with the compile-tested example in the
[crate documentation](src/lib.rs). The implementation contracts are explained
in [Term IR and arenas](../../docs/internals/term-ir.md) and
[Ground evaluation](../../docs/internals/evaluator.md); SMT-LIB edge cases are
specified in the [BV semantics note](../../docs/research/01-foundations/bv-semantics-and-partial-operations.md).

```sh
cargo test -p axeyum-ir
```

This crate defines syntax and semantics, not a solver. Current decision-procedure
coverage belongs in the generated
[support matrix](../../docs/reference/support-matrix.md).

License: MIT OR Apache-2.0.
