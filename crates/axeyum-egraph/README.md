# axeyum-egraph

Axeyum's independent, backtrackable congruence-closure e-graph. It provides
deterministic e-node interning, union/find, explanation forests, push/pop,
theory-variable lists, and bounded e-matching support for equality and
quantifier routes.

This crate has no dependency on another Axeyum workspace crate. Its detailed
data model and resource bounds are documented in the
[crate documentation](src/lib.rs); solver-level coverage remains in the
generated [support matrix](../../docs/reference/support-matrix.md).

```sh
cargo test -p axeyum-egraph
```
