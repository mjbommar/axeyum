# axeyum-smtlib

SMT-LIB 2 parsing and sharing-preserving writing for Axeyum. The parser records
typed terms plus an ordered command stream for scopes and multiple query
points. Parsing a construct does not imply that every solver route decides it.

The [crate documentation](src/lib.rs) has a compile-tested parse/write example.
For the exact command, event, and helper API contract, use the
[SMT-LIB support reference](../../docs/reference/smtlib-support.md).

```sh
cargo test -p axeyum-smtlib
cargo run -p axeyum-smtlib --example proof_gap_shape_census -- query.smt2
```

This crate parses and writes; `axeyum-solver` owns solving and command-faithful
result helpers. The census example reports syntax/IR shape only and must not be
read as a solver verdict.
