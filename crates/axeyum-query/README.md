# axeyum-query

First-class query values over `axeyum-ir`: assertions, assumptions, nested
scopes, stable labels, structural cache keys, support slicing, and replay
against the complete original query.

The [crate documentation](src/lib.rs) contains a compile-tested builder example.
One-shot backends may submit assumptions as assertions; retained backends can
use native assumption literals without changing query semantics.

```sh
cargo test -p axeyum-query
```

See [Solver dispatch and route contracts](../../docs/internals/solver-dispatch.md)
and [Models and replay](../../docs/user-guide/models-and-replay.md).
