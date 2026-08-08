# axeyum-strings

Word-level string and sequence reasoning over `axeyum-ir`: normalization,
normal forms, bounded inference and arrangements, selected regex and
lexicographic reasoning, and independently rechecked conflict routes.

The detailed slice boundaries and decline behavior are documented in the
[crate documentation](src/lib.rs). They are intentionally fail-closed: a route
that cannot reconcile or check a case declines instead of manufacturing a
verdict. Current public coverage is listed in the generated
[support matrix](../../docs/reference/support-matrix.md).

```sh
cargo test -p axeyum-strings
```
