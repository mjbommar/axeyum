# axeyum-wasm

Minimal WebAssembly binding for the browser playground. It accepts one scalar
`QF_BV` SMT-LIB script and returns JSON with distinct `sat`, `unsat`, `unknown`,
and `error` statuses. A returned SAT model has crossed the same source replay
boundary as native `SatBvBackend` use.

Use the pinned build, Node smoke, static-server preview, and exact boundary in
the [WebAssembly user guide](../../docs/user-guide/wasm.md). Generated `pkg/`
output is not committed.

```sh
cargo test -p axeyum-wasm
```
