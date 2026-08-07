# WebAssembly and the Browser Playground

Axeyum's browser binding runs the pure-Rust scalar QF_BV backend client-side.
The browser downloads static JavaScript and WebAssembly files; solving does not
send the SMT-LIB query to a solver service.

The checked-in playground has two pages:

- [`index.html`](../playground/index.html) accepts a free-form QF_BV query and
  displays `sat`, `unsat`, `unknown`, or `error`;
- [`exercises.html`](../playground/exercises.html) substitutes learner answers
  or checks the negation of a claim, then gives solver-checked feedback.

The generated `pkg/` bundle is intentionally ignored by Git. A checkout without
that bundle shows a readable fallback instead of pretending that live solving
is active.

## Current boundary

The `axeyum-wasm` surface is deliberately smaller than the native `full`
solver API:

| Property | Browser binding |
|---|---|
| Accepted logic | scalar `QF_BV` (Bool and fixed-width bit-vectors) |
| Query shape | one result; at most one `check-sat` or `check-sat-assuming` |
| Output | JSON status, declared logic/status, and diagnostic detail |
| SAT assurance | lifted model is replayed against the active original assertions before `sat` |
| Model display | not exposed by the current JSON API |
| UNSAT proof export | not exposed by the current JSON API |
| Unsupported logic | fail-closed `error` |
| Budget exhaustion | classified `unknown`, never `unsat` |

Use the native [model](models-and-replay.md) and
[UNSAT evidence](unsat-evidence.md) APIs when an integration needs the actual
model or a portable proof artifact. The playground's `unsat` verdict is not a
substitute for exporting and independently checking that artifact.

## Prerequisites

- Rust 1.88 or newer;
- `wasm32-unknown-unknown` from `rustup`;
- `wasm-pack` **0.14.0**;
- Python 3 or another static HTTP server for local preview.

Install the exact packaging tool used by this guide:

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-pack --version 0.14.0 --locked
```

Do not omit the version while using Axeyum's Rust 1.88 minimum. As of the
2026-08-07 validation, unpinned `cargo install wasm-pack` resolves 0.15.0, whose
locked dependencies require Rust 1.91. Version 0.14.0 was clean-environment
tested with Rust and Cargo 1.88.0.

## Compile the Rust target

This is the smallest WASM compile check; it does not generate browser glue:

```sh
cargo build -p axeyum-wasm --target wasm32-unknown-unknown
```

Host tests exercise the same exported Rust function without a browser:

```sh
cargo test -p axeyum-wasm
```

## Build the browser bundle

Run this from the repository root:

```sh
wasm-pack build crates/axeyum-wasm \
  --target web \
  --out-dir ../../docs/playground/pkg \
  --out-name axeyum_wasm \
  --release
```

`--out-dir` is relative to `crates/axeyum-wasm`, not the shell's current
directory; the two `..` components are intentional. The command produces:

```text
docs/playground/pkg/
├── axeyum_wasm.js
├── axeyum_wasm_bg.wasm
├── axeyum_wasm.d.ts
├── axeyum_wasm_bg.wasm.d.ts
└── package.json
```

The bundle is generated output. Do not commit it. Rebuild it after changing the
binding, solver, parser, or locked dependency graph.

## Serve and open the page

ES-module imports and WebAssembly loading require HTTP; opening `index.html` as
a `file://` URL is not a supported workflow.

```sh
python3 -m http.server --bind 127.0.0.1 \
  --directory docs/playground 8080
```

Then open:

- <http://127.0.0.1:8080/index.html> for the solver;
- <http://127.0.0.1:8080/exercises.html> for the exercises.

The status line must say `engine ready · axeyum-wasm 0.1.0`. If it says `demo
mode (no engine)`, inspect the browser console and the troubleshooting section
below.

## Smoke cases

The free-form page includes four useful boundaries:

1. `x + 1 = 0` over eight bits returns `sat`;
2. `x = 0` and `x = 1` returns `unsat`;
3. the 8,192-bit multiplication example returns `unknown` with an encoding
   budget classification;
4. a non-QF_BV script returns `error`.

The first result establishes that a model exists and has passed internal replay;
the current page does not render `x = #xff`. Use the native named-model helper
when the value itself is required.

## JSON embedding surface

The generated module exports:

```text
solve_smtlib_json(input: string, timeout_ms: number) -> string
version() -> string
```

Parse the first result as JSON:

```json
{
  "status": "sat",
  "logic": "QF_BV",
  "expected": null,
  "detail": ""
}
```

`expected` only echoes `(set-info :status ...)`; it is never consulted when
solving. Treat `status` as a four-way result. In particular, never turn
`unknown` or `error` into `unsat`.

The exported call is synchronous. Long solves occupy the page's main thread
until the solver returns; the current playground does not use a Web Worker or
provide cancellation. Keep explicit time and encoding budgets, and do not use
this minimal UI as an untrusted public multi-tenant solver endpoint.

## CI-equivalent Node smoke

Repository CI separately checks the raw WASM build with matching
`wasm-bindgen-cli` 0.2.123 and executes SAT/UNSAT cases under Node:

```sh
cargo build -p axeyum-wasm --target wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.123 --locked
wasm-bindgen --target nodejs --out-dir target/wasm-smoke \
  target/wasm32-unknown-unknown/debug/axeyum_wasm.wasm
AXEYUM_WASM_BUILD_PROFILE=debug \
  node scripts/measure-wasm-qfbv.cjs target/wasm-smoke/axeyum_wasm.js 1
```

This validates Node-target glue and real solver calls. The `wasm-pack --target
web` build plus an HTTP page load is a separate browser-packaging check; neither
one alone proves the other.

## Deployment

Deploy `index.html`, `exercises.html`, and the generated `pkg/` directory under
the same static origin. The server must serve `.wasm` files as
`application/wasm`. No solver process is required server-side.

The query remains inside the page's JavaScript/WASM runtime, subject to the
browser, extensions, and static host you chose. “Client-side” is an architecture
statement, not a claim that an arbitrary hosting environment is confidential.

## Troubleshooting

### `wasm-pack` fails on Rust 1.88

Confirm the pinned version:

```sh
wasm-pack --version
# wasm-pack 0.14.0
```

Reinstall with `cargo install wasm-pack --version 0.14.0 --locked`. The current
0.15.0 dependency graph requires a newer compiler than Axeyum's MSRV.

### The page says `demo mode (no engine)`

Check all three generated paths:

```sh
test -f docs/playground/pkg/axeyum_wasm.js
test -f docs/playground/pkg/axeyum_wasm_bg.wasm
test -f docs/playground/pkg/package.json
```

Serve the directory over HTTP and inspect the browser console. A missing JS or
WASM request usually means the bundle was built into the wrong relative
directory.

### A query returns `error`

The minimal binding rejects non-QF_BV logic and malformed/unsupported syntax.
That is distinct from `unknown`, which means a well-formed admitted query was
not decided within the active procedure or budget.

### A query returns `unknown`

Read `detail`. Timeouts and deterministic encoding limits are expected bounded
outcomes. Reduce the query/width or use the native APIs with an explicitly
reviewed budget; do not relabel the result.
