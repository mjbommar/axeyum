# Installation and Build Profiles

Axeyum is currently a Rust workspace and embeddable library, not a published
standalone `axeyum` command. The fastest no-install trial is the
[browser playground](../playground/README.md). To use the Rust APIs, examples,
or benchmark harness, build from the repository.

## Prerequisites

- Git;
- Rust 1.88 or newer, installed with [rustup](https://rustup.rs/);
- `just` 1.57.0 for repository-wide maintainer commands (optional for the first
  example).

The workspace uses Rust edition 2024 and Cargo resolver 3. The default product
path has no C or C++ dependency.

## Clone and run the first query

```sh
git clone https://github.com/mjbommar/axeyum.git
cd axeyum
cargo run -p axeyum-solver --features full --example first_smtlib_query
```

Expected output:

```text
sat
x = (_ bv255 8)
```

The example uses the pure-Rust solver. `full` enables Axeyum's SMT-LIB front
door and multi-theory API; it does not enable a native solver.

If you only need the scalar Boolean/bit-vector API, the solver crate's default
`qfbv` profile is smaller:

```sh
cargo test -p axeyum-solver --lib
```

For the complete in-tree API and its focused SMT-LIB integration tests:

```sh
cargo test -p axeyum-solver --features full --test smtlib
```

## Embed from a source checkout

The crates are not yet published to crates.io (`publish = false`). In another
Cargo project, point dependencies at a pinned checkout or a local path. During
local development:

```toml
[dependencies]
axeyum-solver = { path = "../axeyum/crates/axeyum-solver", features = ["full"] }
```

For scalar QF_BV only:

```toml
[dependencies]
axeyum-solver = { path = "../axeyum/crates/axeyum-solver" }
```

Pin an exact Git revision in reproducible projects; do not rely on a moving
branch for solver semantics or evidence formats.

## Feature profiles

| Feature selection | Includes | Native dependency |
|---|---|---|
| default (`qfbv`) | pure-Rust scalar Bool/QF_BV solving, models, incremental solving, DIMACS/DRAT APIs | none |
| `full` | SMT-LIB, e-graph, floating point, strings, Lean-kernel integration, and multi-theory APIs | none |
| `z3` | `full` plus the linked Z3 oracle backend | system `libz3` |
| `z3-static` | `z3` with the crate's prebuilt static-library route | downloaded/prebuilt native library |

Z3 is an optional differential oracle and benchmark backend, not the default
runtime path. Do not enable it unless you need that comparison surface.

## Repository checks

For a normal edit, run the narrowest crate or script test that covers the
change. Maintainers run the aggregate gate once before integration:

```sh
just check
```

That command is intentionally broad: formatting, Clippy, workspace tests,
doctests, generated resources, evidence policies, and documentation links. See
the [contributor guide](../contributor-guide/README.md) before changing code.

To smoke-test the committed micro corpus without a native oracle:

```sh
just bench-micro
```

The JSON artifact is written to `/tmp/axeyum-bench-micro-sat-bv.json`. For
reproducible public comparisons and the meaning of decided/unknown/error counts,
use the [benchmark guide](benchmarks.md).

## WebAssembly

The pure-Rust core supports `wasm32-unknown-unknown`. After installing the
target:

```sh
rustup target add wasm32-unknown-unknown
cargo build -p axeyum-wasm --target wasm32-unknown-unknown
```

The checked-in playground and its trust boundary are described in
the [WebAssembly guide](wasm.md). Browser packaging and local site preview
require the pinned `wasm-pack` workflow documented there; the Rust target build
above is only the smallest compile check.

## Next

Run [your first SMT-LIB query](first-smtlib-query.md), then read
[models and replay](models-and-replay.md) and [limitations](limitations.md)
before integrating a solver result into another system.
