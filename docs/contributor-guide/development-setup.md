# Development Setup

This page gets a new contributor from a clean clone to a focused green check.
It covers the default pure-Rust workspace. Native solver oracles and the browser
build are optional profiles, not prerequisites for ordinary development.

## Prerequisites

Install:

- Git;
- [rustup](https://rustup.rs/) with a current stable Rust toolchain;
- Rust 1.88.0 when you need to reproduce the minimum-supported-Rust-version
  gate;
- [just](https://just.systems/) for the repository's named commands; and
- Python 3 for documentation, generated-resource, and parity checks.

The workspace declares `rust-version = "1.88"`, edition 2024, and resolver 3 in
the root [`Cargo.toml`](../../Cargo.toml). There is deliberately no repository
toolchain override: local defaults may be newer or nightly, while commands that
must match CI select stable explicitly.

One rustup-based setup is:

```sh
rustup toolchain install stable --component rustfmt clippy
rustup toolchain install 1.88.0
cargo +stable install just --locked
```

If `just` comes from your operating system's package manager, skip the last
line. The project does not require Z3, a C/C++ compiler, Lean, or WebAssembly
tools for its default build.

## Clone and orient yourself

```sh
git clone https://github.com/mjbommar/axeyum.git
cd axeyum
git status --short --branch
git log --oneline -5
```

Before choosing work, read these in order:

1. [`PLAN.md`](../../PLAN.md) for live status, the ordered queue, and the resume
   protocol;
2. the [roadmap](../research/08-planning/roadmap.md) for the current phase and
   exit criteria;
3. the [foundational dependency DAG](../research/08-planning/foundational-dag.md)
   before changing public semantics, transformations, routes, or evidence; and
4. the [ADR index](../research/09-decisions/README.md) for accepted and proposed
   decisions.

[`PROJECT-STATE.md`](../PROJECT-STATE.md) is the short, evidence-linked account
of what the project currently supports. Do not infer current capability from an
old plan or changelog entry.

## Prove the default profile works

Start with the cheap default build and the committed micro corpus:

```sh
cargo +stable check --workspace
cargo test -p axeyum-ir
just bench-micro
```

`just bench-micro` runs the committed SMT-LIB micro corpus through the default
pure-Rust `sat-bv` backend and writes a scratch JSON artifact under `/tmp`.
These commands should not link a native solver.

Reproduce the MSRV contract separately:

```sh
cargo +1.88.0 check --workspace
```

The MSRV gate covers default features. Optional native-oracle features track
stable Rust, as documented in the [feature profiles](../user-guide/installation.md#feature-profiles).

## Choose the right feature profile

The common profiles are:

| Goal | Command | Native dependency? |
|---|---|---|
| Default pure-Rust workspace | `cargo check --workspace` | No |
| One crate's full pure-Rust surface | `cargo test -p axeyum-solver --features full` | No |
| System Z3 oracle | `cargo test -p axeyum-solver --features z3` | Yes |
| Prebuilt static Z3 oracle | `cargo test -p axeyum-solver --features z3-static` | Downloads native Z3 |
| Browser binding | See the [WASM guide](../user-guide/wasm.md) | No |

`full` and `z3` are not synonyms. `full` enables Axeyum's multi-theory
pure-Rust modules; `z3` adds the feature-gated native differential oracle.

## Work in an owned lane

When another contributor or agent is active, use the
[multi-agent worktree model](multi-agent-worktrees.md) and
[operating discipline](multi-agent-operations.md). A typical topic worktree is:

```sh
git fetch origin
git worktree add ../axeyum-my-task -b agent/my-lane/my-task origin/main
cd ../axeyum-my-task
git status --short --branch
```

Use a separate target directory per worktree. Do not point concurrent
worktrees at one `CARGO_TARGET_DIR`; use `sccache` if you need a shared compile
cache. The integration checkout on `main` belongs to the integration owner.

## Optional reference implementations

`references/` is gitignored. Populate it only when implementation work needs a
reference solver or checker:

```sh
./scripts/fetch-references.sh
```

Reference code informs design and differential tests; it does not become a
default linked dependency. New dependency or trust-boundary decisions require
an ADR.

## Your first edit loop

For a one-crate change:

```sh
cargo test -p axeyum-ir
cargo clippy -p axeyum-ir --all-targets -- -D warnings
cargo fmt --all --check
git diff --check
```

For a mixed or unfamiliar change, `just check-scope <base-ref>` maps changed
paths to focused gates and reports anything it cannot scope:

```sh
just check-scope origin/main
```

Read [Testing and validation](testing-and-validation.md) before running the
whole workspace gate or declaring a branch ready.

## Setup completion checklist

- [ ] `cargo +stable check --workspace` passes without a native solver.
- [ ] `cargo +1.88.0 check --workspace` reproduces the MSRV gate when relevant.
- [ ] `cargo test -p <owned-crate>` passes for the area you will change.
- [ ] `just bench-micro` produces a scratch artifact.
- [ ] Your branch/worktree and file ownership are explicit.
- [ ] You have read the current `PLAN.md`, roadmap phase, DAG, and relevant ADRs.
