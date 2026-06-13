# ADR-0017: WebAssembly as a Supported Target

Status: accepted
Date: 2026-06-13

## Context

A downstream use case for "untrusted fast search, trusted small checking" is
running the solver in a **sandbox**: an in-browser playground, an untrusted
plugin host, or a server-side WASI runtime. WebAssembly is the natural sandbox.

Empirically, the entire default stack already *compiles* to
`wasm32-unknown-unknown` unchanged — a direct payoff of the Hard Rule that the
default build has no C/C++ dependency (the pure-Rust `rustsat-batsat` SAT path
and bit-blaster have no native deps; the `z3` backend is feature-gated off). The
one gap is **runtime, in the browser**: the solver calls
`std::time::Instant::now()` for timing/timeout deadlines, and on
`wasm32-unknown-unknown` (no WASI clock) that panics. On `wasm32-wasip1` (WASI)
it works as-is.

## Decision

Make WebAssembly a **supported target**, browser included, by abstracting the
monotonic clock behind a target-conditional alias.

- On `wasm32` (`cfg(target_arch = "wasm32")`), use `web_time::Instant`; on every
  other target, use `std::time::Instant`. `web-time` is a pure-Rust drop-in for
  `Instant` that reads `performance.now()` in browsers and falls back to the std
  clock elsewhere; `Duration` stays `std::time::Duration` (web-time re-exports
  it).
- `web-time` is added **only as a `wasm32`-target dependency** of the two crates
  that read the clock (`axeyum-cnf`, `axeyum-solver`). It is not pulled into
  native builds, and it is pure Rust (no C/C++), so the no-native-dep Hard Rule
  for the default build is preserved.
- Determinism is unaffected: the clock is used only for *timeouts and telemetry*,
  never for results or model values; a wall-clock difference can only change
  whether a budget is hit, which is already a non-deterministic `unknown`
  boundary by design.
- The `axeyum-bench` CLI (filesystem, process) remains a native-only tool; wasm
  support is a property of the **library** crates, which is what a sandbox host
  embeds.

## Evidence

- Verified: `cargo build --target wasm32-unknown-unknown` succeeds for all
  default library crates (`axeyum-ir`/`aig`/`bv`/`cnf`/`query`/`rewrite`/
  `smtlib`/`solver`) before this change; the only runtime gap is the browser
  clock.
- `web-time` already appears transitively in the dependency tree (via rustsat),
  so it is a vetted, in-use crate, not a new supply-chain surface.

## Alternatives

- **WASI-only support.** Simpler (no clock shim needed), but excludes the
  in-browser playground, the most compelling sandbox use case. Rejected.
- **Feature-gate out all timing on wasm.** Loses timeouts (a safety mechanism)
  and telemetry in the browser; the shim keeps full functionality.
- **A hand-rolled clock abstraction.** Reinventing `web-time` for no benefit.

## Consequences

- The solver library runs in browsers and WASI runtimes, enabling a sandboxed
  "trusted small checking" deployment.
- A `wasm32-unknown-unknown` build check should join CI to keep the target green
  (added to the docs/commands; wiring it into the CI workflow is follow-up).
- Any future direct use of `std::time::Instant` must go through the same
  target-conditional alias, or it will reintroduce the browser panic; this is a
  small, local discipline localized to the two clock-using crates.
