# ADR-0227: Executable QF_BV WebAssembly deployability

Status: accepted
Date: 2026-07-17

## Context

ADR-0216 makes `axeyum-wasm` a real workspace member and wasm32 build target,
but compilation alone does not establish deployability, latency, or total
footprint. The publication review specifically asks for a WebAssembly latency
number and an honest deployability claim. The shared SMT-LIB parser also pulls
floating-point and string parser crates even though the solver selects only the
`qfbv` feature, so “minimum pure-Rust footprint” requires measurement rather
than inference from Cargo features.

The first executable Node smoke test exposed why this distinction matters. At
the ADR-0226 tree, the wasm32 build succeeded but the first solve trapped in
`AndUniqueTable::insert_without_growth`: the 32-bit AIG hash branch XOR-folded
a `u64` and then attempted to convert the still-64-bit result to `usize`.

## Decision

Repair the target-width hash conversion by producing a `u32` folded hash before
conversion. Add a host regression for the fold and upgrade the wasm CI job from
build-only to generated-module instantiation plus executed SAT/UNSAT cases in
Node.

Commit reusable Node and browser measurement harnesses. Accept a stable Rust
release build processed by matching `wasm-bindgen` without `wasm-opt` as the
first deployability baseline. Report:

1. raw and bindgen WebAssembly, JavaScript glue, gzip size, and hashes;
2. the actual wasm32 normal dependency surface;
3. five fresh-process Node repetitions with fixed warmups and solve counts;
4. a real Chromium execution with five within-process batches; and
5. explicit claim exclusions.

Do not compare these absolute latencies to native Axeyum or another solver
without a separately designed matched experiment. Do not call the result a
minimum-total-footprint build while the shared parser retains unrelated logic
crates.

## Evidence

At Axeyum `49b36f82`, stable Rust 1.95.0 produces a bindgen WebAssembly payload
of 1,792,615 bytes. The browser runtime (`.wasm` plus JavaScript glue) is
1,801,662 bytes uncompressed and 541,248 bytes as the sum of separately
`gzip -9`-compressed assets. No `wasm-opt` pass is applied. The normal target
tree contains 47 unique packages and 11 workspace crates, including
`axeyum-fp` and `axeyum-strings` through `axeyum-smtlib`.

Five fresh Node processes execute 75,000 measured solves in total with no
status mismatch or trap. Median per-process means are 28.09 microseconds for
the SAT BV8-add case, 13.10 microseconds for contradictory BV8 equalities, and
68.82 microseconds for the structured SAT BV32 case. A real Headless Chromium
process executes another 75,000 measured solves; median within-process batch
means are 25.18, 13.08, and 70.66 microseconds. Its one local-HTTP module
fetch/load/instantiation observation is 20.8 ms and is not a cold-distribution
claim.

Exact commands, repetitions, hashes, size accounting, and boundaries are
committed under
[`bench-results/wasm-qfbv-deployability-20260717/`](../../../bench-results/wasm-qfbv-deployability-20260717/README.md).

## Consequences

The artifact can now claim a working pure-Rust QF_BV WebAssembly deployment
with explicit browser bundle size and representative small-query latency. The
claim is stronger than “builds for wasm32” and is protected by an execution
gate.

The measurements do not establish native parity, solver superiority,
real-Glaurung latency, cross-browser/device performance, or a minimized bundle.
The high-variance module-load observations also need more fresh browser
processes before becoming a cold-start claim. A narrower QF_BV parser surface
is now a concrete footprint optimization candidate, but it must preserve the
current API and executable evidence before replacing this baseline.

## Alternatives

- Report only the successful wasm32 build: rejected because it masked an
  immediate runtime trap.
- Report the Node run as browser latency: rejected; Node and Chromium are
  measured and named separately.
- Run `wasm-opt` before establishing a baseline: rejected because the available
  local toolchain lacks it and an unversioned optimization pass would weaken
  reproducibility.
- Call the explicit solver `qfbv` feature a minimum bundle: rejected because
  the dependency tree directly contradicts the total-footprint claim.
