# QF_BV WebAssembly deployability

- Date: 2026-07-17
- Axeyum revision: `49b36f829604eb67e523d0b7dd6b4c915e46090b`
- Runtime-fix revision: `323b789157d81f79c1bdbbce13b204d77ca9c09a`
- Report SHA-256: `8cdc335f36425aa8a63d6da7d979ee25a2a00af95d43354f83f3de254e5dc033`
- Toolchain: stable Rust 1.95.0, wasm-bindgen 0.2.123
- Optimization boundary: Cargo `release`, no `wasm-opt`

This artifact turns the WebAssembly claim from build-only into an executable
result. The first attempted solve on the pre-fix tree trapped in the 32-bit AIG
hash path even though the wasm32 build was green. The repair folds the hash to
`u32` before conversion, and CI now instantiates the generated module and runs
SAT/UNSAT cases in Node rather than accepting compilation alone.

The generated browser runtime is 1,801,662 bytes (`.wasm` plus JavaScript glue)
before compression. The sum of separately `gzip -9`-compressed runtime assets
is 541,248 bytes. TypeScript declarations are not included. This is a stable
release build without `wasm-opt`, so it is a reproducible baseline rather than
a minimum-size result.

Five fresh Node processes each execute 5,000 measured solves per case after 100
warmups. Median process means are 28.09 microseconds for a small SAT BV8 add,
13.10 microseconds for contradictory BV8 equalities, and 68.82 microseconds for
a structured SAT BV32 query. One fresh Headless Chromium process executes five
5,000-solve batches per case; median batch means are 25.18, 13.08, and 70.66
microseconds respectively. Browser module fetch/load/instantiation is 20.8 ms
in that single local-HTTP observation and is not presented as a stable cold
latency distribution.

These are absolute deployment measurements, not a native/solver speed
comparison and not a real-query Glaurung workload. The shared SMT-LIB parser
also brings `axeyum-fp` and `axeyum-strings` into the 47-package normal target
tree even though `axeyum-solver` selects only `qfbv`. The defensible claim is a
working pure-Rust QF_BV WebAssembly artifact with explicit size and small-query
latency, not a minimum-total-footprint parser surface.

Exact sizes, hashes, repetitions, commands, dependency counts, and claim
boundaries are in [`report.json`](report.json). Reusable Node and browser
measurement harnesses live in `scripts/measure-wasm-qfbv.cjs` and
`scripts/measure-wasm-qfbv-browser.html`.
