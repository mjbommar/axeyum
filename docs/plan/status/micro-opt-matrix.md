# Lane: micro-opt-matrix — core microbenchmarks across optimization levels and architectures

<!-- plan-section: lane-status -->

**`WIP`, micro-opt-matrix, 2026-09-07.** The workspace has **no `[profile]`
overrides anywhere** and no `RUSTFLAGS`: verified across the workspace manifest,
every crate manifest and `.cargo/config.toml` (which sets only `RUST_MIN_STACK`).
So every shipped and benchmarked binary is cargo's release default — `opt-level =
3`, **LTO off**, **codegen-units = 16**, and **baseline `x86-64` (SSE2 only)** on
hardware with AVX2, BMI2 and POPCNT. This lane measures what that costs, on the
hot paths the 2026-09-07 benchmark lanes identified, across optimisation
settings and across the fleet's two microarchitectures (Zen 4 and Alder Lake).

Running record, including the pre-registered expectations and where they were
wrong:
[`docs/research/12-performance/micro-opt-matrix-2026-09-07.md`](../../research/12-performance/micro-opt-matrix-2026-09-07.md).

**Next.** Build the matrix cells, measure on real p4dfa CNF at a fixed conflict
budget (trajectory-identical arms, so a wall-time ratio is pure throughput), and
re-run the like-for-like Kissat comparison under the fairest build.

<!-- plan-section: landed-changes -->

| 2026-09-07 | (this commit) | Lane opened: status file and diary with pre-registered expectations, recorded before any build. |
