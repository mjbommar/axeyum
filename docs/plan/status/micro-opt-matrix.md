# Lane: micro-opt-matrix — core microbenchmarks across optimization levels and architectures

<!-- plan-section: lane-status -->

**`WIP`, micro-opt-matrix, 2026-09-07.** The workspace has **no `[profile]`
override anywhere** and no `RUSTFLAGS`: verified across the workspace manifest,
every crate manifest and `.cargo/config.toml` (which sets only
`RUST_MIN_STACK`). So every binary we ship and benchmark is cargo's release
default — `opt-level = 3`, **LTO off**, **codegen-units = 16**, **baseline
`x86-64`** — on hardware with AVX2, BMI2 and POPCNT. This lane measured what
that costs. Full record, including three pre-registered predictions that were
wrong:
[`docs/research/12-performance/micro-opt-matrix-2026-09-07.md`](../../research/12-performance/micro-opt-matrix-2026-09-07.md).

**Recommendation: change nothing.** Eleven build cells over seven p4dfa
instances, five interleaved repeats on an idle host, trajectory-identical arms
(385 runs). The best cell — fat LTO + `codegen-units = 1` — is worth **1.8%**
and costs **4.6x the build time**. Nothing else helps: `codegen-units = 1`
*alone* is 1.1% **slower**, and `target-cpu=x86-64-v3` / `native` are not
merely small but **not positive** on the SAT core, with `v3` ranking
consistently below baseline. The one large effect in the matrix is `opt-level`
— `o2` is 5.8% slower and the slowest cell on 7 of 7 files — which the default
already takes.

**The Kissat comparison was not handicapped.** Kissat 4.0.4's own `build.h`
records `gcc -W -Wall -O3 -DNDEBUG`: **baseline `x86-64`, no LTO**, separately
compiled `.o` files — the same configuration class we ship, so our default is
already flag parity. Rebuilding under the fairest cell moves the search-only
propagation-rate ratio from **0.708 to 0.726** (Kissat 1.41x → 1.38x faster per
second of search) and leaves the **2.56x** propagations-per-conflict deficit —
the factor that actually is the gap — untouched, because it is a search-
trajectory property no build flag can reach.

**Two premises in the brief the source did not support**, both checked before
spending a measurement: `Cdcl::compute_lbd` counts no bits (it sorts and dedups
a `Vec<usize>`), and there is **not one** `count_ones` / `trailing_zeros` call
in the CDCL core — they are all on the XOR/GF(2) route, which had no bench.
`crates/axeyum-cnf/benches/xor_matrix_gauss.rs` now covers it, as the positive
control for the `target-cpu` axis.

**Next.** Criterion subjects across cells (running), the real-workload
decided-count validation at a wall-clock budget, and the Alder Lake arm of the
architecture axis, which is waiting for s4 to go quiet.

<!-- plan-section: landed-changes -->

| 2026-09-07 | `6fe58279b` | The like-for-like Kissat number, both engines on one idle host with the prior studies' own Kissat binary: 2.56x propagation volume (unchanged and unchangeable by a build flag), rate ratio 0.708 → 0.726. The premise of a handicap does not hold. |
| 2026-09-07 | `5e0b88dc0` | The SAT-core matrix: 385 runs, eleven cells, five repeats, trajectory-identical. Best cell 1.8%; `codegen-units = 1` alone is a loss; `opt-level 3` is the one large effect and we already take it. Three of four predictions wrong, one backwards. |
| 2026-09-07 | `b7d0ea780` | `crates/axeyum-cnf/benches/xor_matrix_gauss.rs` — GF(2) RREF and watched-row assign/backtrack, the only place in the crate where `target-cpu` can reach, added as the positive control after the CDCL core turned out to contain no bit-counting. |
| 2026-09-07 | `455b2132b` | The eleven cells, each with a distinct sha256 and its flags verified in the disassembly; build cost 17.6 s → 80.4 s; Kissat's actual build flags; the aborted contaminated s4 pass and why it was aborted. |
| 2026-09-07 | `ce33bdb6d` | Lane opened: six expectations pre-registered with a predicted ranking, before any build. |
