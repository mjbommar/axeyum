# Lane: micro-opt-matrix — core microbenchmarks across optimization levels and architectures

<!-- plan-section: lane-status -->

**`DONE`, micro-opt-matrix, 2026-09-07.** The workspace has **no `[profile]`
override anywhere** and no `RUSTFLAGS`: verified across the workspace manifest,
every crate manifest and `.cargo/config.toml` (which sets only
`RUST_MIN_STACK`). So every binary we ship and benchmark is cargo's release
default — `opt-level = 3`, **LTO off**, **codegen-units = 16**, **baseline
`x86-64`** — on hardware with AVX2, BMI2 and POPCNT. This lane measured what
that costs, across eleven build cells, ten benchmark subjects and both fleet
microarchitectures. Full record, including three pre-registered predictions that
were wrong and two measurement bugs in the lane's own driver:
[`docs/research/12-performance/micro-opt-matrix-2026-09-07.md`](../../research/12-performance/micro-opt-matrix-2026-09-07.md).

**Recommendation: change nothing.** No `[profile.release]`, no `RUSTFLAGS`, no
`target-cpu`. No ADR is proposed because no decision is being taken; the diary's
§5 is the record so the question need not be re-opened. The case: the best cell
(fat LTO + `codegen-units = 1`) is worth **1.8%** on the fixed-conflict-budget
SAT matrix and **2.9%** of corpus wall time, decides **the same 10 of 20** p4dfa
files at a 20 s budget (identical decided *set*, all eight arms), and costs
**4.6x the build time**. `codegen-units = 1` alone is 1.1% *slower* on the SAT
core. `x86-64-v3` and `native` are **not positive**: across nine subjects `v3`
loses on three (up to 11%), is neutral on five, and wins on one. And no global
profile can be right — `codegen-units = 1` is −22% on `value_bits` and +5% on
`simplex_pivot`. The one setting that matters, `opt-level = 3` over `2` (5.8% on
the SAT core, 8.8% on Alder Lake, slowest cell on 7 of 7 files), is already the
default.

**The Kissat comparison was not handicapped.** Kissat 4.0.4's own `build.h`
records `gcc -W -Wall -O3 -DNDEBUG`: **baseline `x86-64`, no LTO**, separately
compiled `.o` files — the same configuration class we ship. Rebuilding under the
fairest cell moves the search-only propagation-rate ratio from **0.708 to 0.726**
(Kissat 1.41x → 1.38x faster per second of search) and leaves the **2.56x**
propagations-per-conflict deficit exactly where it is, because that is a
search-trajectory property no build flag can reach.

**Architecture.** Same sha256 binaries on both hosts (identical glibc). The
i5-12600K P-core is 4% faster than the 7840HS overall and 8–9% faster above
100,000 variables, losing only on the two smallest instances — a sign flip
around 58,000 variables, the shape an L3 capacity difference makes. The cell
*ranking* is architecture-independent, which is what the recommendation rests
on. The one exception is `target-cpu`: AVX2 is worth 4–6% on the GF(2) RREF on
Zen 4 and nothing on Alder Lake.

**Two brief premises the source did not support**, both checked before spending
a measurement: `Cdcl::compute_lbd` counts no bits, and **not one**
`count_ones` / `trailing_zeros` call is in the CDCL core — they are all on the
XOR/GF(2) route, which had no bench.
`crates/axeyum-cnf/benches/xor_matrix_gauss.rs` now covers it as the positive
control for the `target-cpu` axis, and it fires: it is the only subject where
AVX2 wins.

**If someone wants this lever back**, the shape is per-package
(`[profile.release.package.<crate>]`), not workspace-wide: the two largest wins
in the lane are `cgu1` on `value_bits` (−22%) and LTO on `dl_negative_cycle`
(−18 to −21%), both an order of magnitude larger than anything on the SAT core.
This lane does not propose it — `value_bits`'s win looks like a `Vec<bool>`
allocation-shape artefact, and fixing the data structure would be worth more
than any flag at zero build cost. Measure that first.

<!-- plan-section: landed-changes -->

| 2026-09-07 | (final) | §5 recommendation with its cost and §6 limitations; the criterion matrix over nine subjects; the GF(2) positive control firing on Zen 4 only; and the driver's second measurement bug — a collector that re-recorded every earlier sweep's ids, whose first duplicate check was keyed on the field that hid it. |
| 2026-09-07 | `9f8d50c32` | Corpus wall time: `fatcgu1` 2.9% faster over the ten decided p4dfa files, decided set identical across all eight arms. The microbenchmark predicted the corpus. |
| 2026-09-07 | `81e5632c3` | Real-workload validation (10 of 20 decided in every cell at a 20 s budget) and the subject where the sign flips: `codegen-units = 1` is −39% on `value_to_lsb_bits` and +1.1% on the SAT core. |
| 2026-09-07 | `0ceb47477` | Gates green (`clippy`/`check --workspace --all-targets --all-features`, exit 0, zero warnings), and the sweep that ran 17 minutes and recorded zero rows while exiting 0. |
| 2026-09-07 | `3834ca8e2` | The architecture axis on identical bytes, and the trajectory check with a negative control that fires on a one-propagation perturbation out of 16.8 million. |
| 2026-09-07 | `6fe58279b` | The like-for-like Kissat number, both engines on one idle host with the prior studies' own Kissat binary. |
| 2026-09-07 | `5e0b88dc0` | The SAT-core matrix: 385 runs, eleven cells, five repeats, trajectory-identical. Three of four predictions wrong, one backwards. |
| 2026-09-07 | `b7d0ea780` | `crates/axeyum-cnf/benches/xor_matrix_gauss.rs` — the GF(2) positive control for the `target-cpu` axis. |
| 2026-09-07 | `455b2132b` | The eleven cells, each with a distinct sha256 and its flags verified in the disassembly; build cost 17.6 s → 80.4 s; Kissat's actual build flags. |
| 2026-09-07 | `ce33bdb6d` | Lane opened: six expectations pre-registered with a predicted ranking, before any build. |
