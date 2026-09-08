# Microbenchmarks across optimization levels and architectures

Lane `micro-opt-matrix`, running diary. Started 2026-09-07.

Written as the work happens. Entries are appended, never rewritten: an
expectation recorded before a measurement stays visible next to its correction.

## 0. The starting fact

The workspace builds with cargo's release defaults and nothing else. Verified
2026-09-07 by reading the workspace manifest, every crate manifest and
`.cargo/config.toml`:

```
$ grep -rn '^\[profile' Cargo.toml crates/*/Cargo.toml   # nothing
$ cat .cargo/config.toml                                  # [env] RUST_MIN_STACK only
```

Precisely what that does and does not mean:

- We **do** get `opt-level = 3`, so the LLVM auto-vectorizer and loop unroller
  run.
- We **do not** get LTO, so there is no cross-crate inlining across the 27
  workspace crates, and `codegen-units` stays at 16 — so there is no inlining
  across codegen units *within* a crate either, which for a 6,280-line
  `proof_sat.rs` matters more than the cross-crate part.
- We target **baseline `x86-64`**: SSE2 only. **No AVX2, no BMI2, no POPCNT, no
  TZCNT**, on hardware that has all of them. Clause-quality (LBD) computation
  counts distinct decision levels and the watch/bitset scans count trailing
  zeros; without those target features the compiler emits software sequences
  where the hardware has a single instruction.

## 1. The fleet, and why `native` is a measurement and never a proposal

| host | CPU | topology |
|---|---|---|
| s5, s6, s7 | AMD Ryzen 7 7840HS (Zen 4) | 8 cores / 16 threads, AVX-512 present |
| s4 | Intel i5-12600K (Alder Lake) | **hybrid**: cpu0–11 P-cores @ 4.9 GHz, cpu12–15 E-cores @ 3.6 GHz |

Measured on s4 2026-09-07, `/sys/devices/system/cpu/cpu*/cpufreq/cpuinfo_max_freq`:
cpu0–11 = 4,900,000; cpu12–15 = 3,600,000. So `taskset -c 0-7` is the P-core
half, which is what CLAUDE.md's frontier-ratchet note means by the pin — and the
1.84x E-core penalty it records is the reason every timing line below states its
pin.

`x86-64-v3` (AVX2 + BMI2 + POPCNT + LZCNT/TZCNT + FMA) is the highest level
**uniform across this fleet**. Zen 4 has AVX-512; Alder Lake does not.
`target-cpu=native` produces a binary that is not portable between the two, so
it can be measured but never shipped.

**Both hosts run glibc 2.43-2ubuntu2.3** (checked on s4 and s5). That makes the
strongest available protocol possible: **build each cell once, `sha256sum` it,
and run the same bytes on both microarchitectures.** The architecture axis then
compares two CPUs running an identical binary, not two builds.

## 2. Pre-registered expectations

Recorded before any build, so that being wrong is visible.

**E1 — `target-cpu=x86-64-v3` buys almost nothing on the SAT core.** Under 3%.
The reasoning: the `bench-boolean-core` lane measured this week that the core's
cost is watch-list traversal and clause dereference — a pointer-chasing,
memory-latency-bound stream, with the blocking literal missing ~50% of the time
so half of all watch visits touch the clause arena. POPCNT and TZCNT land in LBD
computation and bitset scans, which are a small fraction of a conflict
(resolutions per conflict is 22–39, flat across a 100x size range). Vector
instructions do not speed up a dependent load chain.

**E2 — `codegen-units = 1` is the largest single-flag win on the SAT core, and
larger than LTO.** `proof_sat.rs` is 6,280 lines in one crate; at
`codegen-units = 16` its hot functions can land in different units and lose
inlining across them, and `propagate`/`analyze`/`lits`/`bump_var` are exactly
the small-function-called-in-a-hot-loop shape that inlining exists for. LTO's
cross-*crate* inlining should matter less, because the SAT core's inner loop
does not cross a crate boundary at all. Predicted: cgu=1 worth more than thin
LTO; fat LTO ≈ cgu=1 (fat LTO implies a single unit).

**E3 — `opt-level = 2` vs `3` is inside the noise floor** on these subjects.
The difference is mainly auto-vectorization and more aggressive unrolling,
neither of which applies to a pointer chase.

**E4 — Zen 4 beats Alder Lake P-core on the SAT core** at equal binary, because
this workload is bound by cache/memory latency and L3 capacity rather than
frequency, and the 7840HS has 16 MB L3 against the 12600K's 20 MB — so the
prediction is *weak* and it is recorded as a coin-flip I expect to lose about as
often as win. The frequency advantage (4.9 vs 5.1 GHz boost) is small.

**E5 — the like-for-like Kissat number moves by less than 10%.** The measured
gap decomposes as `conflicts/s = propagations/s ÷ propagations/conflict`, and
the unambiguous deficit is the second factor — a median **2.56x** more
propagation per conflict, which is a *search-trajectory* property that no
compiler flag can touch. Only the first factor (currently between 0.72x and
1.29x of Kissat) is available to a build setting. So the honest prediction is:
the like-for-like correction improves the throughput factor and leaves the
headline 2.56x exactly where it is.

**E6 — the strongest cell is worth 5–12% overall on the SAT core, and build
time roughly doubles.** Enough to be real, not enough to change any decided
count on a 20 s budget.

**Ranking predicted before measuring: cgu=1 ≈ fat LTO > thin LTO > target-cpu-v3
> opt-level.**

## 3. Method

- **Fixed-work, trajectory-identical arms.** Every SAT measurement uses
  `crates/axeyum-cnf/examples/boolean_core_profile.rs` at a fixed conflict
  budget, on real p4dfa DIMACS. Two builds given the same file and budget
  analyse the same conflicts along the same trajectory, so a wall-time ratio is
  pure per-conflict throughput. The counter block is printed by every run and
  compared: if any counter differs between arms, the ratio is not reported.
- **Criterion's error bars are not this machine's error bars.** A sibling lane
  measured two runs minutes apart at load < 1.5 differing by up to ±20% on
  allocation-heavy benches, far outside criterion's sub-1% intervals. So:
  ratios and shapes, not two significant figures; arms interleaved, not run in
  blocks; minimum of *n* repeats, not the mean; `/proc/loadavg` recorded before
  and after every timing run.
- **Binaries pinned by `sha256sum`.** A cell whose hash equals another cell's
  did not actually build differently, and that has to be checked rather than
  assumed — `RUSTFLAGS` and `CARGO_PROFILE_*` are both easy to pass in a form
  cargo ignores.
- **The wrapper for correctness, the prebuilt binary for measurement.** Builds
  go through `scripts/cargo-serialized.sh` (host-wide flock + memory ceiling).
  Timing runs execute the already-built binary directly under `taskset`, because
  the wrapper's own lock queue would be what the stopwatch measured.

## 4. Log

*(appended as the work happens)*

### 2026-09-07 — lane opened

Status file and §0–§3 above written before any build. Nothing measured yet.
