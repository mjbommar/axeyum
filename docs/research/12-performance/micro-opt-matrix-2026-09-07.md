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

  > **Correction, logged the same day** (§4, "two premises the source does not
  > support"): the last sentence is wrong about *this* codebase. `compute_lbd`
  > sorts and dedups a `Vec<usize>` and counts no bits at all, and there is not
  > one `count_ones` / `trailing_zeros` call in the CDCL core. The bit-counting
  > lives in the XOR/GF(2) path. The sentence is left standing because it is the
  > premise the lane started from and the correction is the finding.

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

### 2026-09-07 — the cells, and the proof that each one actually built differently

Eleven cells, chosen one-factor-at-a-time from the current default plus the
three combinations worth testing. Built by
`CARGO_PROFILE_RELEASE_{LTO,CODEGEN_UNITS,OPT_LEVEL}` + `RUSTFLAGS` into a
separate `CARGO_TARGET_DIR` per cell, so no cell can be contaminated by
another's cache and no shipping manifest is touched.

| cell | `target-cpu` | LTO | codegen-units | opt-level |
|---|---|---|---|---|
| `base` | (baseline `x86-64`) | off | 16 | 3 |
| `o2` | baseline | off | 16 | **2** |
| `cgu1` | baseline | off | **1** | 3 |
| `thin` | baseline | **thin** | 16 | 3 |
| `fat` | baseline | **fat** | 16 | 3 |
| `fatcgu1` | baseline | **fat** | **1** | 3 |
| `v2` | **`x86-64-v2`** | off | 16 | 3 |
| `v3` | **`x86-64-v3`** | off | 16 | 3 |
| `v3cgu1` | **`x86-64-v3`** | off | **1** | 3 |
| `v3fatcgu1` | **`x86-64-v3`** | **fat** | **1** | 3 |
| `native` | **`native`** (measurement only) | off | 16 | 3 |

**Every cell's `boolean_core_profile` has a distinct sha256.** That is checked
rather than assumed, because `RUSTFLAGS` and `CARGO_PROFILE_*` are both easy to
pass in a form cargo silently ignores, and a matrix of eleven identical binaries
would produce eleven identical numbers and look like a clean null result.

The flags reach the machine code, verified by disassembly rather than by
believing the build log:

```
base   AVX (v-prefixed) instructions: 0        BMI/POPCNT-class: 22
v3     AVX (v-prefixed) instructions: 1,835    BMI/POPCNT-class: 59
native AVX (v-prefixed) instructions: 1,895
```

**Build cost, s4, measured** (`-p axeyum-cnf -p axeyum-ir -p axeyum-aig -p
axeyum-bv -p axeyum-egraph --benches`, cold target dir, 16 cores):

| cell | build seconds | vs `base` |
|---|---:|---:|
| `base` | 17.6 | 1.0x |
| `native` | 26.6 | 1.5x |
| `o2` | 27.5 | 1.6x |
| `v2` | 39.0 | 2.2x |
| `cgu1` | 48.4 | 2.8x |
| `thin` | 48.5 | 2.8x |
| `fat` | 58.1 | 3.3x |
| `v3cgu1` | 65.4 | 3.7x |
| `fatcgu1` | 70.1 | 4.0x |
| `v3fatcgu1` | 80.4 | 4.6x |

So the strongest cell costs **4.6x the build time** of the default on this
subset. That is the number any adoption proposal has to carry, and on the whole
27-crate workspace it is the dominant cost of the change, not the runtime win.

### 2026-09-07 — two premises in the brief that the source does not support

Both were worth checking before spending a measurement on them.

**(a) LBD does not count bits here.** The brief expects clause-quality
computation to be a POPCNT site. `Cdcl::compute_lbd` (`proof_sat.rs:3388`) is:

```rust
let mut levels: Vec<usize> = clause.iter().map(|l| self.level[l.var().index()]).collect();
levels.sort_unstable();
levels.dedup();
levels.len()
```

A heap allocation, a sort and a dedup — no bit-counting at all. Grepping
`count_ones` / `trailing_zeros` / `leading_zeros` across `axeyum-cnf`,
`axeyum-aig`, `axeyum-bv` and `axeyum-ir`, **not one hit is in the CDCL core**.
They are all in the XOR/GF(2) path (`xor_matrix.rs`, `xor_extract.rs`,
`gf2.rs`, `xor_dpll.rs`, `xor_propagate.rs`, `xor_cdcl.rs`) plus two sites in
`axeyum-bv` and one in `axeyum-ir`'s 128-bit `wide.rs`.

So if `target-cpu` pays anywhere in this codebase it pays in Gaussian
elimination over GF(2), not in the CDCL search — and the XOR path has **no
bench at all**. That is the gap this finding opens, and it is recorded before
the measurement rather than as an excuse afterwards.

Even there the ceiling is low: the loops are
`while b != 0 { let tz = b.trailing_zeros(); …; b &= b - 1; }`, and because
`b != 0` is a loop invariant LLVM can already use bare `bsf` with no
zero-handling on baseline. `x86-64-v3` turns `b &= b - 1` into one `blsr` and
`bsf` into `tzcnt`. That is single-instruction savings inside a loop whose body
also does a bounds-checked load from `self.assignment` — a dependent load that
dominates.

**(b) Kissat is *not* built aggressively.** The brief's premise for the
like-for-like item is that our comparison handicapped us because Kissat is
"a single-TU C program built aggressively". The build on the measurement host
reports its own flags:

```
$ grep '^CC' references/kissat/build/makefile
CC=gcc -W -Wall -O3 -DNDEBUG
$ grep COMPILER references/kissat/build/build.h
#define COMPILER "gcc (Ubuntu 15.2.0-16ubuntu1) 15.2.0 -W -Wall -O3 -DNDEBUG"
```

**No `-march=native`, no `-mavx2`, no `-flto`.** Kissat is compiled for
baseline `x86-64` exactly like us, and it links separate `.o` files exactly
like us. On the two axes the brief named — target features and link-time
optimisation — the existing comparison was **already like-for-like**, and the
handicap it assumed does not exist.

What is *not* symmetric is the third axis. Kissat's hot path gets its inlining
**in the source**: its per-literal helpers live in headers (`inline.h`,
`assign.h`, `fastassign.h`) as `static inline`, so one gcc translation unit sees
`propagate` and everything it calls. Our `propagate` and `analyze` are in one
6,280-line Rust module that rustc splits into **16 codegen units**, and nothing
guarantees a hot callee lands in the same unit as its caller. `codegen-units =
1` is the setting that gives rustc the view gcc gets from Kissat's source
layout — so it, and not `target-cpu`, is the honest candidate for the
like-for-like correction. This is a sharper form of §2's E2 and it was arrived
at from Kissat's build, not from ours.

### 2026-09-07 — s4 is not a measurement host today; the run moved to s7

The first matrix pass was started on s4 with `taskset -c 0-7` (its P-core half,
confirmed from `cpuinfo_max_freq`: cpu0–11 at 4.9 GHz, cpu12–15 at 3.6 GHz) at
load 0.81. Twenty-two runs in, the load rose to 2.37 and the arms went visibly
non-comparable:

```
r0 string1x8.4  v3         1.053s   load=0.85
r0 string1x8.4  v3cgu1     1.807s   load=0.85
r0 string1x8.4  v3fatcgu1  3.247s   load=2.14
r0 string1x8.4  native     2.469s   load=2.14
```

A 3.1x spread across cells on one file, tracking the load column and not the
cell. The cause was another lane's `cargo test -p axeyum-solver --lib` starting
a 27-crate debug build on the same box. The pass was **aborted, not reported**
(`s4-noisy-aborted.jsonl` kept as the record of what a contaminated pass looks
like), and the matrix moved to **s7** — idle at 0.06, Zen 4, uniform cores, no
hybrid topology to control for, and glibc identical to s4's.

Two things this cost, recorded because both are the point of the discipline:

- Per-run `/proc/loadavg` is what made this visible within one pass. Recording
  it only before and after would have averaged 0.81 → 2.4 and looked survivable.
- **`pkill -f "boolean_core_profile /data0"` killed the invoking shell** (exit
  144), because the pattern matched that shell's own command line. This is the
  `pgrep -f` trap CLAUDE.md names, and `pkill` has it identically.

### 2026-09-07 — the matrix, on the SAT core: the default is nearly optimal, and my top-ranked prediction was backwards

s7, idle Zen 4, `taskset -c 0-7`, load **0.04 before / 1.14 after** — the run was
the only load on the box. Seven p4dfa instances, 20,000-conflict budget, eleven
cells, **five interleaved repeats**, minimum of five reported. 385 runs.

**Trajectories are identical across all eleven cells on all seven files** —
same verdict, conflicts, decisions, propagations, restarts, reductions, watch
visits, clause visits, watch relocations, resolutions, redundancy steps and DRAT
byte count. The driver refuses to print a ratio otherwise. So every ratio below
is pure throughput on one search, not two different searches.

| file | vars | base | `o2` | `cgu1` | `thin` | `fat` | `fatcgu1` | `v2` | `v3` | `v3cgu1` | `v3fatcgu1` | `native` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `mobiledevice_…twocond` | 31,482 | 1.000 | 1.043 | 1.015 | 0.994 | 0.996 | 0.989 | 1.001 | 1.005 | 1.018 | 0.990 | 1.002 |
| `string1x8.4` | 40,548 | 1.000 | 1.056 | 1.019 | 1.002 | 1.001 | 0.992 | 1.001 | 1.013 | 1.022 | 0.993 | 1.005 |
| `mobiledevice_…paired` | 58,380 | 1.000 | 1.046 | 1.006 | 0.993 | 0.987 | 0.991 | 0.990 | 1.001 | 1.011 | 0.980 | 0.993 |
| `compose.s2` | 106,588 | 1.000 | 1.069 | 1.014 | 0.996 | 0.993 | 0.986 | 1.002 | 0.999 | 1.024 | 0.988 | 1.003 |
| `videoconf_full` | 141,923 | 1.000 | 1.057 | 1.004 | 0.993 | 0.985 | 0.968 | 1.007 | 1.011 | 1.020 | 0.980 | 1.002 |
| `string4x8.8` | 256,789 | 1.000 | 1.057 | 1.008 | 0.994 | 0.981 | 0.972 | 0.991 | 1.006 | 1.005 | 0.976 | 1.005 |
| `compose.s3` | 473,949 | 1.000 | 1.083 | 1.012 | 0.998 | 0.977 | 0.974 | 1.002 | 1.005 | 1.018 | 0.973 | 1.000 |
| **geomean** | | **1.000** | **1.058** | **1.011** | **0.996** | **0.989** | **0.982** | **0.999** | **1.006** | **1.017** | **0.983** | **1.001** |

(Below 1.000 is faster than the shipping default. `base` absolute times, for
scale: 0.365 s → 10.008 s.)

**The magnitudes are all inside the run-to-run spread, so the ordering is the
evidence, not the digits.** Within-cell spread over five repeats on this idle
host: **median 2.4%, p90 4.8%, worst 6.3%** — the sibling lane's ±20% warning
is about allocation-heavy criterion benches; this fixed-work driver is tighter,
but still wider than every effect in the table. What survives that is *rank*:

| cell | fastest on | slowest on | mean rank (1 = fastest of 11) |
|---|---:|---:|---:|
| `fatcgu1` | **5 of 7** | 0 | **1.57** |
| `v3fatcgu1` | 2 of 7 | 0 | **1.71** |
| `fat` | 0 | 0 | 3.29 |
| `thin` | 0 | 0 | 4.57 |
| `base` | 0 | 0 | 5.29 |
| `v2` | 0 | 0 | 5.57 |
| `native` | 0 | 0 | 6.57 |
| `v3` | 0 | 0 | 7.86 |
| `cgu1` | 0 | 0 | 8.86 |
| `v3cgu1` | 0 | 0 | 9.71 |
| `o2` | 0 | **7 of 7** | **11.00** |

Seven independent files agreeing on the order is a much stronger statement than
a 1.8% mean, and it is the form the result should be quoted in.

**Scorecard against §2's pre-registered predictions.**

- **E1 (`target-cpu=x86-64-v3` under 3% on the SAT core): right, and then
  some.** `v2` 0.999, `v3` 1.006, `native` 1.001 — not merely small but *not
  positive*, and `v3` ranks **consistently worse than baseline** (mean rank 7.86
  against 5.29). AVX2 makes this binary 6 KB larger and no faster; the plausible
  reading is vectorising code that has nothing to vectorise, paying setup and
  I-cache for it. `x86-64-v3` on top of the best cell (`v3fatcgu1` 0.983 vs
  `fatcgu1` 0.982) is likewise a wash.
- **E2 (`codegen-units = 1` the largest single-flag win): wrong, and backwards.**
  It was my top-ranked prediction and `cgu1` alone is **1.1% SLOWER** than the
  default, with a mean rank of 8.86 of 11 — worse than baseline on essentially
  every file. It only helps *combined with fat LTO*: `fat` 0.989 → `fatcgu1`
  0.982. So the reasoning (16 units lose intra-crate inlining across a
  6,280-line hot module) was not the mechanism. One unit also means one
  inlining and register-allocation budget over a much larger function set, and
  rustc's per-unit heuristics evidently tune better on the split.
- **E3 (`opt-level 2` vs `3` inside the noise floor): wrong.** `o2` is **5.8%
  slower and the slowest cell on 7 of 7 files** — the largest single effect in
  the entire matrix, and it is a *loss*. The most consequential build setting we
  have is the one we already take by default.
- **E6 (strongest cell worth 5–12%): wrong, too optimistic by 3x.** The
  strongest cell is worth **1.8%**, for **4.6x the build time**.

**Predicted ranking `cgu1 ≈ fat > thin > v3 > opt-level`; measured ranking
`fatcgu1 > fat > thin > base > v2 > native > v3 > cgu1 > v3cgu1 > o2`.** The
only part of the prediction that survives is that LTO helps and `target-cpu`
does not; the two cells I ranked highest (`cgu1`) and lowest (`opt-level`) are
respectively a small loss and by far the biggest term.

The `fat` > `cgu1` result is worth one more sentence, because it is where the
mechanism differs from the story: fat LTO's win here is **not** cross-crate
inlining in any interesting sense — `axeyum-cnf`'s propagate/analyze loop calls
nothing outside its own crate. It is that LTO re-optimises the whole crate graph
as one module *and keeps rustc's unit partitioning downstream of that*, which is
a different thing from forcing one unit up front. `cgu1` alone shows what
forcing one unit up front costs.
