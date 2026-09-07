# Boolean core: benchmarks, the per-conflict throughput gap, and the cost of a certificate

Lane `bench-boolean-core`, running diary. Started 2026-09-07.

This file is written **as the work happens**, including the entries where the
expectation recorded before a measurement turned out to be wrong. Entries are
appended, never rewritten: a corrected prediction stays visible next to its
correction.

## 0. The question, and what was already known

Three prior artifacts define the starting point, and none of them is repeated
here:

- [`bench-results/sat-core-gate-b-20260905/`](../../../bench-results/sat-core-gate-b-20260905/README.md)
  — on the 113-file p4dfa slice at a 20 s budget the decided counts are
  **Kissat 11, CaDiCaL 10, native proof core 6, BatSat 4**. Its own "what this
  does not establish" says, verbatim: *"No profiling was done."*
- [`2026-09-05-native-core-vs-kissat-search-stats.md`](../11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md)
  — on the 8 non-outlier files all three engines decide, the native core needs
  a median **1.38x more conflicts** than Kissat and processes them at a median
  **0.637x** Kissat's rate, i.e. Kissat does roughly **1.57x more conflicts per
  second**. It also refuted the strong "it is all inprocessing" guess: Kissat's
  own profiler attributes 45.5-100% (mean 58.7%) of its wall time to core
  search on every file measured.
- The same note's closing limitation is this lane's entry point:

  > **The native core's own time breakdown is not measured at all** — no
  > decision counter, no propagation counter, no restart counter exists in
  > `ProofSearchProgress` to compare against Kissat's `search%`/`probe%` split
  > on the native side. […] Adding that instrumentation is a production change
  > to `axeyum-cnf` (`ProofSearchProgress`), explicitly out of scope for that
  > measurement lane — **a natural next step for a lane that owns that crate.**

So the gap is measured and its *magnitude* is not in question. What is missing
is a cause named at the level of a function and a data-structure choice.

`perf` is not available on this fleet, so the method is counters plus targeted
A/B, not a flamegraph.

## 1. Pre-registered expectations (written before any measurement)

Recorded here so that being wrong is visible later. These came from reading
`proof_sat.rs` only — no measurement yet, and reading is exactly the evidence
class this repository warns is weakest.

**H1 — `analyze` allocates and zeroes an O(#variables) array on every
conflict.** `Cdcl::analyze` opens with

```rust
let mut seen = vec![false; self.assign.len()];
```

That is one heap allocation plus one `memset` of `nvars` bytes **per
conflict**, regardless of how few variables the conflict actually touches.
MiniSat, BatSat, CaDiCaL and Kissat all keep a persistent mark array and clear
only the entries they touched. On a p4dfa instance with ~10^5-10^6 variables
this is 100 KB-1 MB of memset per conflict, and it also evicts the working set
the same conflict is about to read. Predicted to be the single largest
contributor to the per-conflict gap on large instances, and — critically —
**invisible on a small instance**, because on PHP(7,6) with 42 variables it is
42 bytes.

**H2 — `analyze` heap-allocates once per resolution step.** Inside the
resolution loop:

```rust
let lits = self.lits(clause_id).to_vec();
```

a fresh `Vec` per antecedent clause walked, purely to satisfy the borrow
checker while `bump_var` mutates `self.activity`. Predicted second largest.

**H3 — `Watch` is 16 bytes where the reference solvers use 8.**
`Watch { clause: CRef /* usize */, blocker: CnfLit }`. `CRef` is `usize` = 8
bytes; with `CnfLit` at 4 bytes and alignment 8 the struct is 16. CaDiCaL and
Kissat use a 32-bit clause reference and a 32-bit blocker, 8 bytes total.
Watch-list traversal is the single hottest memory stream in a CDCL solver, so a
2x inflation of it costs directly. Predicted third.

**H4 — `watches: Vec<Vec<Watch>>` is a pointer chase per literal.** Each
literal's watch list is a separately heap-allocated `Vec`, so visiting a
literal's watchers costs a dependent load before any watcher is read, and the
lists are scattered across the allocator's arena rather than laid out together.
Kissat uses one flat watch arena. Predicted real but smaller than H1-H3, and
much harder to fix.

**H5 — `compute_lbd` allocates a `Vec` per learned clause** and sorts it.
Predicted small (learned clauses are short) but free to fix.

**Ranking predicted before measuring: H1 > H2 > H3 > H4 > H5.**

**H6 — DRAT logging overhead.** Predicted 5-15% of search wall time for the
in-memory `Vec<DratStep>` sink. Prediction recorded because no authoritative
published figure exists for DRAT logging overhead in CaDiCaL or Kissat, so ours
is worth publishing whatever it is.

## 2. The methodological trap this lane was warned about, restated

Measured in this repository on 2026-09-06: `cdclt_solve_php_6_7` (42 variables)
said engine A beat engine B by 3.4%, while on a 330,000-variable real skeleton
the same swap decided 4 **more** files at 12.9% better PAR-2 — opposite
directions.

H1 above predicts *exactly* that failure mode for this lane's own headline
bench: `proof_sat_solve_php_6_7` has 42 variables, so the O(#vars) memset it
would need to expose is 42 bytes and it will show approximately nothing. **If
H1 is right, the existing committed micro-benchmark is structurally incapable
of detecting the largest defect in the file it benchmarks.** That prediction is
recorded here before the measurement so that it counts either way.

Consequence for the benches this lane adds: every one states the real workload
it proxies, and the headline ones are validated against real corpus DIMACS
(p4dfa) rather than against pigeonhole.

## 3. Log

*(appended as the work happens)*

### 2026-09-07 — lane opened

Read `proof_sat.rs` (6,280 lines), the gate-b artifact, and the three prior
design-review measurement notes. Wrote §1's expectations before touching a
build. Nothing measured yet.

### 2026-09-07 — H1's size-scaling prediction fails on data that already existed

Before building anything, H1 was given a cheap falsification test on committed
data. If `analyze`'s per-conflict mark array — the one per-conflict cost
proportional to the *formula* rather than to the *conflict* — were a dominant
term that Kissat does not pay, then the native:Kissat conflicts-per-second ratio
should **fall as the instance gets bigger**. The 2026-09-05 study population
spans 4,120 to 3,098,002 variables, a 750x range, so the test has room.

Re-analysing `comparison-table.md` over the 17 files where both engines
exceeded 1,000 conflicts (below that a "rate" is startup, not throughput):

```
log10(native c/s : kissat c/s) vs log10(variables):  slope = -0.048, r = -0.119
```

Flat. Over a 750x size range the ratio moves by about 20%, in noise. **The
prediction that follows most directly from H1 is not visible in the data.**

That does not refute H1 as a *cost* — both engines' absolute rates fall steeply
with size (45,877 c/s at 4,120 variables down to 492 c/s at 3,098,002), so
size-dependent costs clearly dominate *both* engines and a shared one could mask
ours. It does refute the strong form: whatever separates us from Kissat is not
predominantly a term we pay per variable and they do not. Recorded here because
the ranking in §1 put H1 first and this is the first evidence against it.

Caveats on this re-analysis, since it is reused data and not a new experiment:
single run per file, the two engines follow different trajectories on the same
file, and four of the 17 files are `unknown` for one engine (a rate over an
unfinished search is still a rate, but not over the same search).

### 2026-09-07 — the instrumentation, and the first real decomposition

`SearchCounters` + `solve_with_drat_proof_counted` landed (`7fd80725f`),
closing the gap the 2026-09-05 note named. `examples/boolean_core_profile.rs`
drives it over real p4dfa DIMACS at a **fixed conflict budget**, so every arm
analyses the same conflicts along the same trajectory.

Eight p4dfa instances were dumped on s5 with the unmodified
`crates/axeyum-bench/examples/dump_dimacs.rs` (the same tool gate (b) and the
search-statistics note used), spanning 31,482 to 3,098,002 variables. s5: idle
16-core host, `taskset -c 0-7`, load 1.34 before / 1.12 after — i.e. the run
itself was the only load.

At a 20,000-conflict budget:

| file | vars | s | conf/s | props/conf | watch visits/conf | deref rate | resolutions/conf | mark bytes/conf |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `mobiledevice_…twocond` | 31,482 | 0.35 | 24,475 | 735 | 2,215 | 0.507 | 26.5 | 31,482 |
| `string1x8.4` | 40,548 | 0.97 | 20,581 | 841 | 2,549 | 0.477 | 37.6 | 40,548 |
| `mobiledevice_…paired` | 58,380 | 1.26 | 15,920 | 966 | 2,980 | 0.489 | 22.6 | 58,380 |
| `compose.s2` | 106,588 | 2.73 | 7,333 | 1,828 | 5,347 | 0.484 | 25.7 | 106,588 |
| `videoconf_full` | 141,923 | 2.75 | 7,275 | 1,752 | 4,939 | 0.511 | 37.3 | 141,923 |
| `string4x8.8` | 256,789 | 4.22 | 4,738 | 2,436 | 6,720 | 0.516 | 39.4 | 256,789 |
| `compose.s3` | 473,949 | 9.76 | 2,049 | 4,272 | 11,615 | 0.523 | 30.2 | 473,949 |
| `string4x16.4` | 3,098,002 | 35.09 | 570 | 11,055 | 29,275 | 0.473 | 32.4 | 3,098,002 |

Three things fall straight out of this table.

**(a) Conflicts per second is almost exactly propagations per second divided by
propagations per conflict, and the second factor is the one that moves.**
Across the eight files, propagations per conflict rises 15x (735 → 11,055) while
resolutions per conflict — the size of the conflict analysis itself — stays flat
at 22-39. So a conflict on a big p4dfa instance is not a bigger *conflict*; it
is the same size conflict reached after 15x more propagation.

**(b) The blocking literal misses about half the time**, 0.473-0.523 across
every file, remarkably stable. Half of all watch visits dereference the clause
array. That is the number H3/H4 were guesses about, and it is now measured
rather than assumed.

**(c) `analyze` zeroes 9.5 GB on `compose.s3` and 62 GB on `string4x16.4`**
over a single 20,000-conflict budget — 971 MB/s and 1.77 GB/s of pure mark-array
traffic respectively. Large in absolute terms, and exactly the quantity §1's H1
named. Whether it *costs* what it looks like it costs is a question a byte count
cannot answer; the A/B below is what answers it.

### 2026-09-07 — the premise of this lane is wrong in an interesting way

The brief this lane was given says our core "processes conflicts roughly 1.5x
slower" than Kissat. Setting the new counters against Kissat's own `-s`
statistics from the 2026-09-05 run, on the two files where both exist:

**`compose.s3`** (473,949 variables)

| | native | Kissat 4.0.4 |
|---|---:|---:|
| conflicts/second | 2,049 | 6,934 |
| **propagations per conflict** | **4,272** | **872** |
| **propagations per second** | **8,754,000** | **6,049,000** |
| decisions per conflict | 5.3 | 7.5 |
| conflicts between restarts | 294 | 19 |
| conflicts between reductions | 1,818 | 5,710 |

**`compose.s2`** (106,588 variables)

| | native | Kissat 4.0.4 |
|---|---:|---:|
| conflicts/second | 7,333 | 8,275 |
| **propagations per conflict** | **1,828** | **1,311** |
| **propagations per second** | **13,406,000** | **10,848,000** |
| conflicts between restarts | 294 | 18 |

The identity is exact on both sides —
`conflicts/s = propagations/s ÷ propagations/conflict`, which is arithmetic, not
a model — and it splits the gap into two factors that point in **opposite
directions**:

- **Propagation throughput: we are ahead.** 8.75M vs 6.05M propagations/second
  on `compose.s3`, 13.4M vs 10.8M on `compose.s2`. The watch scheme, the
  blocking literals, the flat clause arena and the packed one-word `Reason` are
  doing their job. Whatever is wrong, it is not that our BCP inner loop is slow.
- **Propagation volume: we are behind, by a lot.** 4,272 propagations per
  conflict against Kissat's 872 — **4.9x** — on `compose.s3`, and 1.4x on
  `compose.s2`. Every conflict costs us five times the propagation work to
  reach.

So "we process conflicts 1.5x slower" is true as an *outcome* and misleading as
a *diagnosis*. We do not process a conflict slowly. We walk five times as far to
find one.

**This is where §1's ranking was wrong.** H1-H5 are all hypotheses about the
cost of a unit of work — allocations, struct widths, pointer chases. Every one of
them, if fixed perfectly, moves the *first* factor, the one we already lead on.
None of them touches the second factor, which is where the deficit is.

Two caveats that this comparison must carry, and one correction:

- **Different hosts.** The native numbers are s5, the Kissat numbers are s7
  (from the 2026-09-05 run). Propagations *per conflict* is host-independent, so
  the 4.9x is safe. Propagations *per second* is not, so "we are ahead on
  throughput" is provisional until both run on one host — queued below.
- **Kissat's rate is over its whole wall time**, and its own profiler puts
  48-74% of that in `search` on these files (`compose.s3`: 56.8% search, 29.5%
  probe). Correcting to search-only, Kissat's `compose.s3` propagation rate is
  ~10.6M/s, which is *above* our 8.75M/s, not below. So the honest reading of
  the throughput factor is **"comparable, ours possibly slightly behind after
  correction"**, not "ours is ahead" — and the propagation-volume factor is
  correspondingly the larger part of a gap that is smaller than the raw figures
  suggest. Recorded this way round because the uncorrected version was written
  first and was too flattering.
- The native runs are budget-capped at 20,000 conflicts, Kissat's are 60 s
  runs reaching 25,597-416,842 conflicts. Rates from different phases of a
  search are not perfectly comparable; the native core's early conflicts are
  cheaper than its late ones.

**Where the propagation volume comes from is the open question**, and the
restart column is the loudest candidate: we restart every 294 conflicts, Kissat
every 18-19. A restart truncates the trail; going 15x longer between them means
descending far deeper before each conflict, and propagation work per conflict
scales with trail depth. That is a *schedule* — `Cdcl::should_restart`, Luby by
default with the Glucose EMA rule implemented and switched off — not a data
structure. The field comment on `use_ema_restart` records that the EMA schedule
was measured "neutral-to-slightly-negative" on this very corpus, which is
evidence against the simplest version of this explanation, and is why it is
written here as the leading candidate rather than as the answer.

### 2026-09-07 — H1 measured directly: 1.6%. It was ranked first.

The byte counts above do not settle whether the mark array *costs* what it
looks like it costs, so it was A/B'd directly. The arm replaces `analyze`'s
`vec![false; self.assign.len()]` with a persistent buffer cleared only at the
positions the conflict touched — the MiniSat/BatSat/CaDiCaL/Kissat arrangement.
Both `analyze`'s own marks and the ones `lit_redundant` sets are recorded, since
a failed redundancy probe rolls back its own marks and the caller therefore
cannot rely on `to_clear`.

Two builds, one host, `taskset -c 0-7`, arms interleaved, 3 repeats, minimum of
each taken, fixed 20,000-conflict budget. s5 load 1.01 before / 1.07 after —
the run was the only load. The driver refuses to print a ratio if the arms'
trajectories differ, and prints which counter diverged.

| file | vars | base (s) | arm (s) | arm/base |
|---|---:|---:|---:|---:|
| `mobiledevice_…twocond` | 31,482 | 0.352 | 0.347 | 0.988 |
| `string1x8.4` | 40,548 | 0.952 | 0.953 | 1.000 |
| `mobiledevice_…paired` | 58,380 | 1.249 | 1.231 | 0.986 |
| `compose.s2` | 106,588 | 2.726 | 2.683 | 0.984 |
| `videoconf_full` | 141,923 | 2.737 | 2.694 | 0.984 |
| `string4x8.8` | 256,789 | 4.263 | 4.131 | 0.969 |
| `compose.s3` | 473,949 | 9.717 | 9.520 | 0.980 |
| `string4x16.4` | 3,098,002 | 35.083 | 33.736 | 0.962 |

**Trajectories identical on all 8 files** — same verdict, conflicts, decisions,
propagations, restarts, reductions, watch visits, clause visits, watch
relocations, resolutions, redundancy steps, and the same DRAT byte count. So
this is a like-for-like throughput comparison and not two different searches.

**Median 1.6% faster. Best case 3.8%, on the 3.1-million-variable file. Zero on
the 40,548-variable one.** The size trend predicted by H1 is real and visible —
the effect grows monotonically with variable count, which is what a per-variable
cost must do — and it is *small*. 62 GB of mark-array traffic on
`string4x16.4` buys back 1.35 seconds out of 35.

Why so much traffic for so little time: `vec![false; n]` compiles to
`alloc_zeroed`, and for a multi-megabyte allocation repeated at the same size the
allocator hands back memory the kernel has already zeroed or that is still warm,
so the "62 GB of memset" is mostly not memset at all. The byte count was a
correct measurement of a quantity that turned out not to be the cost. This is
the reason the A/B exists and the reason §1's byte-count reasoning was not
allowed to stand on its own.

**Scorecard against §1's pre-registered ranking, so far:** H1 was ranked #1 and
is worth 1.6%. H6 predicted 5-15% and the true figure is under 1%. The ranking
was wrong at both ends, and — more importantly — the whole H1-H5 family turns
out to be aimed at the factor we are not behind on (see the propagations-per-
conflict entry above).

### 2026-09-07 — the certificate is nearly free

DRAT logging overhead, four sink arms on the same fixed 20,000-conflict budget,
two interleaved repeats each, s5 idle. The `null` arm still makes **every** sink
call the core makes; only the body is empty. So the differences below isolate
the cost of *recording* a certificate from the cost of *deciding to emit* one,
which no published CaDiCaL or Kissat figure separates.

| file | null | vec | text | binary |
|---|---:|---:|---:|---:|
| `mobiledevice_…paired` | 1.237 / 1.241 | 1.240 / 1.262 | 1.250 / 1.253 | 1.249 / 1.242 |
| `compose.s2` | 2.757 / 2.723 | 2.732 / 2.764 | 2.746 / 2.752 | 2.732 / 2.734 |
| `videoconf_full` | 2.738 / 2.726 | 2.730 / 2.727 | 2.748 / 2.748 | 2.713 / 2.715 |
| `string4x8.8` | 4.224 / 4.216 | 4.242 / 4.252 | 4.259 / 4.240 | 4.264 / 4.214 |

Taking the minimum of each pair against the `null` minimum:

| sink | overhead vs no recording |
|---|---:|
| `vec` (in-RAM `Vec<DratStep>`, the shipping default) | **+0.2%** |
| `text` (standard DRAT text, formatted) | **+0.7%** |
| `binary` (binary DRAT) | **+0.0%** |

Every one of these is inside the run-to-run spread of the `null` arm itself
(±1.4% on `mobiledevice`), so the honest statement is **"DRAT logging costs less
than 1% of search time on this corpus, and the measurement cannot resolve it
more finely than that."** H6 predicted 5-15%; H6 was wrong by an order of
magnitude.

The reason is visible in the counters and is not a property of DRAT: at a
20,000-conflict budget the core emits ~36,000 steps carrying ~620,000-860,000
literals, i.e. **1.8 steps and ~40 literals per conflict**, against 735-11,055
*propagations* per conflict. Recording the proof is three orders of magnitude
less work than finding it. This should generalise to any CDCL solver whose
learned clauses are short relative to its propagation volume, which is all of
them.

**What this does not say:** it says nothing about the cost of *checking* the
proof, of *elaborating* it to LRAT, or of *writing it to disk* (the `text` and
`binary` arms count bytes into a discard writer, so no I/O is in these numbers —
deliberately, since disk speed is not a property of the solver). It also says
nothing about memory: the `vec` arm's proof is held in RAM, and the streaming
sink exists precisely because a 27.6 GiB in-RAM proof once OOM-killed a run.

**Binary DRAT is 2.3x smaller, not ~3x.** Measured on the same four files:
3,568,995 → 1,541,173 bytes (2.32x), 3,695,185 → 1,624,847 (2.27x), 4,387,732 →
1,894,704 (2.32x), 5,170,384 → 2,129,223 (2.43x). Consistently 2.3x, never 3x.
The ratio is a property of the *literal magnitudes* — a variable index below 128
costs one byte in the binary encoding and up to seven characters in the text one,
so the advertised 3x assumes smaller variable indices than a bit-blasted corpus
instance has.
