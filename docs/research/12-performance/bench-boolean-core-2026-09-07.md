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
  throughput" is provisional until both run on one host — **which the next entry
  does, and it moves the answer.**
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
every 11-34. A restart truncates the trail; going ~15x longer between them means
descending far deeper before each conflict, and propagation work per conflict
scales with trail depth. That is a *schedule* — `Cdcl::should_restart`, Luby by
default with the Glucose EMA rule implemented and switched off — not a data
structure. The field comment on `use_ema_restart` records that the EMA schedule
was measured "neutral-to-slightly-negative" on this very corpus, which is
evidence against the simplest version of this explanation, and is why it is
written here as the leading candidate rather than as the answer. It is tested
below, and it does not survive.

### 2026-09-07 — same host, both engines: the throughput lead was a host artifact

Kissat 4.0.4 at commit `8af8e56` — the commit both prior studies pinned — rebuilt
on s5 from the in-tree `references/kissat` clone and run against the same eight
DIMACS files as the native core, same `taskset -c 0-7`, same idle host, 60 s
budget for Kissat and a 20,000-conflict budget for the native core. Load 0.56
before, 1.00 after.

The first attempt printed "kissat reported no conflicts" for all eight files: the
driver passed `-q` alongside `-s`, and `-q` suppresses the statistics block `-s`
exists to print. It is recorded because the driver's refusal to print a
comparison it had not parsed is the only reason it was noticed rather than
becoming eight rows of zeros.

| file | vars | nat p/c | kis p/c | **p/c n:k** | nat p/s | kis p/s (whole run) | kis p/s (search only) | **srch p/s n:k** | kis srch% | kis restart interval |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `mobiledevice_…twocond` | 31,482 | 735 | 827 | 0.89 | 18.3M | 14.0M | 28.4M | 0.64 | 49.4 | 11 |
| `string1x8.4` | 40,548 | 841 | 226 | 3.72 | 17.4M | 8.5M | 13.0M | 1.34 | 65.6 | 22 |
| `mobiledevice_…paired` | 58,380 | 966 | 1,039 | 0.93 | 15.6M | 12.3M | 25.8M | 0.60 | 47.6 | 12 |
| `compose.s2` | 106,588 | 1,828 | 1,311 | 1.39 | 13.4M | 11.3M | 23.7M | 0.57 | 47.9 | 18 |
| `videoconf_full` | 141,923 | 1,752 | 227 | 7.72 | 12.8M | 5.8M | 7.9M | 1.62 | 73.9 | 30 |
| `string4x8.8` | 256,789 | 2,436 | 338 | 7.21 | 11.5M | 6.1M | 8.8M | 1.30 | 68.7 | 34 |
| `compose.s3` | 473,949 | 4,272 | 847 | 5.04 | 8.8M | 6.2M | 10.9M | 0.80 | 56.7 | 20 |
| `string4x16.4` | 3,098,002 | 11,055 | 15,530 | 0.71 | 6.3M | 5.6M | 11.2M | 0.56 | 50.4 | 18 |
| **median** | | | | **2.56** | | | | **0.72** | | |

Both factors are now measured on one host, and the reading changes:

- **Propagation volume: we need a median 2.56x more propagation per conflict**,
  ranging from 0.71x (we are better) to 7.72x (much worse). Unambiguous, and
  larger than the throughput factor.
- **Propagation throughput: comparable, and probably slightly behind.** Against
  Kissat's whole-run rate we are ahead on every file (median 1.29x). Against its
  search-only rate — dividing its propagations by the fraction of wall time its
  own profiler attributes to `search` — we are at a median 0.72x, i.e. Kissat is
  ~1.4x faster per second of search. **The truth is between these two**, because
  the search-only correction attributes every Kissat propagation to search time
  while some propagation happens during probing (Kissat counts its probing
  sub-solver separately as `kitten_propagations`, but not every probing
  propagation is necessarily excluded from the main counter). So 0.72x is a lower
  bound on our relative rate and 1.29x an upper bound.

So the earlier entry's "we are ahead on throughput" was reading the uncorrected
figure on a different host, and it was too flattering. Corrected: **we are within
about 1.4x of Kissat on raw propagation rate, and behind by 2.56x on how much
propagation each conflict costs us.** The second factor is the larger one and the
only unambiguous one, which is the part of the earlier entry that survives.

Note the pattern in the table: the three files with the worst propagation-volume
ratio (7.72, 7.21, 3.72) are exactly the three where Kissat's `search%` is
highest (73.9, 68.7, 65.6) and its own propagations-per-conflict is lowest
(227, 338, 226). On those files Kissat reached 259k-1.5M conflicts; a solver deep
into a long run is working against a formula its inprocessing has already
reduced. That is a correlation, not a mechanism, and the next entries test the
mechanism.

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

### 2026-09-07 — the restart hypothesis, tested and refuted

The propagations-per-conflict entry above named the restart schedule as the
leading candidate: we restart every ~294 conflicts (Luby x `LUBY_UNIT = 100`),
Kissat every 11-34, and propagation work per conflict scales with trail depth.
The prediction is direct — **restart more often and propagations per conflict
should fall.**

Two arms, both against the same base build, same host, same eight files, same
20,000-conflict budget:

- **`ema`** — `use_ema_restart = true`, the Glucose EMA glue rule already
  implemented in this core and switched off by default.
- **`luby8`** — `LUBY_UNIT` 100 → 8, which lands the mean interval at 35
  conflicts, an 8.4x increase in restart frequency.

| file | base p/c | base c/s | ema p/c | ema c/s | luby8 p/c | luby8 c/s |
|---|---:|---:|---:|---:|---:|---:|
| `compose.s2` | 1,828 | 7,269 | 1,566 | 8,996 | 2,142 | 5,574 |
| `compose.s3` | 4,272 | 2,050 | 4,862 | 1,705 | 7,058 | 1,083 |
| `mobiledevice_…paired` | 966 | 16,013 | 1,091 | 14,333 | 967 | 16,164 |
| `mobiledevice_…twocond` | 735 | 24,572 | 822 | 21,168 | 1,023 | 17,714 |
| `string1x8.4` | 841 | 20,953 | 779 | 21,117 | 878 | 18,238 |
| `string4x16.4` | 11,055 | 571 | 13,920 | 449 | 9,481 | 648 |
| `string4x8.8` | 2,436 | 4,674 | 1,539 | 7,465 | 2,114 | 5,594 |
| `videoconf_full` | 1,752 | 7,293 | 1,697 | 6,707 | 1,810 | 6,397 |
| **median vs base** | — | — | **1.044** | **0.907** | **1.039** | **0.874** |

**Refuted.** Restarting 8.4x more often does not reduce propagations per
conflict — the median rises 3.9% — and conflicts per second falls 12.6%. The EMA
arm behaves the same way: 4.4% more propagation per conflict, 9.3% fewer
conflicts per second. Neither arm improves the factor it was aimed at on the
*median*, and both make throughput worse.

Two things worth keeping from a refuted hypothesis. First, this independently
reproduces what the `use_ema_restart` field comment already recorded from a
different lane's measurement ("neutral-to-slightly-negative on the public p4dfa
slice"), by a different method and on a different metric, which is a reason to
believe both. Second, the per-file spread is large and two-directional —
`string4x8.8` improves 37% in p/c and 60% in c/s under `ema`, `compose.s3`
degrades 47% in c/s under `luby8` — so a schedule that adapts per instance is not
excluded by this. What is excluded is "we restart too rarely, and that is why we
propagate more per conflict".

The candidate this leaves standing is **inprocessing**: Kissat's `probe` umbrella
(vivification, elimination, subsumption, congruence, sweeping) shrinks the
formula before and during search, so its propagation cascades run over a smaller
clause database. `axeyum-cnf` has `vivify`, `simplify` and `bve` as modules, and
`solve_with_drat_proof` runs **none of them**. That is the largest structural
difference remaining between the two engines, and this lane did not test it —
recorded as not run, not as ruled out. It is not the same claim the 2026-09-05
note refuted: that note refuted "Kissat wins because it *spends its time*
inprocessing" (its own profiler says the majority of its time is search). The
surviving claim is that inprocessing is *cheap and changes the formula*, which is
entirely compatible with search dominating Kissat's clock.

### 2026-09-07 — control: is the propagations-per-conflict gap an artifact?

The comparison above sets our first 20,000 conflicts against Kissat's whole run,
which reaches 25,597-1,501,192 conflicts. Early CDCL conflicts have deeper trails
because there are no learned clauses yet to cut them off, so **the gap could be
an artifact of comparing our early phase to their steady state.** The counters
make this cheap to check: run the same files at 5,000, 20,000, 80,000 and
320,000 conflicts and see whether propagations per conflict falls.

| file | 5k | 20k | 80k | 320k |
|---|---:|---:|---:|---:|
| `mobiledevice_…paired` | 1,126 | 966 | 960 | 960 |
| `compose.s2` | 1,692 | 1,828 | 1,818 | 1,818 |
| `string1x8.4` | 838 | 841 | 862 | 853 |
| `videoconf_full` | 2,187 | 1,752 | 1,522 | 1,717 |
| `string4x8.8` | 2,376 | 2,436 | 2,466 | 2,547 |

**Flat.** Over a 64x range of search depth, propagations per conflict moves by at
most ~20%, in both directions; on three of five files it is within 3%. The
artifact is not there, and the 2.5x median gap stands as measured. (Two files
reach their verdict before the larger budgets and simply repeat it.)

This control was run because the headline claim depended on it, and it is exactly
the kind of check that is easy to skip once a number already looks good.

### 2026-09-07 — the benches, and the fixture that had to be rejected twice

`benches/proof_pipeline.rs` and `benches/proof_sat_propagate.rs` landed. What
each proxies is in its module doc; two results are worth pulling out here.

**The evidence path is wildly asymmetric between its forward and backward
engines.** On the committed pigeonhole proof (757 DRAT steps):

| routine | time |
|---|---:|
| `check_drat` (forward) | 52.6 ms |
| `check_drat_backward` | **2.0 ms** — 26x faster |
| `elaborate_drat_to_lrat` (forward) | 82.4 ms |
| `elaborate_drat_to_lrat_backward` | **2.4 ms** — 35x faster |
| `write_drat` (text) | 100.6 µs |
| `write_drat_binary` | **6.5 µs** — 15x faster |
| `parse_drat_binary` | 60.3 µs |

The forward/backward gap is expected in kind — backward checking only re-derives
the clauses the refutation actually needs — but a factor of 26-35 is larger than
"expected in kind" prepares you for, and neither routine had a bench before, so
nobody could have said which. **This is a small fixture and the ratio will not
hold at corpus scale**; it is recorded as a starting point for someone measuring
the ADR-0613 certification path properly, not as a corpus number.

Binary DRAT is also **15x cheaper to write**, not merely smaller — which the
size-focused framing of the format ("~3x smaller") does not mention, and which is
the larger of the two effects for a solver emitting a proof during search.

**The fixture-shape assertion earned its place by firing twice.** The proxy bench
asserts its own shape against the p4dfa figures rather than describing it, and it
rejected two fixtures before accepting one:

1. A single 20-bit multiplier — the natural first choice, and the shape the
   existing `tseitin_encode` bench uses. It encodes to **770 variables**: a
   pigeonhole-class instance wearing a bit-blasted costume. Without the
   assertion this file would have shipped with a module doc claiming "tens of
   thousands of Tseitin variables" over a fixture with 770.
2. A sum-of-products with an odd target, unsatisfiable by a parity argument. The
   reasoning was that CDCL would have to rediscover the parity through a
   bit-blasted multiplier and would run to the budget. It is decided in **2
   conflicts**: the low bit of a bit-blasted sum is a pure XOR chain and unit
   propagation collapses it immediately. Reading the code would not have revealed
   that; the assertion did, in one run.

The accepted fixture is six independent bounded-factor multiplications (32-bit
factors, 64-bit products, six 64-bit semiprimes): 23,997 variables, 100,221
clauses, exhausts its 2,000-conflict budget on every sample, 84 ms per sample.

**And it fails to match the corpus on one axis, which is itself a finding.** It
does **128 resolutions per conflict** against the corpus's 23-39 — factorisation
learns from far longer resolution chains than a p4dfa instance does. So this
bench over-weights `analyze` and `lit_redundant` and under-weights `propagate`
relative to the real workload: a conflict-analysis optimisation will look better
here than on the corpus, and a propagation optimisation worse. That is written
into the module doc next to the table, because a proxy whose mismatch is
documented is usable and one whose mismatch is unknown is not.

## 4. Where §1 was wrong, in one place

| | pre-registered | measured |
|---|---|---|
| H1 `analyze`'s per-conflict `vec![false; nvars]` | ranked **#1** | **1.6%** median, 3.8% best case |
| H2 per-resolution-step `to_vec()` | ranked #2 | not measured (see below) |
| H3 16-byte `Watch` | ranked #3 | not measured |
| H4 `Vec<Vec<Watch>>` pointer chase | ranked #4 | not measured |
| H5 `compute_lbd` allocation | ranked #5 | not measured |
| H6 DRAT logging 5-15% | — | **< 1%** |
| restart schedule (not in §1 at all) | — | tested, **refuted** |
| **propagations per conflict** (not in §1 at all) | — | **the actual deficit: 2.5x median, up to 7.7x** |

The ranking was wrong at the top (H1), wrong at the bottom (H6, by an order of
magnitude), and — the part that matters — **aimed at the wrong factor
entirely**. Every one of H1-H5 is a hypothesis about the cost of a unit of
propagation work. The measured deficit is in the *amount* of propagation work,
which none of them touches. H2-H5 were left unmeasured deliberately once that was
clear: they are optimisations to the factor we are already roughly competitive
on, and measuring them would have spent the lane's remaining time on the wrong
axis.

The general shape of the error is worth naming, because it is cheap to repeat:
**reading a hot function tells you what it costs, and says nothing about how
often the search chooses to call it.** Every hypothesis in §1 came from reading
`propagate` and `analyze`. The answer came from a counter that neither function
contains.

## 5. What this lane did not measure

- **Inprocessing** — the surviving candidate for the propagation-volume gap, and
  the largest structural difference between the two engines
  (`solve_with_drat_proof` runs none of `vivify`, `simplify` or `bve`). Not run.
- **H2-H5**, for the reason above. Not run, not ruled out; each would move a
  factor that is currently not the deficit.
- **CaDiCaL.** Only Kissat was rebuilt on the measurement host. Not run.
- **Certificate cost at corpus scale.** DRAT *logging* overhead is measured on
  real p4dfa CNF; DRAT *checking* and LRAT *elaboration* are measured only on the
  757-step pigeonhole proof, where the clause database RUP runs against is 133
  clauses. The corpus-scale certification cost is not measured, and the bench
  numbers must not be extrapolated to it.
- **Memory.** Every number here is time. The `vec` sink holds its proof in RAM
  and that has OOM-killed a run before (27.6 GiB); nothing here measures it.
- **Repeats.** The A/B took 3 interleaved repeats and reports minima; the
  restart, budget-scaling and Kissat runs are single runs per cell. Load average
  was recorded before and after every timing run and never exceeded 2.4 on an
  idle 16-core host, but there are no variance bars.

## 6. Reproducing any of this

Every measurement above comes from two committed things plus a host:

```sh
# the per-conflict decomposition and the DRAT-sink arms, on one DIMACS file
cargo run --release -p axeyum-cnf --example boolean_core_profile -- \
    <file.cnf> <max_conflicts> [null|vec|text|binary]

# the two benches
cargo bench -p axeyum-cnf --bench proof_pipeline
cargo bench -p axeyum-cnf --bench proof_sat_propagate
```

The p4dfa DIMACS were produced with the unmodified
`crates/axeyum-bench/examples/dump_dimacs.rs` — the same tool gate (b) and the
2026-09-05 search-statistics note used — from
`/nas3/data/axeyum/corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen`.
Kissat is 4.0.4 at commit `8af8e56`, the commit both prior studies pinned,
rebuilt on the measurement host. The A/B and experiment drivers were session
scratch scripts: they only shell out to already-built binaries and do no SAT work
of their own, so they are not committed, and every number they produced is
reproducible from the two commands above.
