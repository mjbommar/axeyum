# Inprocessing: where the cost actually goes, and when it pays

**Date:** 2026-09-08 · **Host:** s4 (12th Gen Intel i5-12600K, 6 P-cores /
4 E-cores, 16 threads, 123 GB) · **Tree:** `cbb178c55` plus this lane's
instrumentation · **Corpus:** the pinned `bench-results/parity-lists/QF_BV.txt`
(200 files, sha256 `6f873e15b191`)

This re-measures a claim I was handed rather than inheriting it: *"the benefit
of inprocessing only appears at ~5x the 24-second competition budget"*, i.e. a
break-even near 120 s. It does not reproduce. It also decomposes the cost,
which is the part that changes what to do next.

**Read this first, because it reframes everything below.** "Inprocessing costs
too much" is not one phenomenon. It is two, with different fixes, and the
aggregate ratio that was handed to me averaged them together:

* On **179 of 195 files** the passes run to their own fixpoint and cost a median
  of **28 ms**. That is not a cost problem at all.
* On **16 files (8%)** bounded variable elimination spends its **entire granted
  slice** — 11.9 s of a 12.0 s budget — and is then cut off unfinished. Those 16
  files account for **189 s of the 342 s total inprocessing spend across the
  whole corpus**, and five of them are decided by the baseline in under 120 ms.

The single largest lever is not a faster BVE. It is not spending half a query's
budget on a pass that will not finish, on a query the search decides in 90 ms.

---

## 1. What was already known, and what this adds

[ADR-1750][adr] already measured the per-pass decomposition, and this lane does
not repeat it. Its numbers, for reference:

| ADR-1750 finding | value |
|---|---|
| break-even for BVE | **59k–131k conflicts**, median ~92k, flat across a 100x size range |
| propagations/conflict vs `off` | subsume 0.933, **BVE 0.426**, preprocess 0.388 |
| conflicts/second vs `off` | subsume 1.051, **BVE 1.875** |
| BVE `DRAT` prefix vs subsumption's | 37.7 M steps vs 92 k on a 3.1 M-variable instance |
| backward vs forward proof checking | 231x faster backward |

That measurement was taken on **eight `p4dfa` instances**, at a **fixed
20,000-conflict budget**, on host **s5**. Its break-even is denominated in
**conflicts**, which is the right unit: it does not move with host load.

This lane adds four things ADR-1750 does not have.

1. **A different corpus and the shipping front door.** ADR-1750 measured the SAT
   core on raw DIMACS. This measures `solve_smtlib` end to end over the pinned
   parity list — the path a competition run takes.
2. **Stage attribution inside inprocessing**, including whether a pass was cut
   off by the clock. `inprocess_ms` alone attributes everything to
   "inprocessing", which is the same error as attributing a solve to the last
   route that ran.
3. **Setup versus work.** Each pass is run a second time on its own output; the
   second run rebuilds the same occurrence lists and finds nothing, so its time
   is the cost the pass pays whether or not it finds anything.
4. **The wall-clock conversion**, which is what a 24 s budget is actually
   denominated in.

[adr]: ../09-decisions/adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md

---

## 2. Protocol

Everything below is a `--release` build. Arms of one comparison run
**concurrently, each pinned to its own physical P-core** (CPUs 0, 2, 4 — SMT
siblings 1, 3, 5 left idle), so all arms saw the same host at the same moment.
Pinning is not cosmetic here: CPUs 12–15 are E-cores and the same binary is
measured 1.84x slower on one, so an unpinned arm reports the scheduler's core
choice as its own performance.

```sh
# 0. Build. `cargo-serialized.sh` holds the host-wide lock; the MEASUREMENTS
#    then run the prebuilt binary directly, never through the wrapper (it takes
#    a flock, so a timed run through it measures the queue).
scripts/cargo-serialized.sh build --release -p axeyum-bench \
    --example inprocess_ab --example dump_dimacs
scripts/cargo-serialized.sh build --release -p axeyum-cnf \
    --example inprocess_pass_cost --example inprocess_profile

# 1. End-to-end, three arms, 24 s / 8 GiB (the parity protocol's limits).
SWEEP_CPUS=0 scripts/inprocess-cost-sweep.sh bench-results/parity-lists/QF_BV.txt \
    24000 off           bench-results/inprocess-cost-2026-09-08/qfbv-24s-off.jsonl &
SWEEP_CPUS=2 scripts/inprocess-cost-sweep.sh bench-results/parity-lists/QF_BV.txt \
    24000 inproc        bench-results/inprocess-cost-2026-09-08/qfbv-24s-inproc.jsonl &
SWEEP_CPUS=4 scripts/inprocess-cost-sweep.sh bench-results/parity-lists/QF_BV.txt \
    24000 inproc-vivify bench-results/inprocess-cost-2026-09-08/qfbv-24s-vivify.jsonl &
wait

# 2. The same at 120 s, to test the handed-down claim directly.
SWEEP_CPUS=0 scripts/inprocess-cost-sweep.sh bench-results/parity-lists/QF_BV.txt \
    120000 off    bench-results/inprocess-cost-2026-09-08/qfbv-120s-off.jsonl &
SWEEP_CPUS=2 scripts/inprocess-cost-sweep.sh bench-results/parity-lists/QF_BV.txt \
    120000 inproc bench-results/inprocess-cost-2026-09-08/qfbv-120s-inproc.jsonl &
wait

# 3. Per-pass, at the CNF level, over the encoding-verified subset.
scripts/inprocess-cost-dump-cnf.sh \
    bench-results/inprocess-cost-2026-09-08/cnf-population-candidates.txt <dir>
SWEEP_CPUS=6 scripts/inprocess-pass-sweep.sh \
    bench-results/inprocess-cost-2026-09-08/cnf-verified-paths.txt conflicts 20000 \
    bench-results/inprocess-cost-2026-09-08/pass-conflicts-20k.jsonl &
SWEEP_CPUS=8 scripts/inprocess-pass-sweep.sh \
    bench-results/inprocess-cost-2026-09-08/cnf-verified-paths.txt wall 24000 \
    bench-results/inprocess-cost-2026-09-08/pass-wall-24s.jsonl &
wait

# 4. The report.
python3 scripts/inprocess-cost-report.py \
    bench-results/inprocess-cost-2026-09-08/qfbv-24s-{off,inproc,inproc-vivify}.jsonl
```

The three arms are the ones `SolverConfig` can actually ship: `off`,
`cnf_inprocessing` (= subsumption + BVE), and that plus `cnf_vivify`. There is
deliberately **no "BVE only" end-to-end arm**, because `SolverConfig` has no
per-pass toggle and inventing one would measure a configuration the solver
cannot ship. Per-pass isolation is done at the CNF level, where
`InprocessOptions` has the fields.

### Load

| sweep | load before | load after |
|---|---|---|
| 24 s, all three arms | 2.17–2.27 | 1.56–5.77 |

Three pinned single-threaded arms on a 16-thread box. The comparison is
within-run and back-to-back, which is what the arms-concurrent design buys; the
absolute seconds are not comparable to a differently-loaded run elsewhere.

### The verdicts were checked before any timing was read

| arm | decided | agreed with declared `:status` | **disagreed** | no declared status |
|---|---:|---:|---:|---:|
| off | 186 | 171 | **0** | 15 |
| inproc | 188 | 173 | **0** | 15 |
| inproc-vivify | 188 | 173 | **0** | 15 |

Cross-arm verdict conflicts: **0**. So nothing below is a timing over answers
nobody checked. See §7 for what this does and does not establish about the
`sat` reconstruction path.

---

## 3. The break-even is between 12 s and 24 s, not at 120 s

Solved count against budget. Columns at or below 24 s are derived by
thresholding each file's recorded wall time from the 24 s run.

| arm | 1 s | 3 s | 6 s | 12 s | **24 s** |
|---|---:|---:|---:|---:|---:|
| off | 158 | 172 | 177 | **184** | 186 |
| inproc | 124 | 144 | 156 | 172 | **188** |
| inproc-vivify | 133 | 152 | 161 | 176 | **188** |

**The crossover is between 12 s and 24 s.** At 12 s inprocessing is 12 files
behind; at 24 s it is 2 ahead. The handed-down "~5x the 24-second budget"
break-even is not what this corpus shows: on the shipped path, at the
competition budget, inprocessing is already slightly ahead on decided count.

Two corrections that make the headline smaller and more honest:

* **One of the two "gained" files is a harness flake, not a solver difference.**
  `sage/app12/bench_3388.smt2` is a 575-byte query with a 13-variable CNF; the
  `off` arm's row records `killed`, and re-running that exact file on the same
  binary decides `unsat` in 0 ms. The real gain at 24 s is **one file**
  (`simple_processors_008_006_0004`), not two. The flaked row is left in the
  committed data as measured — a sweep whose rows are edited afterwards is not
  evidence.
* **Decided count is not the only score, and PAR-2 disagrees with it.**

| arm | decided | total wall | PAR-2 (24 s budget) |
|---|---:|---:|---:|
| off | 186 | 463.3 s | **817.5** |
| inproc | 188 | 746.2 s | 1027.8 |
| inproc-vivify | 188 | 679.6 s | 960.7 |

So: inprocessing decides one more file and costs 283 s more wall time to do it.
Which of those matters is a scheduling decision, not a measurement — but a
report that quoted only the decided count would be choosing the flattering one.

### The derived columns are licensed, but only just

Thresholding a 24 s run to read off a 6 s result assumes behaviour does not
depend on the budget given. **It does**: inprocessing is granted half the
remaining solve budget, so a 6 s budget is a 3 s slice. The truncation counters
say how far that assumption is stretched — 16 files already exhaust the 12 s
slice at a 24 s budget, so at 6 s the derived column is optimistic for the `on`
arms on at least those files, and they are a floor, not an estimate. The 6 s
columns are therefore reported as **derived**, and the honest reading is
directional (inprocessing loses badly below ~12 s) rather than exact.

---

## 4. Where the cost goes: it is BVE, and it is inside the pass

Summed over the 195 files that ran inprocessing, in milliseconds:

| arm | xor_propagate | subsume | vivify | **bve** | compact | Σ stages | `inprocess_ms` | residual |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| inproc | 107 | 60,213 | — | **278,050** | 2,295 | 340,665 | 342,024 | **1,359** |
| inproc-vivify | 108 | 59,019 | 2,522 | **209,666** | 2,169 | 273,485 | 274,454 | **969** |

Two answers here.

**Which pass dominates: BVE, at 81% of the total.** Subsumption is 18%, and
everything else is under 1%.

**The cost is in the pass, not in rebuilding the pipeline around it.** The
residual — `inprocess_ms` minus the sum of the stages, i.e. the formula copying
between stages — is **1,359 ms of 342,024, or 0.4%**. Compaction (the
renumbering after BVE) is 2,295 ms, 0.7%. So "is the cost in the pass or in
re-encoding afterwards?" has a clean answer: **the pass**. Nothing is to be won
by making the plumbing cheaper.

### But *within* BVE, the cost is not in finding things

At the CNF level, each pass is run twice — the second time on its own output,
where it rebuilds the same occurrence lists and finds nothing. On the smoke
instance (`bv-term-small-rw_1128`, 4,571 vars / 18,559 clauses):

| arm | first run | second run (setup floor) | setup share |
|---|---:|---:|---:|
| subsume | 3.9 ms | 2.4 ms | 61% |
| vivify | 6.8 ms | 6.1 ms | 90% |
| **bve** | **205.4 ms** | **199.9 ms** | **97%** |

BVE's second run eliminated **zero** variables and still cost 97% of the first
run. Nearly all of BVE's expense is occurrence-list construction plus the
per-variable elimination-bound evaluation — work it does whether or not any
variable turns out to be eliminable. That is the part a schedule can amortise;
the resolution work itself is nearly free by comparison.

---

## 5. The two failure modes, separated

The question put to me was whether "inprocessing does not pay inside 24 s" is
(A) the passes being genuinely expensive at any budget, or (B) a wall-clock
cutoff halting a pass after it has paid its setup and before it collects the
benefit. These need opposite work, and an aggregate ratio cannot separate them.

They are **both true, on disjoint files**, and the counters say which is which
per file rather than on average.

The distribution of `inprocess_ms` over the 195 files that ran it:

| statistic | value |
|---|---:|
| median | **28 ms** |
| files under 100 ms | 115 of 195 |
| files under 1 s | 150 of 195 |
| files over 10 s | **18** |
| mean | 1,754 ms |
| max | 12,011 ms |

The mean is 63x the median. Reporting the mean alone would describe a corpus
that does not exist.

### (B) is real, rare, and dominant in cost

16 of 195 files record `bve_deadline_expired = 1` — BVE returned with its
deadline already passed. Every one of them also spent **more than 90% of its
granted slice**:

| off ms | inproc ms | `inprocess_ms` | granted slice | `bve_ms` | verdict | file |
|---:|---:|---:|---:|---:|---|---|
| 24,366 | 24,379 | 11,947 | 11,486 | 8,454 | unknown | `148.smt2` |
| 24,112 | 24,255 | 11,881 | 11,660 | 8,047 | unknown | `tsp_rand_70_300_…` |
| 15,134 | 22,276 | 11,954 | 10,933 | 366 | sat | `div3.c.50.smt2` |
| 4,243 | 13,776 | 11,461 | 11,161 | 6,065 | sat | `bin_eventlogadm_vc352379` |
| 3,028 | 13,445 | 11,236 | 11,069 | 5,604 | sat | `convert-jpg2gif-query-1166` |
| 2,076 | 13,215 | 11,691 | 11,462 | 8,095 | sat | `bin_libmsrpc_vc1225899` |
| 1,753 | 12,767 | 12,011 | 11,801 | 8,797 | sat | `bench_12354` |
| 1,677 | 13,004 | 11,684 | 11,506 | 8,491 | sat | `bin_libsmbclient_vc1225764` |
| 1,215 | 12,712 | 11,776 | 11,638 | 9,618 | sat | `bin_eventlogadm_vc331099` |
| 1,129 | 12,673 | 11,785 | 11,664 | 10,009 | sat | `bin_libsmbsharemodes_vc6315` |
| 821 | 12,500 | 11,828 | 11,715 | 10,820 | sat | `bin_libsmbsharemodes_vc5714` |
| **116** | 12,123 | 12,005 | 11,963 | 11,487 | sat | `bench_3010` |
| **88** | 12,114 | 12,004 | 11,963 | 11,459 | unsat | `bench_3708` |
| **90** | 12,108 | 11,996 | 11,961 | 11,410 | unsat | `bench_2598` |
| **93** | 12,100 | 11,995 | 11,962 | 11,447 | unsat | `bench_869` |
| **92** | 12,095 | 11,995 | 11,964 | 11,468 | unsat | `bench_3293` |

**189 s of the corpus's 342 s total inprocessing spend is inside a BVE that was
cut off unfinished** — 55% of all inprocessing cost, on 8% of the files. On the
last five rows the baseline decides the query in **88–116 ms**, and turning
inprocessing on spends **12 seconds** first, to no benefit whatsoever.

Note what makes this (B) rather than (A): these passes did not finish and report
a cost. They were stopped by the clock. Their cost is therefore a property of
**the budget**, not of the pass — at a 120 s budget they would be granted 60 s
and some would complete, which is a different experiment (§6).

### The lever nobody was looking for: vivification rescues BVE

Vivification is documented as the most expensive of the three passes and is off
even in `InprocessOptions::preprocess()`. On this corpus it is the opposite —
it makes the whole of inprocessing **20% cheaper** (274 s vs 342 s) and shrinks
the formula further (clauses 0.675 vs 0.711 of the original). The mechanism is
visible per file:

| file | `bve_ms` (inproc) | truncated? | `vivify_ms` | `bve_ms` (with vivify) | truncated? | wall |
|---|---:|---|---:|---:|---|---|
| `bench_3293` | 11,468 | yes | 45 | **27** | no | 12,095 → **680** ms |
| `bench_3708` | 11,459 | yes | 44 | **28** | no | 12,114 → **689** ms |
| `bench_2598` | 11,410 | yes | 44 | **27** | no | 12,108 → **656** ms |
| `bench_869`  | 11,447 | yes | 45 | **27** | no | 12,100 → **695** ms |
| `bench_3010` | 11,487 | yes | 18 | 11,513 | yes | 12,123 → 12,122 ms |

On four of the five, **45 ms of vivification turns an 11,468 ms truncated BVE
into a 27 ms completed one** — a 425x reduction in BVE's cost, for a pass that
is supposed to be the expensive one. Something about the clause shape these
queries produce makes BVE's per-variable bound evaluation pathological, and
vivification removes it. The fifth file is unaffected, so this is a shape, not
a universal rule.

This is the most actionable finding in the lane, and it was invisible to every
aggregate: `inprocess_ms` says vivification made things faster, and only the
per-stage split says *why*.

---

## 6. Results still running or not run

Stated as "did not run" rather than estimated.

* **120 s sweep (off / inproc).** RUNNING at the time of writing; results in
  `qfbv-120s-*.jsonl`. This is the direct test of the handed-down claim and of
  whether the 16 truncated files complete when granted a 60 s slice.
* **Per-pass CNF sweeps.** RUNNING. `pass-conflicts-20k.jsonl` reproduces
  ADR-1750's protocol (fixed 20,000-conflict budget, arms `off`/`subsume`/`bve`/
  `preprocess`) on parity-corpus CNFs instead of `p4dfa`;
  `pass-wall-24s.jsonl` adds the wall-clock verdict and the setup/work split.
* **The variance test (5 identical repeats on the 19 boundary files).** NOT YET
  RUN — it must run on a quiet host, and the box is currently running the two
  sweeps above.
* **Proof-checking cost with inprocessing on.** NOT RUN. ADR-1750 measured it
  (231x backward vs forward) and nothing here re-tests it.
* **`prove_unsat` mode.** NOT RUN. Every sweep above is the default
  non-certifying path.

### What the CNF-level population is, and what was excluded

`dump_dimacs` claims to mirror the encoding the fair runs use. **Checked rather
than assumed, it does not always.** Comparing its `p cnf` header against the
solver's own `cnf_variables`/`cnf_clauses` on the same file:

| file | `dump_dimacs` | shipping solver |
|---|---|---|
| `bench_13795` | 504,958 / 2,158,659 | 246,160 / 962,977 |
| `bench_8967` | 12,355 / 50,811 | 8,986 / 40,042 |
| `bench_10924` | 134,823 / 542,638 | 90,283 / 337,441 |

Three of 14 comparable files differ, `dump_dimacs` larger every time. Two more
(`bench_10451`, `countbitsrotate128`) could not be compared at all: the shipping
path never reached the CNF stage inside 24 s, so those two are bound by
*lowering*, not by search, and no amount of CNF inprocessing can decide them.

So the per-pass population is the **11 files whose encoding was verified
identical** (1,300 to 277,149 variables, a 213x range), and the five excluded
files are recorded with the reason in
`bench-results/inprocess-cost-2026-09-08/cnf-population-candidates.txt` versus
`…-verified.txt`. A population chosen after seeing the results is the one thing
a protocol cannot allow; writing down what was dropped, and why, before quoting
a number is the only defence.

This is worth knowing beyond this lane: **`dump_dimacs` is not a faithful mirror
of the shipping encoding**, and a measurement that assumes it is will be about a
formula roughly twice the size of the real one, on some files, silently.

---

## 7. Soundness: what was checked, and what was not

A claim reached me mid-lane that `sat_bv_backend`'s `compact()` step breaks
model reconstruction, so that turning inprocessing on "would produce `sat`
results we cannot check against the original term". **That is not what the code
does, and not what the corpus shows.** Recorded carefully because it is a
soundness claim in both directions.

What the shipping path does: `reconstruct_sat_result` composes
`compaction.expand` (compacted → BVE-reduced width) with `reconstruction.extend`
(BVE-reduced → original), and only then does `handle_sat_result` lift through the
AIG and **replay the model against the original assertions**. A model that fails
to satisfy the originals returns `Unknown`, not `sat`. So a broken reconstruction
would cost decided files; it could not produce a wrong `sat`.

What the corpus shows: over 200 files × 3 arms, **188 decided per inprocessing
arm, 173 cross-checked against the benchmark's declared `:status`, zero
disagreements, and zero cross-arm verdict conflicts.** Inprocessing decided
strictly *more* than the baseline, which is the opposite of the signature a
broken reconstruction would leave.

**What is genuinely unresolved is the `unsat` certificate, not the `sat` model.**
ADR-1750 states it plainly: with `cnf_inprocessing` on, `sat_bv_backend` checks
its `unsat` proof against the *reduced* formula, and no pass's DRAT enters the
emitted stream — so the BVE link is trusted rather than checked. That is a real
gap in proof coverage. It is not a wrong verdict, and it is not about `sat`.

**None of the runs in this document enabled inprocessing anywhere but in its own
measurement process.** No default was changed; `SolverConfig::cnf_inprocessing`
is still `false`, and every arm is a per-invocation configuration in a probe
binary.

---

## 8. What this says to do

1. **Do not schedule inprocessing by giving it a fraction of the wall clock.**
   Half the remaining budget is a rule that spends 12 s on a query the search
   decides in 90 ms, 16 times in 200 files, for 55% of the total cost. A cheap
   admission test — or a much smaller absolute cap with the option to extend —
   recovers nearly all of that.
2. **Measure the pass in conflicts, budget it in something deterministic.**
   ADR-1750's break-even is in conflicts precisely because that unit does not
   move with host load; the cutoff that fights it is wall-clock. Those two
   disagree by exactly the amount the host varies, which is what the variance
   test (§6, not yet run) is for.
3. **Attack BVE's setup, not its search.** 97% of BVE's cost on the smoke
   instance is work it does before finding anything. A schedule that reduces
   repeatedly amortises that; a faster resolution loop does not touch it.
4. **Turn vivification on if inprocessing is ever turned on.** It costs ~45 ms
   where it matters, makes the whole of inprocessing 20% cheaper, shrinks the
   formula further, and converts a pathological BVE into a trivial one on four
   of five measured cases.
5. **The `unsat` certificate gap (§7) is the blocker on enabling any of this by
   default**, not the `sat` path and not the cost.
