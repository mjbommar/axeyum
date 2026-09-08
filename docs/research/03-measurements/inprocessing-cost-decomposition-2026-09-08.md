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

* On **179 of the 195 files** that ran inprocessing the passes reach their own
  fixpoint inside the slice. Across all 195 the **median** spend is **28 ms**
  (115 files are under 100 ms). That is not a cost problem at all.
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
3. **Setup versus work.** Each pass is run a second time on its own output. It
   rebuilds the same occurrence lists, so its time approximates the cost the
   pass pays for existing — approximates, because a pass that has not reached a
   fixpoint does real work on the re-run, and the tool prints the re-run's own
   reduction counters so a reader can tell which case they are looking at
   (§4 shows both).
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

**The crossover is between 12 s and 24 s — and the sub-24 s columns understate
the `on` arms (see below), so it is at or below that band.** The handed-down
"~5x the 24-second budget" break-even is not what this corpus shows: on the
shipped path, at the competition budget, inprocessing is already slightly ahead
on decided count.

That "slightly" is doing real work, and §5's variance result cuts it further:
the gain is one file, and that file decides in only 1 of 5 repeats under load.
**The defensible statement is that inprocessing is at parity on decided count at
24 s and behind on PAR-2 — not that it wins.**

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

### The derived columns are biased, and they are biased AGAINST inprocessing

Thresholding a 24 s run to read off a 6 s result assumes behaviour does not
depend on the budget given. **It does**: inprocessing is granted half the
remaining solve budget, so a 6 s budget is a 3 s slice, not a 12 s one.

I first wrote that this made the derived columns optimistic for the `on` arms.
**That is backwards, and the direction matters.** Take `bench_3708`: at a 24 s
budget it spends 12.0 s in a truncated BVE and then decides in ~0.1 s, wall
12,114 ms, so the derived 12 s column scores it NOT solved. At a *real* 12 s
budget the slice is 6 s, so the same file would spend ~6 s and decide at ~6.1 s
— **solved**. The derivation charges the `on` arm for a slice it would never
have been granted at the smaller budget.

So the sub-24 s columns are **exact for `off`** (nothing in that arm depends on
the budget except when it stops) and a **lower bound for the `on` arms**. The
true crossover is therefore at or below the 12–24 s band, not above it — which
moves the answer further from the handed-down 120 s, not closer.

Measured rather than left as an argument. A real 12 s sweep over the population
where the derivation can differ (§6), first six files:

| file | 24 s run: wall / slice / spend | real 12 s run: wall / slice / spend | verdict at 12 s |
|---|---|---|---|
| `bench_12354` | 12,767 / 11,801 / 12,011 | **9,056** / 5,443 / 5,919 | **sat — solved** |
| `vlsat3_a85` | — | 12,136 / 5,971 / 5,988 (truncated) | unknown |
| `predicate_851` | — | 12,134 / 5,945 / 862 | unknown |

`bench_12354` is the case in point: the derived 12 s column scored it **not
solved** because it took 12,767 ms at a 24 s budget, and at a real 12 s budget
it decides `sat` at **9,056 ms**. The slice halved from 11,801 ms to 5,443 ms
and the file came in under budget. The derivation was wrong about it, in the
direction stated.

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

### Within a pass: setup dominates exactly where the pass finds least

At the CNF level each pass is run twice — the second time on its own output,
where it rebuilds the same occurrence lists and has (nearly) nothing left to
find. The second run's time is the floor the pass pays for existing;
`first − second` is the part that depends on there being work.

On the first smoke instance (`bv-term-small-rw_1128`, 4,571 vars) the split
looked decisive: BVE's second run eliminated **zero** variables and still cost
**97%** of the first run. **That does not generalise, and the wider sweep says
so.** Median setup share over the encoding-verified files measured so far:

| pass | files | median setup share | range | what the re-run still found |
|---|---:|---:|---|---|
| vivify | 6 | **92%** | 83–96% | nothing at all on any file |
| subsume | 7 | 48% | 4–98% | 0–673 clauses |
| **bve** | 6 | **30%** | **3–104%** | nothing at all on any file |
| preprocess (sub+BVE) | 6 | 68% | 41–110% | up to 44,747 clauses, 15,359 vars |

Three things follow, and the first corrects my own earlier reading.

* **BVE's setup share is low where BVE does real work.** On `tsp_rand_70_300`
  it eliminated 277,149 → 143,443 live variables and setup was 3% of its 35.8 s.
  On the smoke instance it eliminated 482 of 4,571 and setup was 97%. The
  pattern is not "BVE is all setup"; it is **the setup share is high exactly
  where the pass finds little** — which is exactly the case where running the
  pass at all was the mistake. That is still the lever, but the lever is
  *admission*, not index reuse. (Medians here are over 6–7 files per arm; the
  sweep was stopped at 36 of 66 rows — §6.)
* **Vivification alone is 92% setup and found nothing on any of these files**,
  leaving the formula bit-identical (clause and literal ratios 1.000). Its
  corpus-level benefit in §5 comes from files not in this CNF population;
  here it is pure overhead. Both are true, of different files.
* **A setup share above 100% is not a bug, it is the caveat firing.**
  `preprocess`'s re-run subsumes 44,747 more clauses and eliminates 15,359 more
  variables, so subsumption-then-BVE has *not* reached a fixpoint in one round
  and the second run is doing real work rather than measuring a floor. Where
  the re-run found something, the "setup share" column is an overestimate and
  is not a setup measurement at all.

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

### The variance test: truncation is deterministic, but the boundary is a coin flip

Five identical repeats per file, both arms, over the boundary population, run at
host load **16–40** (other lanes; the "quiet" half of this comparison was never
available — see §6). The driver runs a file's five repeats back to back, so
every group is complete or absent; the run was stopped with 8 files complete in
both arms.

Compared on the **8 files where both arms have a complete 5-repeat group** — an
unmatched comparison here is meaningless, because the slower arm completed
fewer files and its median would be over a different, harder population:

| file | `off` min–max ms | `off` max/min | `inproc` min–max ms | `inproc` max/min | BVE truncated |
|---|---|---:|---|---:|---|
| `bench_3388` | 0–2 | 2.00x | 0–1 | 1.00x | no |
| `bench_3293` | 188–305 | **1.62x** | 12,314–12,365 | **1.00x** | yes |
| `bench_12354` | 2,789–4,361 | 1.56x | 13,166–14,063 | 1.07x | yes |
| `ext_con_008_001_0064` | 23,725–24,223 | 1.02x | 8,455–8,983 | 1.06x | no |
| `simple_processors_008_006_0004` | 24,139–24,235 | 1.00x | 22,037–24,169 | 1.10x | no |
| `div3.c.50` | 24,902–25,000 | 1.00x | 24,746–25,000 | 1.01x | yes |
| `tsp_rand_70_300` | 24,230–25,000 | 1.03x | 24,544–25,000 | 1.02x | yes |
| `148` | 24,582–25,000 | 1.02x | 24,906–25,000 | 1.00x | yes |
| **median** | | **1.03x** | | **1.01x** | |
| **worst** | | 2.00x | | 1.10x | |

Three findings, and they answer (A)-versus-(B) as a pair rather than a choice.

* **Truncation never flipped.** Across every group, on every file where the flag
  was reported, BVE was either always cut off or never was — **zero**
  disagreements between runs that both reported it. So the truncation in §5 is
  **deterministic saturation, not a race the clock sometimes wins**.
  Hypothesis (B) is real as a *budget dependence* — the pass's cost is set by
  the slice, and the real 12 s sweep above shows the same file spending 5.9 s
  instead of 12.0 s when the slice halves — and it is **not** real as
  run-to-run variance.
* **Wall-time spread is small on both arms even at load 40**, and if anything
  the truncating arm is the *steadier* one: `bench_3293` runs 12,314–12,365 ms
  with inprocessing on (1.00x, truncated every time) against 188–305 ms with it
  off (1.62x). A pass that always spends exactly its slice is perfectly
  reproducible; that is the point. The wall-clock cutoff is not producing the
  instability (B) predicted.
* **But verdicts do flip at the boundary, on both arms.** Two groups changed
  answer across identical repeats: `ext_con_008_001_0064` on `off` (4× unknown,
  1× unsat, walls 23,725–24,223 ms against a 24 s budget) and
  `simple_processors_008_006_0004` on `inproc` (4× unknown, 1× unsat at
  22,037 ms). That is a property of deciding *at* the budget, not of
  inprocessing.

The last one carries a caveat against this lane's own headline. **The single
file inprocessing genuinely gains at 24 s is itself load-fragile**: on the quiet
run `simple_processors_008_006_0004` decides `unsat` at 13,798 ms, and under
load 22–30 it decides in only **1 of 5** repeats. A one-file gain measured once
on a quiet box is not a result to build on.

---

## 5b. Does ADR-1750 reproduce? The per-conflict result yes; the break-even not always

ADR-1750's protocol, re-run on this tree: fixed 20,000-conflict budget, arms
`off`/`subsume`/`bve`/`preprocess`, arm order rotated per file, over the 11
encoding-verified parity `QF_BV` CNFs (1,300 to 277,149 variables) instead of
the eight `p4dfa` instances. 44 rows, 11 files, none killed.

### The deterministic half reproduces

Median propagations per conflict against `off`, over the files where every arm
exhausted the budget:

| | `subsume` | `bve` | `preprocess` |
|---|---:|---:|---:|
| **this lane** (parity corpus, s4) | 1.000 | **0.496** | **0.474** |
| ADR-1750 (`p4dfa`, s5) | 0.933 | 0.426 | 0.388 |

Same ordering, same magnitude, different corpus, different host, current tree.
These counters are deterministic at a fixed conflict budget, so host load cannot
touch them — which is exactly why they are the half worth quoting.

The qualitative claims carry too: subsumption alone does essentially nothing for
propagation volume (1.000 here, 0.933 there), and every bit of the effect is BVE.

### The break-even carries in magnitude, but it does not always exist

| | value |
|---|---|
| BVE break-even, median (this lane) | **57,187 conflicts** |
| BVE break-even, median (ADR-1750) | ~92,000 conflicts (range 59k–131k) |
| BVE break-even in seconds of unreduced search (this lane) | 0.0 s to **129,583 s**, median 4.8 s |
| ADR-1750, same quantity | 4.6 s to 176.9 s |

Two differences, and the second is the substantive one.

* **Magnitude agrees.** 57k against a 59k–131k range is just below it, same
  order. Given the corpus and host differ, this is a reproduction.
* **A break-even does not always exist here.** ADR-1750 reports one for all
  eight of its files. On the parity corpus **BVE has none on three of eight**:
  it is not faster per conflict than the baseline, so no amount of search
  repays the pass. The clearest case is `vlsat3_a85` — BVE spent **15.0 s** to
  move the conflict rate from 40,458/s to 40,463/s. `p4dfa` is the family BVE
  was characterised on, and the characterisation does not transfer to this
  corpus unconditionally.

And ADR-1750's observation that the break-even is *flat in conflicts and not in
seconds* is not merely confirmed but amplified: across eight files the seconds
span **six orders of magnitude** (0.0 s to 129,583 s). That is the argument for
denominating a scheduling decision in conflicts rather than wall time, stated
more strongly than the original data supported.

Two pass costs that no 24-second budget can ever absorb, worth naming because
they are on the shipped corpus: BVE's pass on `bench_12354` takes **128 s**, and
`preprocess` on the same file **155 s**.

### Timing caveat on this table, and it is not small

`load_start=1.82`, `load_end=15.98` — another lane began a build partway through
the sweep, so absolute seconds drift across it. Per-file break-evens remain
internally consistent (a file's four arms run back to back, seconds apart, and
the rotation stops one arm always being first), but **the level is advisory and
a quiet re-run is owed**. The propagations-per-conflict table above is
unaffected: those counters are deterministic.

## 6. Results still running or not run

Stated as "did not run" rather than estimated.

**Every incomplete run below was stopped deliberately when other lanes took the
host to a sustained load of 30–40 and kept it there for hours.** At that load
these are not measurements: the numbers they would produce would be about the
queue. Row counts are given so nothing here can be mistaken for a full sweep.

* **120 s sweep. DID NOT RUN to a usable result.** The full 200-file version was
  abandoned after 26 files (~2 minutes per file, i.e. 6.5 h, almost all of it
  re-deciding files that decide in 90 ms); its prefix is kept as
  `qfbv-120s-*-ABANDONED-PREFIX.jsonl` — a prefix of a list is not a sample of
  it, and those rows must never be read as a 120 s result. The targeted
  replacement over the 28 files whose verdict *can* differ at a longer budget
  reached **4 of 28 rows per arm** before being stopped. **So the handed-down
  claim was not tested at 120 s directly.** It was tested at 24 s and below,
  where inprocessing is already at parity — which is what refutes it.
* **Per-pass CNF sweep, conflict-budgeted.** DONE, 44/44 rows — §5b.
* **Per-pass CNF sweep, wall-clock-budgeted.** PARTIAL, **36 of 66 rows**
  (`pass-wall-24s.jsonl`). The setup/work medians in §4 are over 6–7 files per
  arm, not 11.
* **Real 12 s sweep** (`qfbv-12s-boundary-inproc.jsonl`). PARTIAL, **23 of 28
  rows**, `inproc` arm only. Enough to demonstrate the derivation's direction
  (§3), not enough for a 12 s solved count.
* **The variance test, under load.** PARTIAL — **8 files complete in both arms**
  of 19. Every group present has all five repeats (the driver runs a file's
  repeats back to back), so the partial is a prefix of *files*, never of
  repeats. Reported in §5.
* **The variance test, on a quiet host.** NOT RUN. Other lanes took the box to
  load 16–40 shortly after the 24 s sweep finished and it never came back down;
  the quiet half of that comparison is the half I do not control. **So the
  measured spread is an upper bound** — a quiet host cannot be noisier — which
  is the useful direction, but the load-versus-quiet contrast itself was not
  made.
* **A quiet re-run of the conflict-budget sweep.** NOT RUN — owed, per the
  caveat in §5b.
* **A mutation control on the `sat` reconstruction path.** NOT RUN. §7 rests on
  the code path plus a corpus-scale argument, not on a deliberately broken
  `reconstruct_sat_result`. Doing it properly needs a rebuild, and the box was
  saturated.
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

That second paragraph is the live negative control, and it is worth being
explicit about why: a broken reconstruction cannot produce this data. It would
fail replay, return `Unknown`, and show up as the inprocessing arms **losing**
decided files. They lost none. What this does *not* establish is that the
replay guard would catch a reconstruction bug that produces a *different but
still satisfying* model — no such bug is possible to distinguish this way, and
a deliberate mutation of `reconstruct_sat_result` is the test for it. **That
mutation was not run** (§6).

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
3. **Attack admission, not BVE's inner loop.** The setup share is high exactly
   where the pass finds little (97% on an instance where it eliminated 11% of
   variables, 3% on one where it eliminated 48%), so index reuse buys least on
   the files that cost most. A cheap predictor of "will BVE find anything here"
   is worth more than a faster BVE.
4. **Turn vivification on if inprocessing is ever turned on.** It costs ~45 ms
   where it matters, makes the whole of inprocessing 20% cheaper, shrinks the
   formula further, and converts a pathological BVE into a trivial one on four
   of five measured cases.
5. **The `unsat` certificate gap (§7) is the blocker on enabling any of this by
   default**, not the `sat` path and not the cost.
