# Roadmap 3.2 measured: DO NOT BUILD any of the 18 missing passes — the valve's bootstrap constant is off by 1.7x and that is the next task

**Date:** 2026-09-10 · **Host:** `s4` (12th Gen Intel i5-12600K, 6 P-cores /
4 E-cores, 16 threads, 123 GB) · **Tree:** `474423c8d` · **Corpus:** the pinned
`bench-results/parity-lists/QF_BV.txt` (200 files, sha256 `6f873e15b191`), and
the 17 DIMACS dumps of files from it under `/data0/measure-inproc-cost/cnf/`.

Roadmap item 3.2
([`11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
proposes adding the 18 CaDiCaL inprocessing passes we lack — failed-literal
probing, hyper-binary resolution, blocked- and covered-clause elimination,
bounded variable addition, SAT sweeping, transitive reduction, instantiation,
gate extraction with congruence closure — gated by "per-pass ratchet delta on
the QF_BV parity slice; keep only passes that move it."

**Recommendation: DO NOT BUILD, and not primarily for the reason item 1.2
suggests.** The measurement found something more actionable than an ordering
argument: `TickValve`'s `bootstrap_reference` — the constant that funds a
pre-search inprocessing round, and the *only* valve knob that acts at our single
inprocessing call site — is **1.69x smaller than the smallest value that admits
BVE on the one file inprocessing wins on this slice**, and 19x smaller than the
top of the window that still refuses every file BVE ruins. Fixing one integer
and re-running item 1.2 is a bounded task with a measured target. Adding an
eighteen-pass family to a pipeline whose admission constant has not yet been
calibrated is the wrong order of operations.

---

## 0. The question, as numbers

Three, in the order they were asked:

| question | answer |
|---|---:|
| Where does the current inprocessing time go, per pass, on the parity slice? | **BVE 76%, subsume 22%, everything else under 2%** (§2) |
| Would routing item 1.5's `TickValve` in change 1.2's answer? | **Not at its shipping constants** — it refuses BVE on 98/195 files carrying 99.8% of BVE's spend, *including the single file inprocessing gains* (§3). At a recalibrated `bootstrap_reference` it plausibly does, and the window is measured (§4). |
| How much frontier is even addressable by an inprocessing pass here? | **9 files.** `off` leaves 14 of 200 undecided at 24 s; 5 of those never reach a CNF at all. The whole existing pipeline — 2.54 M variables eliminated corpus-wide — converts **1** of the 9 (§5). |

And the shape census for the cheapest missing-pass family: over 3.82 M
variables / 14.65 M clauses / **3.73 M binary clauses (25.5%)**, SCC finds
**4,362 substitutable variables — 0.114%**, and nothing at all on 6 of 17 files
(§6).

---

## 1. What the shipping path actually runs, and it is not six passes

`crates/axeyum-solver/src/sat_bv_backend.rs:294` is the **only** call site of
`maybe_inprocess`, and it sits before the search. So what ships is **one
pre-search preprocessing round**, not inprocessing in the CaDiCaL sense — there
are no in-search rounds at all.

The stages `inprocess_scheduled` offers are XOR propagation, equivalent-literal
substitution (`decompose`), subsumption, vivification, BVE, and compaction. Two
of them do not run on the shipping path:

* **`decompose` (roadmap item 2.1, merged in `295781893` yesterday) is off.**
  It is admitted through `InprocessObserver::decompose_grant`, which is a
  *defaulted* trait method returning `None`
  (`crates/axeyum-cnf/src/inprocess.rs:445`). `BackendInprocessObserver`
  (`sat_bv_backend.rs:1641`) does not override it — verified: `grep -rn "fn
  decompose_grant" crates/` returns four hits, all in `axeyum-cnf`, none in
  `axeyum-solver`. That is consistent with 2.1's own merge message ("Corpus at
  baseline, 0 DISAGREE"): the pass changed nothing because it did not run.
* **XOR propagation is a no-op on this slice** (107 ms over 195 files; 0 units
  added on the files inspected).

So the honest count is **five stages offered, two that cost anything.** Item
3.2's premise "we now have 6" is true of the crate and not of the solver.

---

## 2. Where the cost goes: re-derived from the committed 2026-09-08 counters

[`inprocessing-cost-decomposition-2026-09-08.md`](inprocessing-cost-decomposition-2026-09-08.md)
already measured this and I did not re-run the sweep; I re-derived the table
from the committed per-file rows so the number below is read off the data rather
than inherited from the prose. `inproc-vivify` is the arm that matches the
shipping config (`cnf_vivify` defaults `true`, so flipping `cnf_inprocessing`
alone gives you this arm).

```
$ python3 <probe>   # over bench-results/inprocess-cost-2026-09-08/qfbv-24s-vivify.jsonl
===== arm inproc-vivify =====
files 200, ran inprocessing 195
stage totals ms: {'xor_propagate_ms': 108, 'subsume_ms': 59019, 'vivify_ms': 2522,
                  'bve_ms': 209666, 'compact_ms': 2169, 'inprocess_ms': 274454}
```

| stage | ms | share of `inprocess_ms` |
|---|---:|---:|
| xor_propagate | 108 | 0.04% |
| subsume | 59,019 | 21.5% |
| vivify | 2,522 | 0.9% |
| **bve** | **209,666** | **76.4%** |
| compact | 2,169 | 0.8% |
| residual (plumbing) | 970 | 0.4% |

**One existing pass dominates.** That is the actionable finding the brief asked
for, and it points at admission, not at a new pass.

---

## 3. The valve at its shipping constants refuses BVE where BVE earns its keep

`maybe_inprocess` runs once, pre-search, so `TickValve`'s numeraire
(`search_ticks`) reads **zero** and `TickEffort::bootstrap_reference` is what
funds the round (`crates/axeyum-cnf/src/ticks.rs:551-560`, CaDiCaL's
`preprocessinit`). The decision is then fully determined by two integers:

```
allowance = bootstrap_reference * per_mille / 1000     # search_ticks == 0
threshold = threshold_per_clause * |clauses|
refuse iff allowance < threshold
```

At the shipping settings (`bootstrap_reference` 2,000,000; subsume
`MAJOR_PASS` = 100‰ / 5x; BVE `EXPENSIVE_SETUP` = 50‰ / 20x; `decompose`
`DECOMPOSE_EFFORT` = 100‰ / 1x) that is a pure clause-count gate: subsume
admitted at or below 40,000 clauses, **BVE at or below 5,000**, decompose at or
below 200,000.

### 3a. The real valve, asked directly (the control on the arithmetic)

A throwaway `axeyum-cnf` example wrapped `RecordingObserver::granting(u64::MAX)`
in `TickValve::shipping` — so any `None` is the *valve's* refusal and not an
inner policy declining — and called `grant`/`decompose_grant` on each dumped
CNF. Verbatim, on the two smallest files (positive and negative control, both
fire):

```
{"file":".../04_simple_processors_008_006_0004.cnf","vars":2490,"clauses":8510,
 "valve_subsume":200000,"valve_bve":null,"valve_decompose":200000,
 "valve_log":["subsume granted ticks=0 clauses=8510 allowance=200000 reference=2000000 budget=200000",
              "bve refused ticks=0 clauses=8510 accrued=100000 threshold=170200 budget=none"]}
{"file":".../10_ext_con_008_001_0064.cnf","vars":1300,"clauses":3558,
 "valve_subsume":200000,"valve_bve":100000,"valve_decompose":200000,
 "valve_log":["subsume granted ticks=0 clauses=3558 allowance=200000 reference=2000000 budget=200000",
              "bve granted ticks=0 clauses=3558 allowance=100000 reference=2000000 budget=100000"]}
```

Across all 17 dumped CNFs the valve refuses **subsume on 11, BVE on 16,
decompose on 6** — and every decision matched the arithmetic above, so the
offline simulation in §3b is validated against the shipped code.

### 3b. Simulated over the full 195-file population

| pass | files refused | spend refused | share of that pass's spend |
|---|---:|---:|---:|
| subsume | 58 / 195 | 57,936 ms | 98.2% |
| **bve** | **98 / 195** | **209,207 ms** | **99.8%** |

`inprocess_ms` over the slice falls from **274.5 s to ~7.3 s**. And
`bve_variables_eliminated` falls with it: of the 2,537,430 variables BVE
eliminates corpus-wide, the valve-admitted files account for **17,162 —
0.68%**.

So the valve does not make BVE cheaper. It makes BVE **not happen** on 99.3% of
the work it does. That is an approximation of `cnf_inprocessing: false` with
extra machinery, which is 1.2's answer already.

### 3c. And it refuses the one file that gains

The parity slice's genuine gain from inprocessing is
`simple_processors_008_006_0004.smt2`: `off` = unknown at 24,113 ms, `on` =
**unsat at 13,823 ms**. (The second apparent gain, `bench_3388`, is the harness
flake the 2026-09-08 note already labels: the `off` row records `killed` at
0 ms and the file decides `unsat` in 0 ms on re-run.)

The valve **refuses BVE on that file** — `threshold=170200` against
`accrued=100000`, printed verbatim above.

**And the gain is BVE's, not subsumption's.** Two independent measurements:

* The front-door counters for that file: BVE eliminated **1,515 of 2,490
  variables**, removed 10,045 clauses and added 6,081 (8,510 → 4,475 clauses,
  24,830 → 14,694 literals) in **221 ms** of an 11,994 ms budget. Subsumption
  subsumed **71** clauses and strengthened 74 literals, in 2.4 ms.
* A four-arm CNF-level run on the same file at a 24 s wall budget
  (`inprocess_pass_cost`, release, `taskset -c 0-7`, back to back):

| arm | vars live after | clauses after | props/conflict | conflicts/s |
|---|---:|---:|---:|---:|
| off | 2,490 | 8,510 | 147.04 | 18,038 |
| subsume | 2,490 | 8,439 | **147.04** | 13,829 |
| bve | 897 | 4,217 | **99.41** | 21,930 |
| preprocess | 975 | 4,475 | 103.83 | 25,031 |

Subsumption leaves propagations-per-conflict **bit-identical**; BVE cuts it
32%. **Caveat, stated because it is a coverage failure of this control:** all
four arms returned `interrupted` at 24 s — this CNF-level harness does not
reproduce the front door's 13.8 s decision, so it shows *which pass moves the
search* and does **not** show that subsume-only loses the verdict. Only the
re-measurement in §7 settles that.

---

## 4. The constant is outside its own window, and the window is wide

If the valve is to keep BVE where BVE pays and refuse it where BVE ruins the
file, the pre-search allowance must sit between two measured bounds on this
slice:

* **≥ 168,780** to admit BVE on the gain file (20 x its 8,439 post-subsume
  clauses).
* **< 3,214,720** to refuse all 12 files that record `bve_deadline_expired`
  (BVE returned with its slice already spent; they carry 96.7 s of the arm's
  209.7 s).

```
BVE allowance must be >= 168,780 to admit the gain file,
and < 3,214,720 to refuse every one of the 12 ruinous files.
=> bootstrap_reference in [3,375,600, 64,294,400); shipping value is 2,000,000,
   which is 1.69x too small.
```

The window spans **19x**, so this is not a knife-edge fit. The shipping value
falls **below** it.

| `bootstrap_reference` | BVE allowance | BVE admitted | BVE ms kept | ruinous admitted | gain admitted | subsume admitted | subsume ms kept |
|---:|---:|---:|---:|---:|---:|---:|---:|
| **2,000,000** (shipping) | 100,000 | 97/195 | 459 | 0/12 | **no** | 137/195 | 1,083 |
| 3,500,000 | 175,000 | 117/195 | 1,196 | 0/12 | YES | 151/195 | 2,534 |
| 5,000,000 | 250,000 | 125/195 | 2,375 | 0/12 | YES | 157/195 | 3,849 |
| **10,000,000** | 500,000 | 134/195 | 9,415 | 0/12 | YES | 176/195 | 11,031 |
| 20,000,000 | 1,000,000 | 148/195 | 25,552 | 0/12 | YES | 182/195 | 15,090 |
| 40,000,000 | 2,000,000 | 160/195 | 55,506 | 0/12 | YES | 187/195 | 22,197 |
| 70,000,000 | 3,500,000 | 173/195 | 98,870 | **1**/12 | YES | 191/195 | 34,946 |
| 200,000,000 | 10,000,000 | 184/195 | 133,943 | **2**/12 | YES | 195/195 | 59,019 |

At `10,000,000` the arm's inprocessing spend is roughly 0.1 + 11.0 + 2.5 + 9.4
+ 2.2 ≈ **25 s against 274 s** — a 91% cut — while admitting BVE on the gain
file and refusing it on every ruinous one.

**This is a fit with n = 1 on the positive side.** One file wants BVE admitted,
so the lower bound rests on a single observation and the choice of where inside
the window to sit is not settled by this data. What *is* settled, and is the
claim worth acting on: **the shipping constant is demonstrably outside the
window**, and it is outside in the direction that discards the only benefit
while the machinery stays.

Why the constant is wrong is not mysterious: `bootstrap_reference = 2_000_000`
was transcribed from CaDiCaL's `preprocessinit`, but our threshold is
denominated in *our* occurrence-list steps against *our* clause counts. The
number crossed a unit boundary without recalibration.

---

## 5. The addressable frontier is 9 files, and the pipeline converts 1

Any inprocessing pass can only help on a file `off` fails to decide. On the
pinned slice at 24 s:

```
parity slice files: 200
off decides 186; undecided 14
inproc-vivify decides 188; still undecided among off's undecided: 12
=> the whole inprocessing pipeline converts 2 of 14
```

Of the 14, **5 never reach a CNF at all** (`cnf_clauses = 0`: encoding itself
exhausts the budget — `bench_10451`, `bench_13795`, `countbitsrotate128`,
`testcase15.stp`, `string4x16.7...`). No CNF-level pass can touch them.

So the addressable population is **9 files**. The pipeline converts one of them
(`simple_processors_008_006_0004`); the second "conversion" is the acknowledged
`bench_3388` flake. On the **7 that stay undecided**, BVE eliminates 620 /
3,215 / 3,788 / 12,988 / 44,311 / 48,088 / 116,211 variables respectively — so
it is not failing there for want of reduction.

A new pass would have to beat that on the same 9 files. The gate item 3.2 sets
for itself ("keep only passes that move it") has a denominator of 9 and an
incumbent that scores 1.

---

## 6. Shape census for the binary-implication-graph family

The one family I could census cheaply is the one every probing pass feeds:
SCC / equivalent-literal substitution, hyper-binary resolution, transitive
reduction and failed-literal probing all mine the binary implication graph.
`decompose` (landed, unshipped) is its cheapest member, so its own counters are
the census. Unbudgeted, `max_rounds = 2`, over all 17 dumped CNFs:

| file | vars | clauses | binary | v_bve | decompose ms | classes | substituted | % of vars |
|---|---:|---:|---:|---|---:|---:|---:|---:|
| `10_ext_con_008_001_0064` | 1,300 | 3,558 | 22.3% | admit | 0.2 | 0 | 0 | 0.00% |
| `04_simple_processors_008_006_0004` | 2,490 | 8,510 | 22.6% | REFUSE | 1.0 | 4 | 20 | 0.80% |
| `12_dualexecution.t1.i15` | 3,580 | 10,941 | 37.2% | REFUSE | 2.1 | 339 | 796 | **22.23%** |
| `08_ext_con_028_008_0064` | 4,296 | 12,340 | 23.9% | REFUSE | 0.8 | 0 | 0 | 0.00% |
| `smoke` | 4,571 | 18,559 | 14.3% | REFUSE | 1.2 | 0 | 0 | 0.00% |
| `06_predicate_851` | 7,455 | 30,096 | 28.5% | REFUSE | 4.1 | 33 | 33 | 0.44% |
| `07_counterexample.dump.ia32_Mul` | 12,030 | 49,146 | 15.2% | REFUSE | 5.2 | 330 | 526 | 4.37% |
| `11_bench_8967` | 12,355 | 50,811 | 10.8% | REFUSE | 3.2 | 0 | 0 | 0.00% |
| `09_vlsat3_a85` | 13,778 | 55,349 | 23.1% | REFUSE | 3.6 | 0 | 0 | 0.00% |
| `13_gryzzles.30.lp` | 50,928 | 154,946 | 36.6% | REFUSE | 24.5 | 3 | 3 | 0.01% |
| `15_lfsr_002_127_112` | 58,421 | 174,806 | 33.0% | REFUSE | 23.4 | 1 | 1 | 0.00% |
| `02_countbitsrotate128` | 73,154 | 315,976 | 5.3% | REFUSE | 20.3 | 0 | 0 | 0.00% |
| `16_bench_10924` | 134,823 | 542,638 | 17.7% | REFUSE | 73.3 | 448 | 539 | 0.40% |
| `14_bench_12354` | 229,849 | 873,669 | 28.1% | REFUSE | 104.5 | 60 | 60 | 0.03% |
| `05_tsp_rand_70_300` | 277,149 | 936,326 | 30.6% | REFUSE | 143.8 | 604 | 1,204 | 0.43% |
| `03_bench_13795` | 504,958 | 2,158,659 | 9.2% | REFUSE | 276.7 | 1,073 | 1,120 | 0.22% |
| `01_bench_10451` | 2,431,260 | 9,253,921 | 29.5% | REFUSE | 1,161.3 | 60 | 60 | 0.00% |

```
totals: vars 3822397, clauses 14650251, binary clauses 3731244 (25.5%),
        substitutable vars 4362 (0.114%), decompose wall 1849 ms
files where SCC substitutes NOTHING: 6/17
```

Three readings:

* **The graph is big and almost acyclic.** A quarter of every clause database is
  binary — 3.73 M binary clauses — and they contain 4,362 substitutable
  variables, 0.114%. Our Tseitin encoding is binary-clause-rich and
  equivalence-poor. One outlier (`12_dualexecution`, 22.2%) shows the pass is
  not broken; six zeros show the shape is genuinely absent elsewhere.
* **The pass is genuinely cheap** — 1,849 ms for the whole 14.65 M-clause set,
  including 1.16 s on the 9.25 M-clause file, against BVE's 209.7 s on the
  slice. Cheap is not the problem.
* **It finds least on the files that cost most.** On the two ruinous files in
  this set — `14_bench_12354` and `05_tsp_rand_70_300` — SCC substitutes 60 of
  229,849 (0.03%) and 1,204 of 277,149 (0.43%).

Cheap, correct, proof-carrying, and it removes a thousandth of the variables on
a corpus where removing 2.5 million of them wins one file. That is the shape
answer for this family, and it is why "start with the cheapest pass and work up
CaDiCaL's schedule" does not get off the ground here.

---

## 7. Recommendation

**DO NOT BUILD any of the 18 passes.** Not one of them is named as a BUILD; a
family recommendation would not be a measurement and none is offered.

The right order, with the cheapest measured task first:

1. **Recalibrate `TickEffort::bootstrap_reference`** from 2,000,000 to a value
   inside the measured window `[3,375,600, 64,294,400)` — 10,000,000 is the
   mid-scale candidate. One integer in `crates/axeyum-cnf/src/ticks.rs:337`.
   Note that this is the *only* valve knob that acts at our call site: with one
   pre-search round and no in-search rounds, `search_ticks` is always zero, so
   item 1.5's outstanding **tick feed buys nothing for the shipping path
   today**. That reorders 1.2's stated next step.
2. **Route `TickValve::shipping` around `BackendInprocessObserver`** at
   `sat_bv_backend.rs:1701`, and give `decompose_grant` an override at the same
   time (it is currently the defaulted `None`, so item 2.1's pass has never
   run in the solver).
3. **Re-measure item 1.2** — `progress_frontier` at a pinned frame plus the
   corpus sweep, both arms — against the recalibrated valve. The prediction to
   pre-register: inprocessing spend on the parity slice falls from 274 s to
   ~25 s, the `simple_processors_008_006_0004` gain survives, and the 12
   `bve_deadline_expired` files stop losing their verdicts.
4. **Only if 1.2 then flips** does adding passes become the right question —
   and it should be asked against §5's denominator of 9 files, not against
   CaDiCaL's pass list.

If step 3 does not flip 1.2, the conclusion is stronger than "do not add
passes": it is that one pre-search reduction round is not where QF_BV time is
won on this corpus, and item 3.2 should be closed rather than deferred.

---

## 8. What I did not measure

* **Shape for 14 of the 18 passes.** Blocked- and covered-clause elimination,
  bounded variable addition, SAT sweeping, instantiation, gate extraction with
  congruence closure, and vivification-adjacent passes were **not** censused.
  Counting blocked clauses requires an occurrence-list implementation, which is
  the pass, not a probe. §6 covers the binary-implication-graph family only —
  and even there it measures **SCC's** shape (cycles), not failed-literal
  probing's or HBR's (implications). That the graph is equivalence-poor is a
  prior against HBR, whose product is more binaries feeding SCC; it is not a
  measurement of HBR.
* **End-to-end wall time or verdicts under the valve.** §3 and §4 predict
  *inprocessing spend* and *admission decisions*. Refusing BVE changes the
  formula the search sees, so a wall time cannot be derived from spend — only
  step 3 above settles it. Nothing here claims a frontier number.
* **Whether the gain file still decides without BVE.** §3c's four-arm run
  returned `interrupted` on all four arms and therefore did not reproduce the
  13.8 s decision. It establishes which pass moves the search, not which pass
  is necessary for the verdict.
* **Any corpus other than the pinned QF_BV parity slice** and the 17 CNFs dumped
  from it. `corpus/regression` — the corpus 1.2's 6-7 lost files came from —
  was not re-run here. The NAS mount at `/nas3/data/axeyum/corpus/` was present.
* **A fresh sweep.** §2, §3b, §4 and §5 are derived from the committed rows of
  the 2026-09-08 sweep (`bench-results/inprocess-cost-2026-09-08/`), re-parsed
  rather than re-run. §3a, §3c and §6 are new runs on this tree at `474423c8d`.
* **Contention.** §3c's arms ran back to back with 1-minute load moving 2.37 →
  10.74 across the four; the props/conflict column is load-insensitive and the
  conflicts/second column is not. The conclusion rests on the former.

## 9. Reproducing

The two throwaway probes were removed from the tree, as the Phase 3 method brief
requires. Neither is worth keeping as an `#[ignore]`d test: §3's arithmetic is
one line over constants that `crates/axeyum-cnf/src/ticks.rs` already
unit-tests, and §6's census is a `parse_dimacs` + `decompose` loop.

```sh
# §2, §3b, §4, §5 — pure re-analysis of committed rows, no build:
#   bench-results/inprocess-cost-2026-09-08/qfbv-24s-{off,inproc,vivify}.jsonl
#   valve decision per file: allowance = bootstrap_reference*per_mille/1000,
#   threshold = threshold_per_clause * clauses, refuse iff allowance < threshold.
#   BVE's clause count is post-subsume: cnf_clauses - subsume_clauses_subsumed
#                                        - subsume_tautologies_removed.

# §3a, §6 — an axeyum-cnf example that parse_dimacs'es each file, calls
#   TickValve::shipping(RecordingObserver::granting(u64::MAX)).grant(..) for
#   Subsume/Bve and .decompose_grant(..), prints schedule_log(), then runs
#   decompose(&formula) and prints DecomposeStats.
scripts/cargo-serialized.sh build --release -p axeyum-cnf --example <probe>
taskset -c 0-7 ./target/release/examples/<probe> /data0/measure-inproc-cost/cnf/*.cnf

# §3c:
scripts/cargo-serialized.sh build --release -p axeyum-cnf --example inprocess_pass_cost
for arm in off subsume bve preprocess; do
  taskset -c 0-7 ./target/release/examples/inprocess_pass_cost \
    /data0/measure-inproc-cost/cnf/04_simple_processors_008_006_0004.cnf 24000 "$arm"
done
```
