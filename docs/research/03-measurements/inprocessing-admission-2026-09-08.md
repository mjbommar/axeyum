# BVE was budgeted in the one counter that was not the cost

**Date:** 2026-09-08 · **Lane:** `inproc-admission` · **Host:** s4 (12th Gen
Intel i5-12600K, 6 P-cores / 4 E-cores, 16 threads, 123 GB) ·
**Corpus:** the pinned `bench-results/parity-lists/QF_BV.txt` (200 files,
sha256 `6f873e15b191`)

This acts on the finding in
[the cost decomposition](inprocessing-cost-decomposition-2026-09-08.md): 16 of
195 files spend their entire granted inprocessing slice inside a bounded
variable elimination that is then cut off unfinished — 189 s of 342 s, 55 % of
all inprocessing cost on 8 % of the files, and five of them are decided by the
baseline in 88–116 ms.

Its recommendation was "a cheap admission test". What the code turned out to
need first was different, and finding that out changed the fix.

---

## 1. The counter BVE was budgeted in was not the counter it spends

`crates/axeyum-cnf/src/bve.rs` already had a deterministic work budget:

```rust
let budget = opts.max_rounds.max(1) * 30 * (total_lits + nvars);
...
if elim.resolutions > budget { break; }
```

`elim.resolutions` counts **resolution attempts** — the `pos × neg` pairs
inside `try_eliminate`. On all 20 files that this lane measured being cut off by
the clock, that cap was never reached. It could not have been: it does not count
the work the pass actually does.

The dominant cost is `live_ids`, which walks a literal's whole occurrence list
and returns the live entries. Three things make that the hot spot, and none of
them touch `resolutions`:

* it runs **twice per variable popped** from the touched queue, before any
  resolution is attempted, including for the variables a bound then rejects;
* clause removal is **lazy**, so a dead clause's id stays in every occurrence
  list it was ever in and is re-scanned forever;
* a variable is **re-queued once per neighbour of every later elimination**, so
  a formula that eliminates 27,000 variables walks those lists a very large
  number of times.

Measured on `bench_3010` (163,348 clauses): 15,998 × the pass's own setup cost
in occurrence-list steps, for 14,890 eliminations, in 11.0 s — while the
baseline decides that query in 116 ms.

So the first change is not a gate at all. It is to **charge the work that
costs**: `BveStats::work_spent` counts occurrence-list steps (entries examined,
literals merged, resolvents compared during dedup, occurrence entries written),
with setup charged up front, and `BveOptions::work_budget` bounds it.

Two properties matter. It is deterministic — the same formula gives the same
count on any host, which a `deadline: Option<Instant>` cannot — and it is
monotone in what actually costs, so a budget in it bounds the pass rather than
one component of it. Verified on the corpus: `bench_.../0005.smt2` reports
`bve_work_spent = 166,179,877` in the calibration run and `166,179,877` in the
gated run, on different builds minutes apart.

---

## 2. What one unbudgeted sweep says about every candidate budget

`BveStats::work_at_last_elimination` records the meter reading at the pass's
last successful elimination. `work_spent − work_at_last_elimination` is spend
after the last useful action, and a budget at or above the last-elimination
reading costs that file nothing. So a single sweep with the budget disabled
prices every candidate, instead of needing one corpus sweep per candidate.

Protocol: `--release`, `scripts/inprocess-cost-sweep.sh` at the parity
protocol's 24 s / 8 GiB, pinned to one physical P-core, arm `inproc`
(subsumption + BVE), 200 of 200 rows,
`bench-results/inprocess-admission-2026-09-08/calib-24s-inproc.jsonl`.
196 files ran inprocessing; 143 reached BVE and recorded the counters.

| quantity | value |
|---|---|
| total `bve_ms` | **306.9 s** of 388.2 s of inprocessing |
| files whose BVE was cut off by the clock | **20** |
| their share of `bve_ms` | **175.7 s (57 %)** |
| spend after the last elimination | 22.9 % of all BVE work, ≈ 49 s |
| throughput, `work / bve_ms` (97 files ≥ 20 ms) | p10 170,671 · **median 460,365** · p90 1,326,285 steps/ms |

### The distribution is the finding

The point of the last elimination, in units of the pass's own setup cost:

| p50 | p75 | p90 | p95 | max |
|---:|---:|---:|---:|---:|
| **474 ×** | 4,333 × | 12,723 × | 18,418 × | 39,654 × |

**Five orders of magnitude.** There is no multiple that is simultaneously
generous to every file and frugal with any of them, so choosing one is a trade
priced in seconds against eliminations — not a threshold that separates healthy
runs from pathological ones. Anyone quoting a single "BVE costs N× setup" number
for this corpus is quoting a statistic of a distribution that has no typical
member.

### The population being cut is the one worth cutting

The 20 clock-cut files against what the **baseline** spends on the same query:

| `bve_ms` | `inprocess_ms` | baseline `off_ms` | baseline verdict | file |
|---:|---:|---:|---|---|
| 11,142 | 12,010 | **80** | unsat | `bench_464` |
| 11,186 | 11,964 | **88** | unsat | `bench_3708` |
| 11,192 | 12,000 | **90** | unsat | `bench_2598` |
| 10,733 | 12,012 | **92** | unsat | `bench_3293` |
| 11,091 | 12,050 | **93** | unsat | `bench_869` |
| 11,283 | 12,012 | **96** | sat | `bench_3218` |
| 10,997 | 12,009 | **116** | sat | `bench_3010` |
| 9,542 | 11,902 | 400 | unsat | `predicate_425` |
| 10,758 | 11,978 | 405 | unsat | `bench_2251` |
| 11,041 | 12,157 | 821 | sat | `bin_libsmbsharemodes_vc5714` |
| 9,765 | 11,771 | 1,129 | sat | `bin_libsmbsharemodes_vc6315` |
| 8,118 | 11,487 | 1,215 | sat | `bin_eventlogadm_vc331099` |
| 8,878 | 12,066 | 1,677 | sat | `bin_libsmbclient_vc1225764` |
| 9,400 | 12,030 | 1,753 | sat | `bench_12354` |
| 8,031 | 11,698 | 2,076 | sat | `bin_libmsrpc_vc1225899` |
| 5,373 | 11,121 | 3,028 | sat | `convert-jpg2gif-query-1166` |
| 2,381 | 10,689 | 4,243 | sat | `bin_eventlogadm_vc352379` |
| 97 | 11,426 | 15,134 | sat | `div3.c.50` |
| 7,372 | 11,755 | 24,112 | unknown | `tsp_rand_70_300…` |
| 7,305 | 12,019 | 24,366 | unknown | `148` |

**17 of 20 are decided by the baseline in under 4.3 s; seven in under 120 ms.**

Two of these rows say something the aggregate hides. `div3.c.50` spends 97 ms in
BVE and 11.4 s in inprocessing — **subsumption** ate that slice, so no BVE
budget can help it. And `bench_12354`'s last elimination is at 52 × setup while
it spends 5,227 ×: on that one file, 99 % of BVE's spend came after its last
useful action.

### Pricing the candidates

Derived from the calibration rows, so no extra sweep. "sec saved" charges each
file at its own measured rate; "files 100 %" is files whose last elimination
still fits the budget.

| K (× setup) | files cut | sec saved | of which clock-cut files | files keeping 100 % |
|---:|---:|---:|---:|---:|
| 500 | 77 | 265.1 s | 153.7 s | 75 |
| 1000 | 66 | 236.6 s | 137.2 s | 87 |
| **2000** | **51** | **200.4 s** | **114.6 s** | **98** |
| 5000 | 39 | 127.4 s | 71.5 s | 109 |
| 12000 | 19 | 44.3 s | 24.3 s | 126 |
| 40000 | 1 | 0.1 s | 0.0 s | 143 |

`K = 2000` is the shipped value: it declines to spend **200 s of the corpus's
307 s of BVE time**, 115 s of that on the files the clock was cutting off
anyway, while 98 of 143 files still reach their last elimination inside the
budget.

---

## 3. The admission gate, and the honest limit of it

The decision goes through `axeyum_ir::budget` rather than a second mechanism.
`bve_admission` builds one `EffortPolicy`, asks one `EffortAccount`, and lets
`Grant` say both things at once:

```
setup     = literals + 2 x variables            (BVE's own unit, exact)
reference = min(2000 x setup, 400_000 x remaining_slice_ms)
policy    = EffortPolicy::new(1000)
                .with_min_reference(reference)
                .with_init_cost(2)
Grant::Granted(b) -> BVE runs with work_budget = b.limit()
Grant::Delayed    -> BVE does not run at all
```

`with_min_reference` is what makes a pre-search round the same code path as an
in-search one: no search has happened, the numeraire reads zero, and the
bootstrap reference supplies the window — `CaDiCaL`'s `preprocessinit`, in the
primitive's own terms.

**What the gate can and cannot do here, stated plainly.** `CaDiCaL`'s
accumulate-and-delay gate works because inprocessing runs *repeatedly*: on the
delay path it does not advance the watermark, so the accrued budget grows until
it clears `thresh × clauses` (`src/limit.hpp:136-164`,
`src/probe.cpp:902-907`). We run **one** round, before search. There is nothing
to accumulate, and with a size-proportional budget the setup-recovery ratio is
`BVE_BUDGET_SETUP_MULTIPLE` by construction — a constant, so the gate could
never fire. That is a property of a one-shot round, not an oversight.

It is armed anyway, and it is not decoration, because the reference is *also*
capped by what the remaining slice can buy. The gate then fires on a real and
nameable population: a large formula meeting a slice that earlier passes have
already spent. `a_spent_slice_delays_bve_instead_of_paying_for_setup_it_cannot_use`
is the test that reaches the `Grant::Delayed` arm; without it that arm would be
unexecuted code claiming to be a safety mechanism.

**How often it fires on this corpus is reported in §4, including if the answer
is zero.**

---

## 4. Verification

Three arms, run **concurrently and pinned to distinct physical P-cores**
(CPUs 0, 2, 4; SMT siblings idle), so every arm saw the same host at the same
moment. 200 of 200 rows each,
`bench-results/inprocess-admission-2026-09-08/gated-24s-{off,inproc,vivify}.jsonl`.
The ungated row is the calibration sweep from §2 — a separate run, so its
seconds are comparable in kind but not in load.

### Verdicts were checked before any timing was read

| arm | decided | agreed with declared `:status` | **disagreed** | no declared status |
|---|---:|---:|---:|---:|
| off | 187 | 172 | **0** | 15 |
| inproc (gated) | 186 | 171 | **0** | 15 |
| inproc-vivify (gated) | 186 | 171 | **0** | 15 |

Cross-arm verdict conflicts: **0**.

### What the budget cost and bought

| arm | decided | PAR-2 | inproc s | subsume s | vivify s | **bve s** | clock-cut | work-cut | vars eliminated | literal ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| off | 187 | **806.5** | — | — | — | — | — | — | — | — |
| inproc, **ungated** | 187 | 1131.9 | 388.2 | 76.3 | — | **306.9** | 20 | — | 2,379,424 | 0.846 |
| inproc, **gated** | 186 | 945.2 | 160.8 | 66.7 | — | **90.1** | 2 | 51 | 2,197,400 | 0.844 |
| inproc-vivify, **gated** | 186 | 928.7 | 153.6 | 65.7 | 2.7 | **81.6** | **0** | 44 | **2,450,831** | **0.777** |

**BVE goes from 306.9 s to 90.1 s — 217 s, 71 % of it, not spent.** Total
inprocessing falls from 388.2 s to 160.8 s. On the 20 files the clock was
cutting off, BVE falls from 175.7 s to 50.5 s (71 %), and to 43.5 s (75 %) with
vivification.

What it costs: **7.7 % of the eliminations and 0.2 % of the shrink**
(2.38 M → 2.20 M variables; literal ratio 0.846 → 0.844). Per file, the trade is
stark — `bench_3218` drops from 11,283 ms of BVE to 826 ms and from 12,801
eliminations to 9,524, and its whole solve goes from 12,195 ms to **1,318 ms**.

**The stop is also now deterministic where it matters.** 51 files stop because
the work budget ran out, a decision that is a function of the formula alone; the
files still cut by the clock go from 20 to 2, and to 0 with vivification.
Reproduction check: `…/0005.smt2` reports `bve_work_spent = 166,179,877` in the
calibration run and `166,179,877` in the gated run, on different builds.

### The admission gate fired 0 times on this corpus

Stated plainly rather than left to be inferred. `bve_admitted == 0` on **0 of
200 files** in both gated arms (and on 1 file, `div3.c.50`, in the calibration
build, where the deliberately absurd throughput constant made the gate
equivalent to "zero milliseconds left"). §3 says why: a one-shot pre-search
round has nothing to accumulate, so the gate can only fire when an earlier pass
has already spent the slice, and on this corpus that did not happen with the
shipped constants. **The seconds in the table above were recovered by the work
budget, not by the admission test.**

### Vivification, re-measured with BVE budgeted

The 2026-09-08 decomposition found vivification made inprocessing 20 % cheaper.
It survives the budget and gets better: **2.7 s of vivification buys 8.5 s less
BVE, 253,431 more variables eliminated than the un-vivified gated arm — more
even than the ungated arm gets in 306.9 s — a literal ratio of 0.777 against
0.844, and zero files left being cut off by the clock.** Per file, on
`bench_2598`, `bench_3708`, `bench_869` and `bench_3293`, an 11,000 ms BVE that
hits its budget becomes a **27 ms** one that reaches its own fixpoint and
eliminates roughly twice as many variables. Shorter clauses mean shorter
occurrence lists, and occurrence-list scanning is what BVE spends.

So `SolverConfig::cnf_vivify` now defaults to `true`. It is a no-op unless
`cnf_inprocessing` is set, and that is still `false`, so **the default build is
unchanged**; the flip only affects callers who have already opted in.

### What it does not do, and this is the honest headline

**Inprocessing is still not a net win at 24 s, and this change does not make it
one.** Against `off` it is one decided file behind (186 vs 187) and 139 PAR-2
points worse (945.2 / 928.7 against 806.5). The gate closes 60 % of the gap the
ungated arm had (1131.9 → 928.7 against 806.5) and does not close it.

The single lost file is `div3.c.50`, and it is not a BVE story: **subsumption**
spends 10.7 s of its slice there while BVE spends 97 ms, and the file lands at
14.6 s in `off` against a 24 s budget, i.e. exactly the boundary population the
decomposition documented as flipping under load. A BVE budget cannot help it;
§5 names the pass that could.

---

## 5. What was not done

* **Subsumption is unbudgeted in the same way BVE was.** It is 18 % of
  inprocessing cost overall, but on `div3.c.50` it spends the entire 11.4 s
  slice by itself, and `simplify.rs` has no work meter at all. The same two
  changes apply to it and were not made.
* **The occurrence lists are never compacted.** Removal is lazy, so a dead
  clause id is re-scanned by every later pass over that literal's list. That is
  a large constant on exactly the files this lane is budgeting, and a budget
  hides it rather than fixing it. Whether compaction beats budgeting, or the
  two compose, was not measured.
* **The `unsat` certificate gap is untouched and out of scope.** Per
  [ADR-1750][adr] the proof is checked against the *reduced* formula, so the BVE
  link is trusted rather than checked. Nothing here changes that, and nothing
  here is enabled by default in the shipping SMT path: `SolverConfig::
  cnf_inprocessing` is still `false`.
* **A quiet-host repeat.** Both sweeps ran at host load 2–7 with other lanes
  active. The work counters are deterministic and unaffected; the seconds are
  not.

[adr]: ../09-decisions/adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md
