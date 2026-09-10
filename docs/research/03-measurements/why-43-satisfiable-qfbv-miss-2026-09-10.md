# Why 43 satisfiable QF_BV instances miss: it is not encoding size

Roadmap item 3.9 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md),
measured 2026-09-10 on `af83dd929`. Lane B1.

The item named three candidate causes — **encoding size, search, admission** —
and asked which. The answer is that all three appear, in disjoint sub-classes,
and **the largest one is none of them**: on a measurable part of this class we
compute the right answer and then throw it away.

## The four findings, each with its number

1. **We decide instances we report as `unknown`.** Nine instances, including two
   real SMT-LIB files, return `unknown` at a 10 s budget after spending 29-43 s,
   and return **`sat`** at a 300 s budget after spending the *same* time. The
   search never stopped; only the verdict was discarded. `sat_bv_backend.rs:327`
   re-reads the clock after `primary_sat_search` returns and converts any result
   to `unknown` when the deadline has passed.
2. **The wall-clock budget is not enforced during that search.** The CDCL core
   tests its deadline every `DEADLINE_CHECK_INTERVAL = 1_024` **conflicts**
   (`proof_sat.rs:62`, used at `:3453`), and on this class the whole search is
   **fewer than 256 conflicts** at **28-51 conflicts/second**. The test can never
   fire. Measured overrun of a 10 s budget: **1.15x to 8.01x**.
3. **Encoding size is refuted as the cause, by our own data.**
   `bvwide-mul-w01024` has **8,891,930** CNF clauses and decides in 5.9 s.
   `bvwide-addcmp-w12288` has **430,038** — 20.7x fewer — and does not decide.
   At the `addcmp` frontier, lowering plus CNF construction is **56 ms of
   5,385 ms (1.0%)**.
4. **Admission over-refuses, measurably.** `ABSOLUTE_CLAUSE_CEILING`
   (`sat_bv_backend.rs:2154`, 64,000,000) refuses `bvwide-mul-w02048` on a
   *projected* **100,681,731** clauses. Its real encoding is **35,609,626** —
   the estimator is **2.83x pessimistic** and the instance is **1.80x under** the
   cap. With the ceiling raised it decides **`sat` in 41.0 s**.

And one negative result the roadmap asked for by name:

5. **`BitLoweringMode::DemandSliced` removes ZERO gates on this class** and costs
   **51.6x** more lowering time on the family that dominates it. Do not turn it
   on. Item 3.3's carve-out 1 is closed as DO NOT BUILD.

## What was measured, and the population caveat I owe

**I could not reproduce item 3.1's 166-instance sample and did not try to
inherit it.** Re-running its stated recipe (`find`, five size bands, up to 120
files each at `random.seed(20260910)`, keep `:status sat` from the first 8 KB,
drop over 200 MB) over the same NAS division gives 600 drawn, **200** satisfiable
and kept — not the 168/166 recorded. The `find` order, the sort, and the exact
`random` call are not pinned tightly enough in either note to re-derive the same
draw. The division size does match exactly (46,191 files), so the population is
the same; only the draw is not.

So the miss set here was reconstructed **by name** from the per-file tables in
[`rewrite-depth-gap-2026-09-10.md`](rewrite-depth-gap-2026-09-10.md), which name
42 of the 43 across three tables. All 42 resolve on the NAS and all 42 carry
`:status sat`. **Six of the 42 basenames are ambiguous** — `bench_1008.smt2`
exists in seven `sage*/` directories at sizes from 1,132 B to 6,405,553 B — and
for those I took the `Sage2/` copy. Any claim below about a `bench_*` file is
therefore about the `Sage2` copy, which may not be the copy item 3.1 drew.

Of those 42 I measured the **9 that are 1 MB or smaller**. The other 33 are
3-90 MB; running them was not attempted here. Everything else below is measured
on the width-graduated corpus committed with this note, whose `:status sat` is
established by an explicit witness the generator checks in exact integer
arithmetic before emission — so it depends on no solver at all.

Instrument: `crates/axeyum-bench/examples/qfbv_sat_attribution.rs`, release
build, **one file per process** under `timeout -s KILL` and `ulimit -v`. A
killed process prints no row, and the harness records that as `KILLED_rc<n>`
rather than as a measured zero. Shared dev box, load average **1.2-5.9**;
`uptime` was read around every run and load-sensitive numbers are flagged where
it matters.

## Measurement 1 — where the budget actually goes

`corpus/public-curated/synthetic/QF_BV/width-graduated/`, cold `SatBvBackend`,
10 s budget, release. `blast` is `bit_blast_ms`, `cnf` is `cnf_encode_ms`, both
straight out of `SolveStats`.

### `bvwide-addcmp` — the `ndist.b` shape, linear encoding

| width | verdict | total ms | blast | cnf | solve | AND gates | CNF clauses |
|------:|---------|---------:|------:|----:|------:|----------:|------------:|
| 64 | sat | 3 | 0 | 0 | 3 | 1,137 | 2,198 |
| 512 | sat | 46 | 1 | 3 | 42 | 9,201 | 17,878 |
| 1,024 | sat | 132 | 2 | 5 | 125 | 18,417 | 35,798 |
| 2,048 | sat | 426 | 5 | 16 | 405 | 36,849 | 71,638 |
| 4,096 | sat | 1,472 | 6 | 21 | 1,445 | 73,713 | 143,318 |
| 6,144 | sat | 3,093 | 12 | 31 | 3,050 | 110,577 | 214,998 |
| **8,192** | **sat** | **5,385** | **12** | **44** | **5,329** | 147,441 | 286,678 |
| 12,288 | unknown | 11,544 | 23 | 65 | 11,456 | 221,169 | 430,038 |
| 16,384 | unknown | 19,980 | 27 | 91 | 19,862 | 294,897 | 573,398 |
| 20,000 | unknown | 29,434 | 36 | 109 | 29,289 | 359,985 | 699,958 |
| 24,576 | unknown | 49,043 | 53 | 139 | 48,851 | 442,353 | 860,118 |
| 32,768 | unknown | 80,096 | 81 | 235 | 79,780 | 589,809 | 1,146,838 |

**Decide-frontier: width 8,192.** Two rates, and they are not the same rate:

- the circuit is **linear** in the width — 17.77 gates/bit at 64, 18.00 at
  32,768, over a 512x range;
- the wall clock is **~w^1.8**: 1,024 -> 8,192 is 8x the width and 40.8x the
  time; 4,096 -> 32,768 is 8x and 54.4x.

Lowering plus CNF construction is **1.04%** of the budget at the frontier and
**0.39%** at width 32,768 — it gets *less* relevant as the instance gets harder.
Every millisecond that matters is in the SAT search.

### `bvwide-mul` — a single wide multiply, quadratic encoding

| width | verdict | total ms | blast | cnf | solve | AND gates | CNF clauses |
|------:|---------|---------:|------:|----:|------:|----------:|------------:|
| 256 | sat | 206 | 29 | 91 | 86 | 326,149 | 551,834 |
| 512 | sat | 1,078 | 158 | 424 | 496 | 1,307,653 | 2,217,754 |
| 768 | sat | 2,991 | 488 | 1,048 | 1,455 | 2,944,517 | 4,997,786 |
| **1,024** | **sat** | **5,935** | **814** | **1,999** | **3,122** | 5,236,741 | **8,891,930** |
| 2,048 | unknown | 0 | — | — | — | — | — |
| 4,096 | unknown | 0 | — | — | — | — | — |

**Decide-frontier: width 1,024**, and this family is genuinely encoding-bound —
**2,813 ms of 5,935 ms (47.4%)** is lowering plus CNF. Widths 2,048 and 4,096 are
refused before lowering (measurement 4).

### The comparison that settles the question

| instance | CNF clauses | verdict at 10 s |
|---|---:|---|
| `bvwide-mul-w01024` | **8,891,930** | **sat**, 5.9 s |
| `bvwide-addcmp-w12288` | **430,038** | unknown |

A formula **20.7x larger** is solved; the smaller one is not. Encoding size is
not what separates the instances we decide from the ones we miss. Two cost curves
over one knob was the point of building two families.

## Measurement 2 — the search is a few hundred conflicts, at tens per second

`SolverConfig::resource_limit` reaches the CDCL core as `max_conflicts`
unchanged (`sat_bv_backend.rs:2402`), so timing a run at `max_conflicts = N`
measures the wall clock to reach N conflicts.

| max_conflicts | `addcmp-w08192` (we decide it) | `addcmp-w12288` (we miss it) |
|--------------:|-------------------------------|------------------------------|
| 0 | budget exhausted, solve 17 ms | budget exhausted, solve 28 ms |
| 1 | exhausted, 215 ms | exhausted, 472 ms |
| 4 | exhausted, 555 ms | exhausted, 1,257 ms |
| 16 | exhausted, 659 ms | exhausted, 1,432 ms |
| 64 | exhausted, 2,321 ms | exhausted, 5,164 ms |
| 256 | **sat, 4,993 ms** | not decided, 11,052 ms |
| 1,024 | **sat, 5,093 ms** | not decided, 10,892 ms |

Three things fall out:

- **The whole successful search is between 65 and 256 conflicts.** This is not a
  hard search in the usual sense — it is a small number of very expensive ones.
- **Rate: 28-51 conflicts/second** at width 8,192, **12-23** at width 12,288.
  Reference solvers report `10^4`-`10^6`. (`pbls.rs`'s flip rate was found 2-3
  orders low in item 3.1; this is the same shape one layer down, and this time
  it is on the path we ship.)
- **Cost per conflict is quadratic in the width**: 36.3 ms at width 8,192 and
  80.7 ms at 12,288 (64 conflicts each) — a 1.5x width for a 2.22x cost,
  exponent 1.97. That is where the `w^1.8` in measurement 1 comes from.

**Therefore the deadline test cannot fire.** It runs when
`self.conflicts.is_multiple_of(DEADLINE_CHECK_INTERVAL)` with the interval at
**1,024 conflicts** (`proof_sat.rs:3453`). At 51 conflicts/s the first check
after conflict zero would land 20 s into a 10 s budget, and the search finishes
long before conflict 1,024 anyway. The cadence's own docstring says it is
"deterministic w.r.t. the search and cheap" — both true, and both irrelevant on
a formula whose search is propagation-bound rather than conflict-bound.

## Measurement 3 — the answer is computed and discarded

If the search runs to completion regardless of the budget, then the same
instance must decide once the budget is raised past its *unchanged* search time.
It does, on every instance tried — nine of nine.

| instance | arm | 10 s budget | 300 s budget |
|---|---|---|---|
| `addcmp-w12288` | backend | unknown, 11,476 ms (solve 11,381) | **sat**, 11,175 (solve 11,085) |
| `addcmp-w16384` | backend | unknown, 19,137 (19,016) | **sat**, 19,081 (18,949) |
| `addcmp-w20000` | backend | unknown, 28,270 (28,114) | **sat**, 28,038 (27,874) |
| `pspace/ndist.b.20000` | backend | unknown, 29,547 (29,398) | **sat**, 28,453 (28,277) |
| `pspace/ndist.b.20000` | **front door** | unknown, 28,956 | **sat**, 32,163 |
| `pspace/ndist.b.24491` | backend | unknown, 43,408 (43,219) | **sat**, 41,640 (41,432) |
| `pspace/ndist.b.29980` | backend | unknown, 66,314 (66,057) | **sat**, 75,165 (74,876) |
| `pspace/ndist.b.29980` | **front door** | unknown, 71,296 | **sat**, 72,868 |
| `Sage2/bench_15255` | backend | unknown, 29,626 (27,598) | **sat**, 31,000 (28,223) |

The search time is the same in both arms to within run-to-run noise on a shared
box. The `ndist.b.29980` backend pair (66.3 s vs 75.2 s) is the one row where the
spread exceeds noise, and load moved between the runs.

Two of these are **real SMT-LIB benchmarks solved through the shipping front
door**, and `Sage2/bench_15255` is not a `pspace` file — so this is not an
artifact of the width family.

The mechanism is one `if` (`sat_bv_backend.rs:327-332`):

```rust
let mut sat_result = primary_sat_search(config, solve_formula, deadline, &mut stats, reduction);
stats.solve = solve_start.elapsed();
if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
    return Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Timeout,
        detail: "pure-Rust BV backend timeout after SAT search".to_owned(),
    }));
}
```

The overrun has already been paid at that point; discarding the result does not
recover it. And keeping it costs no assurance: every `sat` on this path is lifted
and **replayed against the original terms** before it is returned, so a late
`sat` is exactly as checked as a timely one. What a caller loses is the promise
that a 10 s budget returns in 10 s — which was already lost, by 1.15x to 8.01x:

| instance (10 s budget) | returned after | overrun |
|---|---:|---:|
| `addcmp-w12288` | 11.5 s | 1.15x |
| `addcmp-w16384` | 19.1 s | 1.91x |
| `addcmp-w20000` | 28.3 s | 2.83x |
| `addcmp-w24576` | 49.0 s | 4.90x |
| `addcmp-w32768` | 80.1 s | 8.01x |
| `pspace/ndist.b.29980` (front door) | 71.3 s | 7.13x |

These are two separate defects and they want two separate fixes. Making the
deadline real (a time-based or propagation-based cadence, not a conflict one)
makes the budget mean something and returns `unknown` at 10 s honestly. Keeping a
late result converts an overrun we are already paying into a verdict. They
compose; neither subsumes the other.

## Measurement 4 — the admission estimator is 2.83x pessimistic

`bvwide-mul-w02048`, cold backend, 120 s budget:

| `cnf_clause_budget` | verdict | total ms | blast | cnf | solve | real CNF clauses |
|---|---|---:|---:|---:|---:|---:|
| default (64,000,000) | unknown | 0 | — | — | — | — |
| 200,000,000 | **sat** | 40,980 | 3,075 | 8,888 | 28,370 | **35,609,626** |

The default refuses it with `estimated 100681731 CNF clauses before lowering
exceeds budget 64000000 (oversized encoding refused gracefully)`. The real
encoding is **35,609,626 clauses — 1.80x under the cap it was refused against**,
and the estimator over-shot by **2.83x**.

`estimate_blast_clauses` (`sat_bv_backend.rs:2163`) charges `bvmul` at `~8w²`
gates and then `~3x` for Tseitin. Its own comment records that charging only `w²`
under-estimated by ~8x and let a 4,096-bit `bvmul` OOM during lowering — so the
8x was a deliberate, sound correction. What has not been re-measured since is the
`~3x` Tseitin multiplier on top of it, and on this shape the composed estimate is
2.83x high. **The refusal is graceful and sound; it is simply firing on an
instance we can solve.** This is the one place in this note where the answer to
"is it admission?" is yes.

For completeness, the *other* admission gates on this path are inert:
`node_budget` and `cnf_clause_budget` are `None` in `SolverConfig::default()`
(`backend.rs:380`) and are never assigned anywhere in `auto.rs`, `smtlib.rs` or
`solver.rs`, so `ABSOLUTE_CLAUSE_CEILING` is the only one that ever fires.

### The item's third question: are the 19 an admission gate we chose?

**No.** Item 3.3 reports 19 of the 43 where "the front door never reaches the
solver". Their reason strings are `preprocessing timeout before reduced dispatch`
(`auto.rs:1953`, `:1958`) and `preprocessed dispatch timeout after reduced solve`
(`auto.rs:2408`) — **timeouts, not admission refusals**. No `UnknownKind::NodeBudget`
or `EncodingBudget` is involved. There is no chosen size gate stopping them;
preprocessing simply spends the budget. (I did not re-measure those 19 files
here; see "what I did not measure".)

## Measurement 5 — `DemandSliced` is measured neutral, and expensive

Item 3.3 named `BitLoweringMode::DemandSliced` (`backend.rs:79`, defaulted to
`Eager` at `:395`) as its highest-value carve-out. Measured A/B, same binary,
same files, 10 s budget:

| file | mode | verdict | total ms | blast | cnf | AND gates | CNF clauses |
|---|---|---|---:|---:|---:|---:|---:|
| `addcmp-w04096` | `Eager` | sat | 1,391 | **10** | 21 | 73,713 | 143,318 |
| `addcmp-w04096` | `DemandSliced` | sat | 1,892 | **516** | 20 | 73,713 | 143,318 |
| `mul-w00512` | `Eager` | sat | 1,023 | 158 | 388 | 1,307,653 | 2,217,754 |
| `mul-w00512` | `DemandSliced` | sat | 1,003 | 143 | 382 | 1,307,653 | 2,217,754 |

**The circuits are byte-identical.** Zero gates removed, zero clauses removed, on
both families. On `addcmp` the demand analysis costs **506 ms against a 10 ms
lowering — 51.6x — and 36% of the total wall clock**, bought for nothing.

The mechanism is in ADR-0157's own text, and it is structural rather than a
tuning miss. Its exact-propagation class covers Boolean and BV bitwise
operators, `extract`, `concat`, extensions, constant rotations, `ite` and
`FpFromBits`. **"Every other operator is a conservative barrier: demanding any
output bit demands every bit of every operand."** Every operator in this class —
`bvuge`, `bvule`, `bvadd`, `bvmul`, `=` — is on the barrier side. There is
nothing to slice, so there is nothing to gain, and the analysis still runs.

**The reason the default is off still holds, and it now holds for a second,
independent reason.** ADR-0157's Glaurung measurement rejected it because the
backward analysis cost more than the circuit it avoided (1.42x -> 4.49x Z3, bit
blast 47% -> 83%). That was a *different corpus*, so "the default is stale" was a
live hypothesis worth testing — it is the recurring shape in this codebase. It is
not stale: on the class item 3.9 is about, the analysis avoids **nothing at all**
and the same cost reappears. Item 3.3's carve-out 1 is closed **DO NOT BUILD**.

## The width threshold, stated plainly

The item asked: if bit-blasting simply cannot reach these widths, say what the
threshold is. **It is not a width threshold, and that is the finding.**

At a 10 s budget in the release/backend frame the frontier is width **8,192** for
`addcmp` and **1,024** for `mul`. But those are budget artefacts, not capability
limits: at 300 s the `addcmp` family decides at least to width **29,980** (the
whole real `ndist.b` family), and `mul` decides at width **2,048** once the
admission estimator is corrected. Nothing in the measured range is beyond
bit-blasting. What the widths cost is **time, quadratically per conflict** —

> circuit size ~ `w^1.0`, solve time ~ `w^1.8`, cost per conflict ~ `w^2.0`

— and the ceiling we hit is our own clock, not the method's. **Bit-blasting work
on this class is worth doing**, and the first three items are cheap.

## What to do, in value order

1. **Keep a completed result that arrives late** (`sat_bv_backend.rs:327-332`).
   Nine of nine instances flip `unknown` -> `sat`. The work is already paid for
   and the `sat` is replay-checked either way. Needs a decision recorded: the
   budget stops being an upper bound on wall time, which it already was not.
2. **Make the deadline cadence time-bearing, not conflict-bearing**
   (`proof_sat.rs:62`, `:3453`). A search that propagates more than it conflicts
   currently never reads the clock. A propagation-count cadence beside the
   conflict one keeps the determinism the current design is protecting.
   Overruns measured at 1.15x-8.01x.
3. **Re-measure the Tseitin multiplier in `estimate_blast_clauses`**
   (`sat_bv_backend.rs:2163`). Measured 2.83x high on `bvmul`; correcting it
   admits `bvwide-mul-w02048`, which we then solve in 41 s. Do NOT simply raise
   `ABSOLUTE_CLAUSE_CEILING` — the 8x gate charge exists because a 4,096-bit
   `bvmul` OOM'd during lowering, and the cap is what makes the refusal graceful.
4. **The conflict rate itself** — 28-51/s where reference solvers report
   `10^4`-`10^6`, and cost per conflict quadratic in the width. This is the big
   one and the least bounded; it wants its own item and a profile, not a guess.
   The shape to look at first is that these searches are propagation-bound: the
   `addcmp` circuit is a `w`-stage ripple-carry chain, so one propagation
   sweep is `O(w)` and the fixpoint is reached `O(w)` times.
5. **Not `DemandSliced`, and not more rewrite rules** (measurement 5, and item
   3.3).

## What I did not measure

- **The other 33 of the 42 named misses.** They are 3-90 MB; only the 9 at 1 MB
  or under were run. The 17 that item 3.3 found cannot finish word-level
  rewriting in 300 s / 20 GB are all in that unrun set, and nothing here revisits
  them.
- **The 19 that never reach the solver.** Their reason strings are read from
  source above, not re-measured. Whether a real deadline (item 2 above) changes
  what preprocessing does with its budget is untested.
- **Item 3.1's exact sample.** Not reproducible from either note; see the
  population caveat. Every "43" in this document is item 3.1's number, quoted,
  not re-derived.
- **Any head-to-head.** No z3, cvc5 or Bitwuzla was run. That these instances are
  easy for other solvers is the SMT-LIB `pspace` family's stated purpose, not
  something measured here.
- **Whether keeping a late result is safe under every route.** It is sound for
  `sat` on this path (replay against the original terms), and I did not examine
  the `unsat` side, the proof-carrying route, or the incremental façade. Item 1
  above needs that examination before it lands.
- **Any source change on the shipping path.** Nothing in `crates/*/src` was
  modified for this note beyond the new bench example; all four levers were
  exercised through existing `SolverConfig` fields.
- **A comparable capability-frontier reading.** `progress_frontier` was run
  (`taskset -c 0-7`, `--test-threads=1`) and all 12 tests passed, but the
  emitted `bench_results/frontier/bv_reduction.json` carries
  `"comparable": false, "ratchetable": false` at `load_start 7.39` — an
  **ADVISORY ONLY** run in which the ratchet is not enforced, so its green does
  not rule a regression out. Its artifacts were restored rather than committed,
  per the rule against recording a frontier measured under one's own heavy
  sweeps. Nothing in this lane's diff touches a solve path, so there is no
  mechanism by which it could move that number.
- **Whether the conflict rate is width-specific.** Measured on two synthetic
  shapes and confirmed on `pspace` and one `Sage2` file. Whether a 64-bit
  industrial QF_BV instance shows the same per-conflict cost was not tested.

## Reproducing

```sh
python3 scripts/gen-graduated-qfbv-width.py          # re-emits the corpus byte-for-byte
cargo build --release -p axeyum-bench --example qfbv_sat_attribution

B=target/release/examples/qfbv_sat_attribution
G=corpus/public-curated/synthetic/QF_BV/width-graduated

# measurement 1: per-stage attribution along the ladder
for f in "$G"/bvwide-addcmp-*.smt2; do "$B" "$f" 10000 backend; done

# measurement 2: wall clock to reach N conflicts
for n in 0 1 4 16 64 256 1024; do "$B" "$G/bvwide-addcmp-w12288.smt2" 10000 backend "$n"; done

# measurement 3: the same instance at two budgets
"$B" "$G/bvwide-addcmp-w12288.smt2"  10000 backend
"$B" "$G/bvwide-addcmp-w12288.smt2" 300000 backend

# measurement 4: the admission estimate against the real encoding
"$B" "$G/bvwide-mul-w02048.smt2" 120000 backend - -
"$B" "$G/bvwide-mul-w02048.smt2" 120000 backend - 200000000

# measurement 5: the DemandSliced A/B
"$B" "$G/bvwide-addcmp-w04096.smt2" 10000 backend
"$B" "$G/bvwide-addcmp-w04096.smt2" 10000 backend-sliced
```

Run each under `timeout -s KILL` and `ulimit -v`; the probe deliberately has no
internal bound, because the failure mode being measured is a process that does
not stop when it was told to.

The frontier is gated by
[`crates/axeyum-solver/tests/qfbv_width_frontier.rs`](../../../crates/axeyum-solver/tests/qfbv_width_frontier.rs).
Its floors are calibrated to the **debug, front-door** frame the gate runs in
(frontier 1,024 for both families), not the release/backend frame the tables
above use (8,192 and 1,024) — a frontier is a function of the budget, the build
profile *and* the entry point, and the first draft of that file set its floor
from the wrong one and went red.
