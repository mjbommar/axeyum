# ADR-2055: the tableau is the memory, the round trip is 14 % of it, and capping the tableau costs eighteen clean exits

Status: accepted
Index-summary: [ADR-2045] handed off 74 of 93 undecided `QF_LRA` rows on one route and named two unpriced allocations on it. Both are now **priced by measurement** at all 74 rows. The `lra.rs:944` round trip is **real** — the dense `m × nvars` matrix's only consumer is `densify_to_sparse` — and it is **14.0 % of the two allocations** (12.2 % as measured resident-set growth), rising to **30.2 % of the bytes an aborting process actually held**. It is **not** the 5.07 GiB. The **tableau** is: `m × (nvars+m)`, a **median 19,198,877 cells against MAX_TABLEAU_CELLS = 4,000,000** (over by a median **69×**, max **1140×**, on 46 of 74 rows), holding a median **34,555 nonzeros** — **0.0288 % dense**, a structure ~3,500× larger than its data. The two halves answer differently and averaging hides it: the **40 abort** rows are building tableaux needing a median **10.53 GiB** (max 135.94) against an 8 GiB ceiling, while the **34 clock** rows need a median **0.20 GiB** and are not memory-bound at all. **15 of the 40 aborts die INSIDE the round-trip loop**, never reporting `m` — the lever's best case, so they were re-run under the sparse arm where the row build is O(nnz) and cannot be the killer: they then need a **median 228.83 GiB tableau** and **0 of 15 fit**. A/B over the whole board, ONE binary under FIVE environment values, arms back to back per file on a pinned core with rotating order, base re-deriving **107 of 200** exactly: **sparse rows are +0, gains 0, losses 0, flips 0, 0 new aborts**, against a **row-level noise floor of 0 of 200** measured in the same run by a repeated base arm, soundness 0 disagreements at a comparable denominator of 97. **They ship, and ship as the ONLY path** — a lever defaulting `Off` leaves the new path exercised by no gate, which is why the three z3 differential fuzzes (5 / 1 / 1) now mean something. **The cell cap does NOT ship, and not for the pre-registered reason.** R11 allowed "it belongs there and buys 0 verdicts"; the measurement is worse — net **−1** and **18 rows that terminate cleanly become `rc=134` process aborts**, one of them answering `sat`. Mechanism measured, not guessed: base builds **11 tableaux** and spends **20,086 ms of 24,000** in them and exits `0`; the cap arm builds **0**, declines **once**, and dies on `"memory allocation of 427680 bytes failed"`. One entry, not thousands — the loop does not run away. **The unpriced allocation was accidentally load-bearing: the enormous tableau was a sink absorbing the budget a worse route would otherwise spend.** Control `QF_S` **186 → 186** and exposure `QF_UFLRA` **148 → 148**, both **run**, both zero, both shown non-vacuous (the changed function executes **559 times across 12 `QF_UFLRA` rows** and **0 times** in `QF_S`, whose rows bind on `fd:source-string`/`dl-online` at 1–391 ms). Two corrections to the handoff, both the same shape as ADR-2045's own finding one level down: its clock bucket is **26 of 34 dense-engine-bound, not 34 of 34** — 7 rows are bound by the **Boolean skeleton** (`cube_simplex_ms` is 13.7 % of budget on `sc-7`, `skeleton_ms` is 84.2 %) because a **call counter says a thing happened, not that it dominated**; and the named capability wall is **two different failures behind one sentence** — over its 23 rows, **16 are a model that WAS built and does not replay**, 6 are no model reconstructed (all 6 the simplex declining), and **0** are the `i128` witness boundary that was the leading hypothesis.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2045] measured `QF_LRA` at 107 of 200 against z3's 166 and censused all 93
undecided rows to **74 on one route** — the offline dense-matrix LRA engine, 40
aborting on its allocation and 34 exhausting the clock — at a **5.07 GiB median
peak RSS**. It left two allocations on that path *named but unpriced*, neither
needing a config change:

- `simplex::MAX_TABLEAU_CELLS = 4_000_000` is not consulted by `feasible_within`;
- `lra.rs:944` materialises each sparse `LinExpr` into `vec![Rational::zero(); nvars]`,
  which `Tableau::new` immediately re-sparsifies.

This lane prices both and decides what to do about them.

Branch base: `git merge-base main HEAD` is
`91c721f8eda678e40124e089d6761ce3d3d02f94`, which **is** local `main`'s HEAD.

Rules were [pre-registered](../../../bench-results/lra-dense-20260914/PREREGISTRATION.md)
in their own commit (`7158ae5ee`) before the profile ran, before the A/B existed
and before any code change existed.

Compute: **6 pinned pairs** — s5 `(0,8)`/`(1,9)`, s6 `(0,8)`/`(1,9)`,
s7 `(0,8)`/`(1,9)`, all three hosts at load average 0.00–0.09 at launch. Two
shards per host, not three, for ADR-2045's measured reason.

**The prize is 49, not 50.** ADR-2045's `Timeout/ResourceLimit` bucket carries
one lazy-SMT wall-clock row its own census attributes to another engine.
Excluding it, the dense route is `40 + 34 = 74` with `20 + 29 = 49` addressable.
"50 of 61 = 82 %" becomes **49 of 61 = 80 %**; the finding is unchanged.

## 1. Where the memory actually goes — profiled, not reasoned

`AXEYUM_LRADENSEPROBE=1` reports the resident set at four points on the route.
The shape and the resident set are both printed at `feasible_within-entry`,
which is **before** the tableau is allocated, so a row that dies *in* that
allocation still reports everything needed to price it — which is why this runs
at the board's own `ulimit -v 8G` rather than needing 24 GiB of headroom.

Two independent estimates are carried side by side, because either alone could
be wrong in a way the other is not: **measured** resident-set deltas, and
**arithmetic** from `cells × 32 bytes` (`Rational` is two `i128`s, `Copy`). They
agree.

| over all 74 rows | median |
|---|---:|
| `nvars` | 1,778 |
| `m` (constraints) | 10,514 |
| **`nnz` (the actual data)** | **34,555** |
| `dense_cells` = `m × nvars` (the round trip) | 9,241,988 |
| **`tableau_cells` = `m × (nvars+m)`** | **19,198,877** |

```text
round-trip share, ARITHMETIC (cells x 32B):  n=59  median 14.0 %  min  3.0 %  max 19.3 %
round-trip share, MEASURED   (RSS deltas) :  n=31  median 12.2 %  min  0.2 %  max 18.1 %
```

**The round trip is real and it is not the 5.07 GiB.** The tableau is.

And the tableau is the wrong data structure by three and a half orders of
magnitude:

```text
tableau DENSITY (nnz / cells): median 0.0288 %   min 0.0056 %   max 0.2861 %
rows whose tableau exceeds MAX_TABLEAU_CELLS (4,000,000): 46 of 74
  over by: median 69.2x   min 1.1x   max 1140.4x
```

A median 34,555 nonzeros held in 19.2 million cells. That is z3's 52.92 MB
against our 5.07 GiB, in the one number that explains it.

### The two halves answer differently, and averaging them hides it

| half | n | round trip, as a share of the bytes the process ACTUALLY held | the tableau it was building needs |
|---|---:|---:|---|
| **ABORT** (`rc=134`) | 40 | median **30.2 %** (max 96.4) | median **10.53 GiB**, max **135.94** |
| **CLOCK** (terminated) | 34 | median 12.2 % | median **0.20 GiB** |

The clock rows are **not memory-bound at all**. The abort rows are building
something a factor of 1.3 to 17 beyond the whole ceiling, so removing a 30 %
allocation cannot reach them.

### The lever's best case, measured rather than assumed

**15 of the 40 aborting rows die INSIDE the round-trip loop**, before it
completes: they report `simplex-fallback-entry` and never reach
`dense-rows-built`, so `m` is never printed and they were **excluded from the
prediction above** — while being exactly the rows where the round trip is most
likely to decide the outcome. Leaving them out would have left the lever's best
case unmeasured, so they were re-run under `AXEYUM_LRA_SPARSE_ROWS=1`, where the
row build is `O(nnz)` and cannot be the killer:

```text
reached feasible_within under the sparse arm : 15 of 15
STILL ABORT                                  : 14
terminate cleanly                            :  1
DECIDED                                      :  0
the tableau they then need: median 228.83 GiB   min 55.45   max 2348.06
tableau alone fits the 8 GiB ceiling on 0 of 15 rows
```

These rows have `m` between 38,292 and 244,460 — `m ≫ nvars`, so the tableau is
essentially `m²`. **0 of 15.**

## 2. Two corrections to the handoff, both its own finding one level down

### 2.1 The clock bucket is 26 of 34, not 34 of 34

ADR-2045 split its `Timeout/ResourceLimit` bucket on the engines' own counters
and concluded *"34 of 34 rows have `cube_matrices=0` and `cube_simplex_calls>0`;
Fourier–Motzkin never ran"*, labelling the bucket **"dense simplex spent the
budget"**. The first half is a measurement and it holds. The second is an
inference from a **call counter**, and a call counter says a thing happened, not
that it dominated.

On milliseconds, over the 34 rows that survive to print a trace:

```text
DENSE-ENGINE-BOUND (cube_simplex_ms top AND >= half):  26 of 34
SKELETON-BOUND:                                         7 of 34   (1 mixed)

cube_simplex_ms    median 63.3 %   min 13.7 %   max 99.7 %
skeleton_ms        median 33.3 %   min  0.0 %   max 84.2 %
```

The 7 are the `sc-*.base.cvc` family and `p7-driverlogNumeric_s8`. On `sc-7` the
dense engine gets **13.7 %** of the budget and the **Boolean skeleton takes
84.2 %**: the lazy-SMT loop emits 1,483 cubes the theory refutes one at a time.
A lane sizing the dense engine from the bucket would be sizing 7 rows that are a
different problem.

**A trap worth recording, because this ADR fell into it first.** These counters
**nest**:

```text
accounted_ms = skeleton_ms + theory_ms + core_ms + pending_round_ms
theory_ms   >= cube_collect_ms + cube_fm_ms + cube_simplex_ms
```

Verified against a raw trace: `23 759 = 3 170 + 20 575 + 13 + 0`, and
`20 575 >= 796 + 0 + 19 754`. Read as siblings they charge the dense engine's
time to the theory twice, and the first run of this analysis reported **0 of 34**
dense-engine-bound. The disjoint decomposition is derived and checked in
`scripts/attrib.py`.

### 2.2 The capability wall is two failures behind one sentence

ADR-2045 named *"online CDCL(T) LRA model did not replay (arithmetic outside the
incremental engine)"* as the work — 19 of 21 rows reaching the engine die on it.
That one sentence is produced at **two** call sites in `lra_theory.rs` that
demand opposite work, and the first splits five ways inside
`lra_online::model`. `AXEYUM_LRAMODELPROBE=1` separates them. Over the **23**
rows whose census cause is that string:

| rows | site |
|---:|---|
| **16** | `lra_theory:model-built-but-does-not-replay` |
| 6 | `lra_theory:no-model-reconstructed` — all 6 `simplex-declined` |
| **0** | `feasible-but-witness-out-of-i128` |

**The leading hypothesis was refuted.** `Incremental::point` narrows to `i128`
and drops the whole witness if one coordinate does not fit — the boundary
`simplex.rs` pins as roadmap item 2.3, and a query that IS feasible and gets
declined anyway. It fires on **nothing** here.

The dominant case is not the engine failing to represent the arithmetic. It is a
model the engine **does** produce, which then does not satisfy the original
assertions. That is an encoding or skeleton-leaf-completion gap, and the
sentence as written sends a reader to the wrong half.

## 3. The A/B

Interleaved per file, five arms back to back on the same file on the same pinned
core, order rotating with the file index, 6 pinned pairs, 24 s / 8 GiB, **one
binary under five environment values**. Polarity: **A = base, both levers
UNSET — what ships today.**

**R0 holds**: the base arm re-derives **107 of 200**, reproducing the board
exactly, so this is measured against a live baseline and not an inherited
number.

```text
 arm  decided  net vs A  aborts    what it is
   A      107        +0      41    base
  A2      107        +0      41    base REPEATED  -- the noise floor
   B      107        +0      41    sparse rows
   C      106        -1      59    cell cap
   D      106        -1      58    both
```

**Noise floor, measured in this run at ROW level**: A and A2 are the identical
configuration on the same file on the same core, and they differ on **0 of 200
rows by verdict and 0 by exit status**. So `+0` is a real null.

**Soundness vs declared `:status`, with the comparable denominator printed
beside every zero**: A/A2/B **comparable = 97, disagreements = 0**; C/D
comparable = 96, disagreements = 0.

**There are 0 gains, so the three-authority check on new verdicts has an empty
subject and a comparable denominator of 0** — printed rather than reported as a
zero disagreement count. Gain rate 95 % Wilson interval over 200 rows:
**[0.00 %, 1.88 %]**.

### The cap is not neutral. It is a LOSS, and not the one anticipated.

R11 pre-registered *"the cap belongs in `feasible_within` and it buys 0
verdicts"* as an acceptable, publishable outcome. **The measurement is worse than
that**, and the damage is almost entirely invisible in the verdict column:

> **18 rows that terminate cleanly in the base become `rc=134` process aborts
> under the cap**, and one of them — `ecoliMILPglycerolYices3-50000.smt2` — was
> answering **`sat`**.

Mechanism, measured rather than inferred, on `Gcd.bpl_Iteration1_Lasso_7`:

```text
base : 11 offline entries, 11 tableaux built, cube_simplex_ms=20086 of 24000
       -> unknown, rc 0
cap  :  1 offline entry,    0 tableaux built, 1 cap decline
       -> "memory allocation of 427680 bytes failed", rc 134
```

One entry, not thousands, so this is **not** a runaway loop — that hypothesis
was written down before the measurement and refuted by it. The dense tableau was
consuming **20 of the 24 seconds**. Declining it hands the query its whole budget
back, and the route that then runs allocates past the 8 GiB ceiling.

**The unpriced allocation was accidentally load-bearing.** The enormous tableau
was acting as a sink that kept these queries away from a worse route. Removing
work from a budget-bound query hands the budget to whatever runs next, and on
this division whatever runs next is worse.

### Control and exposure: both run, both non-vacuous, both zero

Neither is reported as a zero nobody measured.

| division | role | result | non-vacuity, **shown** |
|---|---|---|---|
| `QF_S` | control — must not move | **186 → 186**, net +0, 0 losses, 0 aborts, soundness 0/165 | rows bind on `fd:source-string` (10 of 12) and `dl-online` (2 of 12) at **1–391 ms**, and the changed function executes **0** times there. A live division bound by a different route: a drift control, and it did not drift. |
| `QF_UFLRA` | exposure — shares the changed code | **148 → 148**, net +0, 0 losses, 0 aborts, soundness 0/148 | **559 entries** into `lra::simplex_fallback` across 12 rows. The changed code runs hard there and nothing moved. |

## Decision

**The sparse rows ship, as the ONLY path. The cell cap ships `Off`.**

### Sparse rows: shipped, and shipped as the default rather than behind a lever

R4's SHIP rule is met in full: R3 passes (0 verdict changes, 0 flips, soundness
0 at denominator 97, the three z3 differential fuzzes green at **5 / 1 / 1**),
peak RSS does not increase on any row, and the exit-status channel shows **0 new
aborts**.

It ships as the **default with the lever deleted**, and that choice is
load-bearing: **a lever defaulting `Off` would leave the new path exercised by no
gate in this repository.** Every documented pre-merge gate would have passed over
the old code while the new code shipped untested — the "gate that cannot fail"
shape. As the default, `corpus_regression`, the full `--lib` sweep and all three
differential fuzzes run it.

R4's CLAIM rule is **not** met and no board gain is claimed: net `+0` against a
measured floor of 0 of 200. **This is a null, and the null is the finding** —
it closes an 80 % bucket by showing the bucket is not shaped the way its size
suggests.

The dense `feasible_within` is kept `#[cfg(test)]` **because deleting it would
delete the round trip's standing check**: the dense entry converts and delegates,
so `the_sparse_entry_point_decides_exactly_what_the_dense_one_decides` compares
`densify_to_sparse(scatter(x))` against `x` end to end, on verdicts, over 200
generated systems, forever.

### The cap: `Off`, kept, and documented with its own refutation

It is **kept rather than deleted** so the finding stays reproducible from the
shipped tree — a measurement nobody can re-run is a remembered number. Its doc
comment carries the numbers and the instruction not to turn it on without
re-measuring the exit-status channel.

### What this says about the division

**The offline dense engine is not fixable by removing allocations from it.** Both
named allocations are now priced; one is 14 % and removing it decides nothing,
and capping the other actively costs clean exits. The structure itself is wrong:
**0.0288 % dense, a median 69× past the cap that was supposed to bound it**. The
remedy is the one ADR-2045 already identified from z3's 334 rows at 52.92 MB —
the **incremental** engine must take these queries — and §2.2 now names what
stands in the way with the right half of the sentence.

## Consequences — what the next lane should do

1. **Do not spend another lane on allocations inside the offline dense engine.**
   Both are priced. The engine needs a sparse tableau or it needs to not run.
2. **The wall is model REPLAY, not model RECONSTRUCTION.** 16 of 23 rows build a
   model that does not satisfy the originals; 0 hit the `i128` witness boundary.
   The work is in `add_boolean_leaf_values` and what the encoding leaves out of
   the reconstructed model — not in making the simplex produce a point.
   `AXEYUM_LRAMODELPROBE=1` is in the tree to re-measure this.
3. **7 of the 34 clock rows are a skeleton problem, not an arithmetic one** — the
   `sc-*.base.cvc` family emits over a thousand cubes per query. That is a
   different lane and it should not be sized as part of this bucket.
4. **Before capping or declining anything on a budget-bound route, measure the
   exit-status channel.** This division contains at least 18 rows where an
   obviously-correct decline is a net harm because the work being declined was
   absorbing a budget that a worse route then spends.

## Measurement caveats, stated rather than discovered

- **The A/B arm measures THIS BRANCH.** Arm B is the configuration this branch
  now ships as its default, so the **post-merge value is predicted to be
  identical to arm B: 107 of 200**, and the reason is that the merge changes
  nothing arm B did not already run.
- **A peer lane (`real-opaque`) started on s5 at pins 2,3 partway through the
  `QF_LRA` A/B.** My shards hold pins `(0,8)`/`(1,9)`, so no core collides, and
  every arm of a given file ran back to back under the same neighbours — which
  is what interleaving is for. The noise floor (0 of 200) was measured inside
  that same run and therefore *includes* the disturbance.
- **`pathological_overbound_stays_terminal_under_every_policy` flaked once**
  under load average 11.09 (`pathological_refusals` read 0), and passed alone
  (4.08 s) and in a full sweep at load 5.34 (**1763 passed, 0 failed**). Its
  assertion is consistent with its 5 s budget expiring before the refusal site
  is reached, and the `Unknown` assertion still held. Recorded as a
  **load-sensitive test**, not as a regression — but recorded, because it failed
  once on this branch.
- **The control and exposure divisions ran the 2-arm form (`A B`).** Arms not run
  are written `na` and reported as **DID NOT RUN**, never as zeros. The first
  draft of the summariser read `na` as a verdict and reported the control as
  "net −148, noise floor 200 of 200" — the reason unrun arms are now excluded
  explicitly.
- The 15 round-trip-killed rows' post-removal requirement is computed from the
  tableau they report **under the sparse arm**, which is the real measurement,
  not an extrapolation.

[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
