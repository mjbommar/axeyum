# The `QF_NIA` "one round" was a different loop's round, and it was slice-sized

Measured 2026-09-08 at solver commit `5d406a12b` (and its lane descendants), on
**s6** and **s7**, one process at a time per host, 24 s per file, over the first
50 files of `bench-results/parity-lists/QF_NIA.txt`.

The [span-log sweep](span-log-sweep-2026-09-08.md) reported the widest dead band
on the board:

> All 50 `QF_NIA` files enter the refinement loop. Rounds run 1 / 2 / 106.
> **25 of 50 complete exactly ONE round**, median 11.2 s of a 24 s budget.

and asked the deciding question: **is that one round genuinely enormous, or is
the loop mis-detected and not actually iterating?**

## The answer is neither, and it is the third option

**The rounds it counted are not the nonlinear-integer route's.**

`LazySmtCounters` instrumented exactly two loops, both in `dpll_t.rs`, and the
`refinement_loop` span summed `lra_rounds + nra_rounds` into a single
`loop_count`. On `QF_NIA` the non-zero one is `nra` —
`check_with_nra_dpll_within`, the sign-cell CAD — and it is reached from
`int_real_relax::refute_int_via_real_relaxation`, which runs **before** the
nonlinear-integer route is entered at all.

Measured on file 34 of the list at HEAD, `--trace`:

```
; lazy-smt reading=measured lra_entries=0 lra_rounds=0 nra_entries=1 nra_rounds=1
  theory_ms=3990 theory_unknown=1
```

One CAD round of 3.99 s. And 3.99 s is not a property of the round: it is
`auto::INT_REAL_RELAX_BUDGET_SHARE` exactly — 24 s / 6 = **4.00 s**. Twenty-three
of the twenty-five "one-round" files in the sweep carry a loop wall between
**3.993 and 4.009 s**. The round is not enormous. It is the size of the slice it
was handed, and the loop ended because the slice did.

So the sweep's reading was a true statement about a route nobody was asking
about, printed under a label that named the route they were.

## The loop the division actually spends its budget in had no instrument

`nia_linearize::solve_with_refinement` — the incremental linearization with
tangent planes — was not counted anywhere. Its behaviour, from
`AXEYUM_NIA_DEBUG` over the 50 files (n = 412 `check_with_nia` calls; the width
ladder re-enters the route on sub-queries, so a per-file count conflates them):

| top-level call per file | |
|---|---:|
| files | 50 |
| rounds: min / median / max | 1 / 1 / 15 |
| files running exactly one round | **26** |
| last round's outcome `unknown` | 45 of 50 |
| slice granted, median | 6.65 s (= remaining / `NIA_MCCORMICK_BUDGET_SHARE`) |
| files granted the 600 ms `NIA_SLICE_MS` floor instead | 3 |
| tangent lemmas emitted | 2,476 |
| files emitting none | 26 |

**The loop does iterate** — up to 15 rounds, 2,476 tangent lemmas — and where it
runs one round, it runs one round because that round returned `unknown` at the
slice deadline, which ends the loop. `OFF` hands round 0 the entire slice, so
the loop's first round is also its last whenever the relaxation solve cannot
decide inside it.

## Where the time inside a round goes

The brief's four candidates were candidate-model search, lemma generation, the
scalar re-solve, or interval/McCormick work. Measured, on file 34:

| | |
|---|---:|
| whole file | 10.98 s of 24 s |
| `int-real-relax` (CAD, invisible in the trail until now) | 4.04 s |
| lemma generation + abstraction (459 products, 2,574 split lemmas) | ~0.09 s |
| **the single refinement round's relaxation solve** | **6.72 s** |
| tangent refinement | 0 (the round never produced a model) |

So it is the **scalar re-solve**, and none of the other three. And that re-solve
does not spend its time searching: `check_with_lia_dpll` finds the relaxation
too large for its own admission screen and hands it to
`oversized_admission_probe`, whose documented behaviour is that "the search
consumes very close to whatever larger budget it is given".

## Three findings, in descending size

### 1. A quarter of the division's wall clock belongs to a route with no row

`int_real_relax::refute_int_via_real_relaxation` recorded a `RouteTrace` entry
only when it refuted. A trace attempt's `elapsed` runs from the previous
recorded attempt, so on every query where it declined its whole share was
printed under the next route that did record — `nia-linearize`.

With the row added (this lane), over the same 50 files:

| | |
|---|---:|
| files carrying an `int-real-relax` row | 50 |
| median wall | 4.02 s |
| sum | **188.5 s of the population's 762.6 s = 24.7%** |
| files it refuted | **0** |
| files where it, not `nia-linearize`, is now `bound_by` | 4 |

Forty-two of the fifty decline with `budget` — the CAD ran out of its sixth.
One declines because the real relaxation is satisfiable, which does not transfer
to the integers. Those are different statements about whether the share buys
anything, and they are now different decline reasons.

`nia-linearize`'s attributed budget on file 34 drops from 10,738 ms to 6,719 ms.

The share does not depend on what the routes after it do: on **s7**, with the
`1/1` arm selected so every later route behaves differently, the same 49 rows
sum to **184.2 s** against s6's 188.5 s over 50. It is a fixed sixth of every
file's budget, spent before the division's own routes are reached.

### 2. Fifteen of fifty files build a relaxation the next stage refuses on size

The linearizer's own `small_domain_lemmas` pass grows the query past the
admission screen of the solver it hands it to. Nothing connects the two bounds.

| file | products | split lemmas | relaxed | atoms | CNF vars |
|---:|---:|---:|---:|---:|---:|
| 6 | 672 | 2,160 | 6,213 | 5,575 | 17,291 |
| 34 | 459 | 2,574 | 5,337 | 6,793 | 18,217 |
| 36 | 1,401 | 4,096 | 12,517 | 11,870 | 36,668 |
| 45 | 1,032 | 3,696 | 9,906 | 9,538 | 28,615 |
| … | | | | 5,575–11,870 | 16,629–36,668 |

`dpll_lia::MAX_PRE_SAT_ARITH_ATOMS` is 1,024 and `MAX_PRE_SAT_CNF_VARS` 4,096;
the moderate envelope is 10,240 / 16,384. **Every one of the fifteen is over.**
The route then spends its whole slice in the 10 s bounded probe that exists for
oversized queries, and returns `unknown` having emitted **zero** tangent lemmas.

`nia_linearize::MAX_SMALL_DOMAIN_PRODUCTS` and `MAX_MCCORMICK_PRODUCTS` are
sized in products; `MAX_PRE_SAT_ARITH_ATOMS` is sized in atoms of the result.
Neither file mentions the other. This is the same shape ADR-1751 fixed for
`nra.rs` / `lra_theory.rs` (a producer's cap in one unit, the consumer's ceiling
in another) and it is the largest untouched lever this measurement found.

#### And it is ONE HALF of the rectangle that refuses them

The admission is conjunctive over two dimensions. Splitting the fifteen by
which dimension is actually over:

| | files |
|---|---:|
| over the CNF-variable ceiling **alone** (atoms fit) | **14** |
| over both | 1 (file 36) |
| over the atom ceiling alone | 0 |

The atom count on those fourteen runs at **54–96%** of its own 10,240 ceiling.
It is the 16,384 CNF-variable half that refuses every one of them, and seven are
over it by less than 10%:

| file | CNF vars | over by | in variables | atoms, as % of its own ceiling |
|---:|---:|---:|---:|---:|
| 40 | 16,629 | **1.5%** | 245 | 59% |
| 39 | 16,657 | 1.7% | 273 | 59% |
| 37 | 16,863 | 2.9% | 479 | 60% |
| 38 | 16,894 | 3.1% | 510 | 61% |
| 6 | 17,291 | 5.5% | 907 | 54% |
| 35 | 17,322 | 5.7% | 938 | 62% |
| 48 | 17,960 | 9.6% | 1,576 | 65% |

The [span-log sweep](span-log-sweep-2026-09-08.md) found one `QF_ABV` refusal
2.3% over a fixed cap and called it out as a shape. Here are seven more of it,
in a second division, against a *different* screen. `MAX_MODERATE_PRE_SAT_CNF_VARS`
is 16,384 because the largest point measured safe was 12,155 CNF variables,
"rounded up to the next power of two in each dimension" — on a `QF_LIA`
population, at a peak RSS of 71 MiB against an 8 GiB ceiling. Its own doc
already says what is owed: "a rectangle in (atoms, CNF vars) is the wrong shape
for a memory bound at all". This is the second population to demonstrate it, and
the first where the CNF dimension alone decides the whole outcome.

Not raised here. Raising it needs the RSS measurement that ADR-1752 did for
`lra_online`, and this lane has not taken it — what is established is only
*which* half refuses, and by how little.

### 3. Giving the loop three times the budget buys rounds and lemmas, not verdicts

`AXEYUM_NIA_REFINEMENT=1/1` hands the loop the whole remaining budget instead of
a third. `OFF` on s6, the arm on s7, both with the same binary; the two hosts
agree at 47/2/1 on three independent control sweeps.

| | `OFF` | `1/1` |
|---|---:|---:|
| sat / unsat / unknown | 2 / 1 / 47 | **4** / 1 / **45** |
| median wall | 10,994 ms | 24,010 ms |
| files killed by the watchdog | 7 | 1 |
| top-level rounds, max | 15 | 18 |
| tangent lemmas | 2,476 | 3,756 |
| files whose round count moved | — | 22 |
| `check_with_nia` calls over the population | 412 | **91** |
| files where `nia-linearize` is `bound_by` | 26 | 42 |

The call count collapsing from 412 to 91 is the cost side stated plainly: under
`OFF` the width ladder re-enters the route on sub-queries dozens of times per
file, and under the arm the first loop holds the budget and it never gets a
turn. No verdict was lost to that, on this population.

Two files move `unknown → sat` and none regress. **But neither move is
reproducible.** On repeat runs, pinned per host:

| file | `OFF` | `1/1` |
|---:|---|---|
| 13 | `unknown` 3/3 (s7), and in all three control sweeps | `sat` **3 of 4** |
| 30 | `unknown` in all controls | `sat` **1 of 7** |

The mechanism is the one `OVERSIZED_ADMISSION_PROBE_BUDGET`'s own justification
already records: this search consumes whatever budget it is given rather than
converging, so a larger slice changes *which* states it visits, not how deep a
monotone search goes. Twenty-two files get more rounds and 1,280 more tangent
lemmas out of it and decide nothing.

**So the refinement loop's budget is not the binding constraint on this
population, and neither is lemma quality.** A secant-based lemma schema
(arXiv:2608.04835) would be a better lemma inside a loop that is not short of
lemmas: 26 of 50 files emit none at all, because their single round never
returns a model to cut off. The measurement does not support building it yet.

The lever is shipped anyway, `OFF` by default, because the next question after
finding 2 is whether a smaller relaxation plus a larger slice behaves
differently from either alone, and that is an A/B nobody should have to rebuild
for.

## What was added

- `RoundHistogram` on `LazySmtCounters`: log2 millisecond buckets, max round and
  its index, per loop. Fed from the stage clocks the loops already take, so it
  reads no new clock. `loop_hist` in the span log is no longer `null`.
- `LazySmtLoop::Nia`, so `solve_with_refinement` is counted at all: the
  relaxation solve is the round-opening half, the ground-evaluator replay the
  theory half, the tangent lemmas the blocking clauses.
- **One span per loop entered** (`lazy-smt:lra`, `lazy-smt:nra`,
  `lazy-smt:nia`). Two deciders behind one count is how this happened.
- A round in flight is `pending_round_ms` on the span, not a lost round — the
  watchdog path keeps it out of the buckets because it is a lower bound there,
  and the completed read folds it in because by then it is a finished round.
- `int-real-relax` records its decline, with the reason.
- `NiaRefinementPolicy` (`AXEYUM_NIA_REFINEMENT=<slice>/<rounds>[/floor_ms]`),
  `OFF` reproducing the committed behaviour and a malformed lever parsing to
  `OFF` rather than to a silent third arm.

## The killed runs, which are the ones that matter

Forty-two of the fifty end `unknown` and seven never return at all, so the
instrument is worth little if it dies with the worker. It does not. Same file
(`QF_NIA` #5) at a 24 s budget, watchdog fired:

```
; partial at=watchdog-kill recovered=8 sampled=...,lazy-smt:in-flight,route:in-flight
; partial lazy-smt reading=measured nra_entries=1 nra_rounds=1 nia_entries=1 nia_rounds=1
    nra_hist=12:1 nra_max_ms=3999 nra_max_round=1
    nia_hist=-    nia_max_ms=0    nia_max_round=0    pending_round_ms=6673
; partial route bound_by=nia-linearize bound_ms=6674 total_ms=10692
; partial route-open ms=14307 after=cas-ideal-refuter
```

The finished CAD round is in bucket 12 (3,999 ms = 24 s / 6, again). The
refinement round that was **still running when the process died** is
`pending_round_ms=6673` and is deliberately not in a bucket: at that moment it
is a lower bound on its own cost, and filing it would put a lower bound into a
distribution as though it were a measurement.

The same file at a 12 s budget returns normally and reads
`nra_hist=11:1 nra_max_ms=1999` (12 s / 6) and `nia_hist=12:1 nia_max_ms=3342`
— both slices track the budget exactly, which is the check that these are
slice-sized rounds and not a coincidence at 24 s.

## One thing a consumer has to change

A `refinement_loop` span's `route` was `"lazy-smt"`. It is now
`"lazy-smt:lra"`, `"lazy-smt:nra"` or `"lazy-smt:nia"`, and there can be more
than one such span per run. A renderer that matches the route exactly — the
gallery's `scripts/sync_spans.mjs` in the `axeyum.com` repository is the one
known consumer — must match the prefix instead, or it will show no refinement
loop at all. The `instruments` list is unchanged (`lazy-smt:<sampled>`), and
`loop_hist` is now an array of 16 counts rather than `null` whenever
`loop_hist_available` is true.

## Reproducing

```sh
# the per-round view, one file
AXEYUM_NIA_DEBUG=1 target/release/examples/smtcomp_cli <file>.smt2 \
    --timeout-ms 24000 --trace 2>&1 | grep -E '^\[nia\]|lazy-smt|^; route'

# the arm
AXEYUM_NIA_REFINEMENT=1/1 target/release/examples/smtcomp_cli <file>.smt2 --timeout-ms 24000
```

Read `; lazy-smt` for `nra_hist` / `nia_hist` before attributing a round count
to a route — they are different loops and, on this division, one of them is
almost always another route's.
