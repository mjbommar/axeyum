# ADR-2090: the minimal cores ARE small, the suffix rule DOES find them, and we still do not decide them — assertion selection is a 1.1 % axis and it is closed

Status: accepted
Index-summary: [ADR-2050] measured a median minimal unsat subset of **ONE conjunct** over 13 quantifier-free rows and named two where we refute a **3-of-268** and a **1-of-633** subset in 24 s and fail on the whole; [ADR-2020] named *selection* as its open axis. This lane censuses the **third** sense of selection — **which ASSERTIONS to look at**, not [ADR-2005]'s *which representative TERM* (measured, +0) nor [ADR-2020]'s *which INSTANCES to admit* — across the undecided rows of all seven Tier 1 divisions, and **closes it**. The population re-derives at **645 undecided of 1,400** (755 decided, 714 comparisons against the declared `:status`, **0 disagreements**), and the board's `+4` hides **8 rows moving**: 2 board-undecided now decided, 6 the board called decided that are undecided here. **ADR-2050's shape GENERALISES**: over the 228 usable `REF-UNSAT` rows the median `minimal` is **3** against a haystack median of **37** — R5(a) `<= 5` **PASS** — and `REF-UNSAT` is **236/639 = 36.9 % [33.3, 40.7]**, R5(b) `>= 20 %` **PASS**. A fixed-`k` reference-free rule finds those cores: **`suffix(1)` CONTAINS the whole minimal core on 53 of 232 rows (22.8 %) against `prefix(1)` at 0 of 232** — position carries real information and the control is clean in both directions. **And none of it converts.** Handed z3's own minimal core at the same 24 s and shipped defaults, we return `unknown` on **193 of 230 (83.9 %)**; the CEILING — what selection could buy if selection were free and perfect — is **36 of 645 undecided rows, 5.6 %**, with **0 wrong answers and 0 nonzero exit statuses** at printed denominators. The best actual reference-free rule, `suffix(1)`, reaches **7 of the 38-row ceiling (18.4 %)** and **7 of 645 = 1.1 % [0.5, 2.2]**; the **R9 build gate FAILS** and **no lever is built**. The traced contrast says why, and it is not selection: the 38 rows we refute carry **`giveup_kind=NONE` on all 38**, finishing in **600 ms** median at **7** route attempts, while all 193 we fail on carry a give-up — `q:mbqi` ResourceLimit 40, `q:mbqi` Incomplete 37, `int-blast-ladder` Timeout 31, `q:egraph` ResourceLimit 26, Watchdog 17 — at **13.1 s** median and **20** attempts (max 1,156). The assertions already ARE the minimal core and the engine worked hard on them. **Two structural findings the sizes alone hide**: a minimal core of **1** does not mean the needle is easy to find, it means the refutation lives inside a SINGLE assertion so selection has no work to do at all (61 such rows, ceiling 11.5 %); and **UFNIA, carrying the largest undecided mass at 146, has a median haystack of TWO conjuncts** — 81 of its 146 undecided rows have `<= 2` and 110 have `<= 5`, so there is nothing there to select from before any solver runs. Division ceilings differ by an order of magnitude and that is where the value is: **UF 8/12 = 66.7 %**, `UFLIA` 15/53, against **`QF_NIA` 0 of 36 [0.0, 9.6]** — on every `QF_NIA` row where z3 found a core, no subset of the query is one we decide. The census's own blind spot is published: **36 `REF-NONE` rows declare `:status unsat`**, known-refutable but unreduced by z3 at 60 s.
Index-status: accepted
Date: 2026-09-15

## Context

Two merged ADRs named this and neither took it.

[ADR-2050] §3, reducing 13 quantifier-free queries that z3 and cvc5 refute and
we do not: *"Every row's minimal unsat subset is **ONE conjunct** (one is 3) —
**median 1** against a pre-registered ≤ 5."* Its bucket (B) named two rows where
we refute a **3-of-268** and a **1-of-633** subset in 24 s and fail on the whole,
and called that *"[ADR-2020]'s open axis with a witness whose answer we provably
already have."*

Two rows is a footnote. The distribution is the lane. If ADR-2050's median-of-1
generalises, a large fraction of what we fail on is a needle-in-haystack problem
rather than a capability problem. If those 13 were selected precisely because
they reduce well, the axis is small and the right outcome is to say so and stop.

**Three senses of "selection" are in play and no number transfers between
them.** [ADR-2005] measured *which representative TERM to substitute* — the
`InstBridge::repr_term` first-inserted defect — and moved **0 of 129**.
[ADR-2020] named *which INSTANCES to admit* as its open axis, after finding that
eight of nine reference-fast files flooded the 8,192 admission cap. **This lane
measures the third: which ASSERTIONS to look at.** It is the one nobody had
measured.

Branch base: `git merge-base main HEAD` is
`b78b887b3064b1075783ba6f4528519d07b1bbb6`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/core-select-20260915/PREREGISTRATION.md)
before any measurement, with five amendments (A1–A5) written before the census
counted a row and recorded in that file with their reasons.

## Decision

**Assertion selection is closed as an axis for this population, and no lever is
built.** The pre-registered build gate (R9) requires R5 to pass *and* some
reference-free rule to reach ≥ 50 % of the measured ceiling. R5 passes on both
halves; the best rule reaches **18.4 %** of the ceiling, and the ceiling itself
is **5.6 %** of the undecided population. R9 **FAILS** and this lane manufactures
nothing.

The value this lane hands forward is not the null. It is that the null is
**located**: the cores are small, they are where a trivial rule looks, and the
failure is downstream of selection entirely.

## 1. The population re-derives, and the board's delta is a third of the movement

All 1,400 pinned Tier 1 files, re-derived on this branch at the board's envelope
(24 s, shipped defaults, one pinned physical core, **all four shards on an idle
s7** so a 24 s boundary is not decided by a neighbour).

| division | n | unsat | sat | unknown | board und | delta |
|---|---:|---:|---:|---:|---:|---:|
| `UFNIA` | 200 | 33 | 21 | **146** | 147 | −1 |
| `QF_NIA` | 200 | 6 | 77 | **117** | 116 | +1 |
| `UFLIA` | 200 | 85 | 0 | **115** | 115 | +0 |
| `UF` | 200 | 68 | 22 | **110** | 106 | +4 |
| `AUFDTLIRA` | 200 | 121 | 0 | **79** | 79 | +0 |
| `UFDTLIRA` | 200 | 138 | 6 | **56** | 56 | +0 |
| `AUFLIRA` | 200 | 178 | 0 | **22** | 22 | +0 |
| **total** | **1400** | **629** | **126** | **645** | 641 | **+4** |

755 of 1,400 decided, which is `tier1-current`'s post-merge total exactly.

**The `+4` is not four rows moving.** It is 2 board-undecided rows now decided
and 6 the board called decided that are undecided here — **8 rows moving, 639
agreeing**. A delta read off the totals reports a third of the movement and the
wrong direction for most of it. This is why R1 reports both directions:
[ADR-2035] found 8 of 22, and the direction people remember to check is the one
that shrinks the population.

One of the six is `QF_NIA/mcm/106.smt2`, which the board does not carry at all —
its `QF_NIA` TSV has `20170427-VeryMax/SAT14/106.smt2` where the pinned list has
`mcm/106.smt2`, and **both exist in the corpus**. A basename collision in the
board's runner, not a missing file.

**Soundness: 714 comparisons against the files' own declared `:status`, 0
disagreements.** The comparable denominator is printed beside the zero.

## 2. Before any solver: 91 rows have nothing to select

A conjunct here is a top-level `assert` body with every `(assert (and a b c))`
split into separate asserts — an **equivalence**, re-checked before anything
else runs, and the right unit because [ADR-2050]'s haystacks (268, 633, 682) live
*inside one `and`*. A census counting `assert` FORMS would report those files as
1-conjunct haystacks and conclude there is nothing to select.

| division | undecided | median haystack | `conj ≤ 2` | `conj ≤ 5` |
|---|---:|---:|---:|---:|
| `UFNIA` | 146 | **2** | **81** | **110** |
| `QF_NIA` | 117 | 86 | 2 | 5 |
| `UFLIA` | 115 | 230 | 0 | 1 |
| `UF` | 110 | 356 | 0 | 1 |
| `AUFDTLIRA` | 79 | 29 | 0 | 0 |
| `UFDTLIRA` | 56 | 13 | 8 | 20 |
| `AUFLIRA` | 22 | 14 | 0 | 0 |
| **all** | **645** | **54** | **91** (14.1 % `[11.6, 17.0]`) | 137 |

**`UFNIA` carries the largest undecided mass and has a median haystack of two
conjuncts.** A two-conjunct file has at most one assertion to drop. Whatever the
core sizes turn out to be, selection cannot be the mechanism on that division —
and this is arithmetic over a parser, with no solver and no reference.

Two parser defects were found by this census's own exit status, which depends on
the finding. `|...|` quoting is not decoration: `(assert |def_B definitions|)`
appears verbatim in the CLEARSY families and a splitter that treats the space
inside the bars as a separator reads that assert as two arguments (2 of 1,400
files). And flattening an `and` tree costs O(bytes × depth), not O(leaves): one
163 KB `UFLIA` file exhausted a 16 GiB address-space cap and was recorded as
**zero** conjuncts, which would have entered the census as the smallest haystack
in the population. It has 2,031. After the fix, 1,400 of 1,400 parse.

## 3. ADR-2050's shape generalises — R5 passes on both halves

The reference finds the core; ours is the thing that fails. `z3 -T:60` on the
split file, then `(get-unsat-core)` over named conjuncts, then greedy single
deletion while the remainder stays `unsat`, then a re-check of the final subset
by z3 **and** cvc5 from its own written file.

| bucket | n | share of the 639 censused undecided rows |
|---|---:|---|
| `REF-UNSAT` | 236 | **36.9 % `[33.3, 40.7]`** |
| `REF-SAT` | 68 | 10.6 % `[8.5, 13.3]` |
| `REF-NONE` | 335 | **52.4 % `[48.6, 56.3]`** |

**More than half the rows we are undecided on, z3 cannot refute either in 60 s.**

Three sizes, never conflated, over the 228 usable `REF-UNSAT` rows:

| | med | p75 | p90 | max |
|---|---:|---:|---:|---:|
| haystack `conjuncts` | **37** | 180 | 357 | 689 |
| `z3_core` — *a* core, **not** minimal | **3** | 10 | 21 | 138 |
| `minimal` — 1-minimal, **not** minimum cardinality | **3** | 6 | 11 | 47 |

`minimal ≤ 1` 61/220 = 27.7 % · `≤ 2` 48.6 % · `≤ 3` 63.2 % · `≤ 5` **74.1 %
`[67.9, 79.4]`** · `≤ 10` 88.6 %. 8 rows are `MIN-CAPPED` and report `z3_core`,
never a guess.

**R5(a): median `minimal` = 3 against the pre-registered ≤ 5 — PASS.**
**R5(b): `REF-UNSAT` 36.9 % against the pre-registered ≥ 20 % — PASS.**

So ADR-2050's 13 were **not** chosen for reducing well. The median is 3 rather
than 1, and it sits against a haystack median of 37.

**A correction this lane made to its own R4 before quoting any number.** The
first partition put 42 rows in `AUTHORITY-SPLIT`. It is not a split:

| | n |
|---|---:|
| z3 **and** cvc5 both refute the core | 194 |
| cvc5 did **not answer** (kept, flagged) | 34 |
| cvc5 says `sat` against z3's `unsat` | **0** — comparable denominator **194** |
| z3 cannot re-check its **own** core | 8 — excluded |

A **disagreement** and a **non-answer** are different findings. Folding them
together turned 0 disagreements into 42 and dropped 34 usable rows. The eight
are 7 `CORE-FAILED` — `:produce-unsat-cores` disables preprocessing and turns
the `unsat` into an `unknown` — plus one `grasshopper` row where z3 refutes the
split file and then cannot refute the core it just produced.

## 4. The cores are where a trivial rule looks

Free arithmetic on the core indices: does a fixed-`k` rule **contain** the core?
Containment is sufficient, because a superset of an unsat set is unsat.

| k | `suffix(k)` | `prefix(k)` — CONTROL | `small(k)` |
|---:|---|---|---|
| 1 | **53/232 = 22.8 % `[17.9, 28.7]`** | **0/232 = 0.0 % `[0.0, 1.6]`** | 3/232 = 1.3 % |
| 2 | 70/232 = 30.2 % | 22/232 = 9.5 % | 18/232 = 7.8 % |
| 5 | 90/232 = 38.8 % | 40/232 = 17.2 % | 41/232 = 17.7 % |
| 25 | 136/232 = 58.6 % | 95/232 = 40.9 % | 92/232 = 39.7 % |

**The last conjunct alone contains the whole minimal core on 23 % of rows; the
first conjunct does so on 0 of 232.** Position carries real information and the
control is non-vacuous in both directions.

The shape behind it, per division — `core-shape.py` records the HEAD of every
core member with `not` unwrapped one level, so `(not (forall …))` and
`(not (=> …))` read as the same negated-goal shape and a bare `forall` reads as
an axiom:

| division | n | med `minimal` | med haystack | med `suffix_need` | cores holding the negated goal |
|---|---:|---:|---:|---:|---|
| `AUFDTLIRA` | 55 | 2 | 35 | **11** | **54 of 55** |
| `UFLIA` | 53 | 6 | 232 | 175 | 11 of 53 |
| `UFNIA` | 42 | 1 | 3 | **2** | 21 of 42 |
| `QF_NIA` | 36 | 13 | 30 | 27 | 5 of 36 |
| `AUFLIRA` | 18 | 1 | 14 | **1** | 8 of 18 |
| `UFDTLIRA` | 14 | 2 | 38 | 11 | 13 of 14 |
| `UF` | 14 | 6 | 349 | 347 | 8 of 14 |

Median non-goal members per core across all 232: **2**.

## 5. And none of it converts — the ceiling is 36 of 645

Hand our own solver the reference's own minimal core, at the same 24 s, the same
shipped defaults and the same pinned-core class as the re-derivation. **This is
a CEILING — what selection could buy if selection were free and perfect. It is
not a gain, not a conversion and not a parity number.**

    subsets handed to our solver   230
    unknown                        193/230 = 83.9 % [78.6, 88.1]
    unsat                           37/230 = 16.1 % [11.9, 21.4]

`WOULD-DECIDE` **36/229 = 15.7 % `[11.6, 21.0]`** of rows with a core, and **36
of the 645 undecided rows — 5.6 %**.

**Soundness: a reference core is unsat, so any `sat` here would be a wrong
answer. 0 of 230.** Exit-status channel: **nonzero rc on 0 of 230** —
[ADR-2045]'s arm was `losses=0` by verdict while creating five new aborts, so
the verdict count alone is not the check.

The ceiling is not uniform, and this is where the value is:

| | ceiling |
|---|---|
| `UF` | **8/12 = 66.7 % `[39.1, 86.2]`** |
| `UFLIA` | 15/53 = 28.3 % `[18.0, 41.6]` |
| `UFNIA` | 6/41 = 14.6 % `[6.9, 28.4]` |
| `UFDTLIRA` | 2/14 = 14.3 % |
| `AUFLIRA` | 2/18 = 11.1 % |
| `AUFDTLIRA` | 3/55 = 5.5 % `[1.9, 14.9]` |
| `QF_NIA` | **0/36 = 0.0 % `[0.0, 9.6]`** |
| by class | `NEEDLE` 29/158 = 18.4 % · `SINGLETON` 7/61 = 11.5 % · `WHOLE` 0/10 |

**`QF_NIA` is a zero at a comparable denominator of 36.** On every `QF_NIA` row
where z3 found a core, we are undecided on the core too — those cores are 15 to
66 coupled arithmetic atoms spread from index 1 to index 287 of the file.

**`AUFDTLIRA` runs opposite to intuition and that is the sharpest result here.**
It has the cleanest core shape in the population — 54 of 55 cores carry the
negated goal, median `minimal` 2, median `suffix_need` 11 — and the
second-worst ceiling at **3 of 55**. Small, well-placed, trivially findable
cores that we still do not decide.

### 5a. The ceiling is a measurement of THIS BRANCH — and of the merged tree

`main` moved a long way inside this lane's measurement window: [ADR-2100]
(typed route ownership), [ADR-2101] (the route trail as an API), and the
`PLAN-SIZING` lane, which independently reports *"the ladder STOPS on Unknown
in **604 of 645** undecided Tier 1 rows"* — **the same 645**, derived by a
different instrument, which is a cross-check on this lane's population that
neither lane arranged.

So the ceiling was re-measured on the merged tree with a freshly built binary
(`BUILD-OK postmerge 4311bdf2a`, `find -newer` clean), same 232 cores, same
24 s, same six pinned cores, and compared **at row level** — equal totals do
not imply equal files:

| | ceiling |
|---|---:|
| pre-merge (`b78b887b3`), the arm every number above was read on | **39 of 232** |
| post-merge (`4311bdf2a`) | **41 of 232** |
| row level | gains **3**, losses **1**, sat↔unsat flips **0** |

**Soundness on the merged tree: 0 `sat` of 232.** The three gains and one loss
are all `spark2014bench` rows. The conclusion does not move: 41 of 232 is
**6.4 % of the 645 undecided rows** against 5.6 % pre-merge, still an order of
magnitude below what a lever would need, and R9 is decided by the *strategy*
reaching 18.4 % of the ceiling, not by the ceiling's own size.

The lane's scripts were also re-run against the post-merge binary to confirm
they still parse what the tree now emits: `bound_by`, `attempts` and
`giveup_kind` all populate on `4311bdf2a`, so a future lane can re-run this
census rather than rebuild it.

## 6. The strategy, sized before building it

Every rule is computable from the query text alone; the reference may **decide**
a subset, it may not **choose** one. Run on the 36 ceiling-positive rows,
because a rule cannot convert a row we would not decide with the answer handed
to us (A4).

| rule | rows our solver refutes |
|---|---|
| `suffix(1)` | **7/36 = 19.4 % `[9.8, 35.0]`** |
| `suffix(2)` | 6/36 = 16.7 % |
| `rel(2)` — SInE-style symbol relevance from the negated goal | 5/36 = 13.9 % |
| `rel(1)` | 4/36 = 11.1 % |
| `small(1)` | 2/36 = 5.6 % |
| `prefix(1)` — CONTROL | **0/36 = 0.0 % `[0.0, 9.6]`** |

**Best single fixed rule `suffix(1)`: 7 of the 38-row ceiling = 18.4 %, and 7 of
645 = 1.1 % `[0.5, 2.2]`.** **R9 FAILS.**

The rule that wins is the most trivial one anybody would write first, and the
control converts zero where it converts seven. That is the useful half of the
negative: nothing more elaborate is being left on the table.

**Soundness audit of the 318 `sat` verdicts on strategy subsets.** Dropping
conjuncts weakens the formula, so most `sat` results here are simply correct; a
`sat` is a wrong answer **only** when the subset provably contains an unsat
core, and a verdict tally cannot tell the two apart. Containment checked on
**318 of 318**, **0 wrong answers** — with its positive control, because a
containment test that always answered False would print exactly that zero:
**152 of 723 subsets DO contain the core**, and **50 of the 51 we refute contain
it**. The one that does not holds a *different* refutation, which is why this
lane's column is named `z3_core` and not `the core`.

## 7. Why, and it is not selection

The traced pass runs over **all** 232 cores, not only the failures: a give-up
reason printed over the failures alone is a list of route names, and any of them
could equally well appear on the rows we refute. The traced verdict disagrees
with the untraced ceiling on **0 of 231 rows**, so the contrast is valid.

| | n | routes | attempts (med) | `total_ms` (med) |
|---|---:|---|---:|---:|
| **we refute the core** | 38 | `giveup_kind=NONE` on **all 38**; `q:mbqi-quick` 17, `q:uf-fmf-probe` 13, `q:bool-skeleton` 3 | **7** | **600** |
| **we do not** | 193 | every row carries a give-up: `q:mbqi` ResourceLimit 40, `q:mbqi` Incomplete 37, `int-blast-ladder` Timeout 31, `q:egraph` ResourceLimit 26, Watchdog 17, `q:egraph` Incomplete 14 | **20** (max 1,156) | **13,134** |

The rows we refute do not give up at all and finish in 600 ms. The rows we fail
on run 13 s and make 20 route attempts. **That is not a solver that looked at
the wrong assertions — the assertions ARE the minimal core, and it worked hard
on them.**

Give-up details verbatim and unbucketed, because sizing a bucket by its LABEL is
how [ADR-2020]'s census reported one cause where the raw details held four:

    39  e-matching: instantiation time budget exhausted mid-round
    30  preprocessed dispatch timeout after reduced solve; [ResourceLimit]
        integer bit-blast
    28  quantified solve time budget exhausted after e-matching
    17  watchdog fired before the worker thread returned
    12  e-matching reached FIXPOINT without refuting (2 or 3 rounds, "no
        further instance to admit; more rounds cannot help")
    17  mbqi declined an unsupported DATATYPE fragment (three distinct wordings)
     5  query has quantifiers instantiation does not reach (nested,
        existential, or non-top-level)
     4  no model within the bounded integer width 32; widen the bound

And the split that says whether a bigger clock would help: of the 193, **64 gave
up in under 2 s of a 24 s budget** and **73 ran 20 s or more**. A refusal and an
exhausted clock are different findings behind the same `unknown`, and this
population is roughly a third of each.

## 8. What a minimal core of 1 actually means

This is the finding that changes how [ADR-2050] §3 should be read, and it is
visible only from the core's TEXT rather than its size.

61 rows have `minimal == 1`. On
`AUFDTLIRA/…/K223-023__search__search.ads_8_9_postcondition`, that single
conjunct of twelve is

```smtlib
(assert (not (forall ((pos Int) (pos1 Int) (search__search__result Int)) …)))
```

— the entire verification condition, one deeply nested alternating-quantifier
formula. **There is nothing to select.** A minimal core of 1 does not mean the
needle is easy to find; it means the refutation lives inside a *single
assertion*, so "which assertions to look at" has no work to do on that row at
all. The `SINGLETON` class ceiling is **7 of 61 = 11.5 %**.

On that row the traced run says
`e-matching: no universal is asserted; the nested quantifiers present are
registered, not instantiated` — selecting the core **removed the universals
e-matching needs**. The reference-found core does not make that query easier for
us; it takes away the only material our quantifier engine knows how to use.

**So a median minimal core of 1 argues AGAINST the selection axis, not for it.**

## 9. What this census cannot see, published rather than left out

`REF-NONE` bounds the census from below: a row the reference cannot refute has a
core this lane cannot see, and reporting only the rows a reference could reduce
would size the axis on the easy half of its own population. Of the 339
`REF-NONE` rows, by the benchmarks' own declared `:status`:

    290  :status unknown   the benchmark is not known-refutable either
     36  :status unsat     KNOWN-REFUTABLE, unreduced by z3 at 60 s
     13  :status sat       no core exists

**36 is the firm lower bound on this census's blind spot.**

And the instrument's own cost, A5's sampled half — a seeded 60-row sample of
that bucket re-asked on the **original** file rather than the split one, because
the `and`-split is an equivalence but not a performance-neutral one:

    58  no verdict line — z3 prints `timeout` on `-T:` expiry, confirmed by
        running one by hand; NOVERDICT here MEANS timed out, at 60,054 ms
     1  unknown
     1  unsat

**One row in sixty is an artefact of the split: 1/60 = 1.7 % `[0.3, 8.9]`**
(`UFNIA/lahiri-cav09-storm-queries/mqueue_example_cegar_2_3_10.smt2`, refuted on
the original in 20.4 s and undecided on the split at 60 s). Scaled to the
339-row bucket that is of order six rows. Small, real, and reported rather than
rounded to zero — an instrument that costs 1.7 % is not an instrument that costs
nothing.

## Consequences

- **No lever is built** (R9 FAIL, R10-style discipline inherited from
  [ADR-2050] and [ADR-1976]). Assertion selection is closed for this population.
- **Do not size a lane against premise selection, relevance filtering or
  assertion pruning on Tier 1.** The ceiling is 5.6 % and the best
  reference-free rule reaches 1.1 %. `suffix(1)` is a two-line rule and it is
  already near the top of what the family offers.
- **Read [ADR-2050]'s median-of-1 as evidence about where the difficulty is,
  not about how findable it is.** A 1-conjunct core is a *single assertion* we
  cannot refute.
- **The divisions are not one population.** `UF` at 66.7 % and `QF_NIA` at 0 %
  do not share a mechanism, and a lane briefed on the Tier 1 aggregate will aim
  at neither. `QF_NIA`'s cores are coupled arithmetic; `AUFDTLIRA`'s are a
  negated goal plus two axioms that we still cannot refute.
- **The named successor axes are in §7's verbatim details, at their own
  denominators**: 12 rows where e-matching reaches a fixpoint and says more
  rounds cannot help; 17 where `mbqi` declines a datatype fragment in three
  distinct wordings; 5 where instantiation does not reach nested or existential
  quantifiers; 4 bounded at integer width 32. None of these is selection.
- **The board TSVs are snapshots.** Re-derive before sizing; the delta on the
  totals understated the movement by a factor of two and reversed its direction.

## Evidence

All under [`bench-results/core-select-20260915/`](../../../bench-results/core-select-20260915/):
`PREREGISTRATION.md` (R1–R12, amendments A1–A5), `ref/rederive-1400.tsv`,
`ref/split-1400.tsv`, `ref/core-census.tsv`, `ref/positions.tsv`,
`ref/core-shape.tsv`, `ref/sim-cores.tsv`, `ref/sim-subsets.tsv`,
`ref/trace-cores.tsv`, `ref/joined.tsv`, `ref/summary.txt`,
`ref/trace-report.txt`, `ref/subset-soundness.txt`, `ref/control-summarize.txt`.

Controls, each with an exit status that depends on its finding:
`control-nonvacuity.py` (the instrument reports 1, 3, 7 and 12 when the answer
is 1, 3, 7 and 12, and locates a buried needle at its own index — 5 of 5),
`control-summarize.py` (5 of 5 mutants killed on the headline test; it caught
its own staleness when the summariser renamed a line), `check-subset-soundness.py`
(318 of 318 `sat` verdicts checked for containment, 0 wrong, positive control
live at 152 of 723), and `collect.sh` (refuses a short or duplicated sweep;
demonstrated against a running sweep at `rows=663 listed=1400 rc=4`).

Hosts and cores: at most **six pinned physical cores** throughout — s7 `0,1,2,3`
(measured idle, load 0.08) for every reference measurement and the whole
re-derivation, plus s5 `1` and s6 `3`.
