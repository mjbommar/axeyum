# UFNIA and UFLIA — the whole winnable set censused, and the one blocker it names sized at 2

**2026-09-13, lane `ufnia-uflia`.** Tier-1 #2 and #3 had never been aimed at.
`UFNIA`'s blockers were censused by the Tier-1 board ([ADR-1957]) and that board
called the division *"genuinely clock-bound"*; `UFLIA`'s had never been censused
at all under the ADR-1956 split. Both are censused here over the **whole**
winnable set on the current tree, the largest family is attributed to a named
route, and the fix that family implies is **sized by a sound one-way surrogate
and measured not to pay**.

Every number below is re-derivable from the committed TSVs by `summarize.py`,
`census-summarize.py`, `route-hit-rate.py`, `ab-summarize.py` and
`confirm-summarize.py`. Nothing here is transcribed.

## The board rows

Our verdicts are from this lane's run at `c281a4b22`; the z3 / cvc5 / `:status`
columns are read from the **pinned boards** and are not re-derived — a reference
verdict at a fixed budget on a fixed file does not change.

| division | files on disk | axeyum (here) | axeyum (pinned board) | z3 | cvc5 | best ref | winnable |
|---|---:|---:|---:|---:|---:|---:|---:|
| UFNIA | 13,464 | **53** | 53 | 96 | 94 | 114 | **61** |
| UFLIA | 10,128 | **76** | 71 | 139 | 142 | 144 | **68** |

`UFNIA` reproduces the Tier-1 board exactly, which is the cross-check that this
lane's harness and that one measure the same thing. `UFLIA` is **+5** on
board-six's row from yesterday; those five are other lanes' work, not this one's.

**Soundness, with the comparable denominator on the same line ([ADR-1957]):**

    UFNIA  53 verdicts   vs :status 14/14   vs z3 49/49   vs cvc5 46/46   DISAGREEMENTS: 0
    UFLIA  76 verdicts   vs :status 76/76   vs z3 74/74   vs cvc5 76/76   DISAGREEMENTS: 0

Neither zero is vacuous: 109 and 226 independent comparisons stand behind them.

## The census — all 129 winnable rows, not a sample

    by kind:  CLOCK 81   SHAPE 14   PARSE 2   OTHER 2   ROUND 1
              UNCLASSIFIED (ADR-1941) 29      no route trail at all 0

| family | kind | UFNIA | UFLIA | tot |
|---|---|---:|---:|---:|
| **ladder CLOCK exhausted after e-matching** | CLOCK | **23** | **23** | **46** |
| e-matching instantiation CLOCK | CLOCK | 18 | 14 | 32 |
| mbqi declined an unsupported fragment | SHAPE | 1 | 4 | 5 |
| ingest resource limit (deterministic cap) | SHAPE | 4 | 0 | 4 |
| instantiation sat, universal unrefuted | SHAPE | 2 | 0 | 2 |
| front-door parse refusal | PARSE | 2 | 0 | 2 |
| quantified CLOCK, other stage | CLOCK | 0 | 2 | 2 |
| bounded integer width | SHAPE | 1 | 0 | 1 |
| MBQI round budget | ROUND | 1 | 0 | 1 |
| e-matching FIXPOINT (no instance left to admit) | SHAPE | 1 | 0 | 1 |
| e-matching has no universal | SHAPE | 0 | 1 | 1 |
| e-matching GROWTH-HEADROOM (a clock exit) | CLOCK | 0 | 1 | 1 |
| *(OTHER, printed in full by `census-summarize.py`)* | OTHER | 1 | 1 | 2 |

**No nested-array refusal appears in either division** — 0 of 129 — so the
20,399-file array-IR ceiling ([ADR-1965]) does not reach here, exactly as the
Tier-1 board projected for `UFNIA` and now measured for `UFLIA` too.

### ADR-1950: which budget, and the family whose label its own data refutes

| family | kind | n | ms_left min | **median** | max | reading |
|---|---|---:|---:|---:|---:|---|
| ladder CLOCK after e-matching | CLOCK | 46 | −463 | **−61** | −5 | genuinely clock-bound |
| e-matching instantiation CLOCK | CLOCK | 32 | 396 | **6,346** | 10,948 | **MIXED — two populations** |
| ingest resource limit | SHAPE | 4 | 23,988 | **23,992** | 23,993 | clock never involved |
| front-door parse refusal | PARSE | 2 | 23,976 | **23,977** | 23,977 | clock never involved |

Counting rows that gave up **past** the 24,000 ms deadline, per kind, is the
direct test of the labels:

    CLOCK      48 of  81      SHAPE       0 of  14
    ROUND       1 of   1      PARSE       0 of   2

Only CLOCK and the one ROUND row run past the deadline; every SHAPE and PARSE
row stops short of it.

**Is `UFNIA` "genuinely clock-bound"?** [ADR-1957] said so on the strength of
its 21+15 CLOCK rows. **Half of that is right and half is not, and the split is
between two families the name does not distinguish.** The 23 rows of
`ladder CLOCK exhausted after e-matching` give up a median 61 ms **past** the
deadline — clock-bound, no argument. The 18 rows of
`e-matching: instantiation time budget exhausted` give up with a median
**8,768 ms of 24,000 still unspent**, and its `UFLIA` twin with 6,346 ms. A
family named for a clock whose median row leaves a third of the clock on the
table is ADR-1950's falsification mechanism firing on the label, and no larger
wall budget reaches it.

### ADR-1956: the round ceiling is not the blocker here either

    e-matching ROUND CEILING (the round budget)     0 rows
    e-matching FIXPOINT (no instance left to admit) 1 row
    e-matching GROWTH-HEADROOM (a clock exit)       1 row

**0 of 129** rows end at the instantiation round ceiling. ADR-1956 measured that
on six divisions; it holds on these two. Anyone reaching for `AXEYUM_QINST_ROUNDS`
on `UFNIA` or `UFLIA` would buy nothing.

### ADR-1941: both readings, on both divisions

| division | census rows | `attempts=`-only would discard | actually carry an open segment |
|---|---:|---:|---:|
| UFNIA | 61 | 60 | **7** |
| UFLIA | 68 | 61 | **22** |

The `attempts=`-only rule would discard 121 of 129 rows and leave `UFNIA`'s
census with a single row. The open-segment reading keeps 100 and excludes 29
from every count above.

## Where the clock goes: `q:egraph`

The census's largest family is attributed, not guessed. On **44 of its 46 rows**
the route that held the largest attributed segment is `q:egraph`, the e-matching
instantiation loop:

| division | rows | `bound_by` | `bound_ms` median | share of the 24 s budget |
|---|---:|---|---:|---:|
| UFNIA | 23 | `q:egraph` on 23 | 22,554 ms | **94 %** |
| UFLIA | 23 | `q:egraph` on 21 | 21,065 ms | **88 %** |

It then declines, and `finish_quantified_solve` reaches
`config_with_remaining_timeout` with nothing left, so **full MBQI and the full
pure-UF finite-model finder never run** and the ladder ends at
`quantified_timeout("e-matching")`.

And what that budget buys, from the same run (`route-hit-rate.py`):

| division | `q:egraph` ENTERED | it DECIDED | it BOUND the run |
|---|---:|---:|---:|
| UFNIA | 125 / 200 (62 %) | **1 / 200** | 82 / 200 |
| UFLIA | 119 / 200 (60 %) | **8 / 200** | 69 / 200 |
| AUFLIA *(control)* | 115 / 200 (57 %) | **0 / 200** | 35 / 200 |

**The rung runs on ~61 % of files, holds the largest segment on ~38 %, and
decides between 0.5 % and 4 %.** That is the case for a ladder reserve, and it
is the strongest form of the case: the same shape, with the same numbers, is
what [ladder-budget-discipline-2026-09-08] built `ABV_ONLINE_LADDER_RESERVE_SHARE`
and `UF_ARITH_LADDER_RESERVE_SHARE` on.

## The sizing — a sound one-way surrogate, and it does not pay

`QuantEgraphReservePolicy` (`AXEYUM_QUANT_EGRAPH_RESERVE`, **ships OFF**) holds
a share of the remaining clock back for the rungs below `q:egraph`. `share = 1`
hands the rung `MIN_LADDER_SLICE` — one millisecond — and the ladder below it
essentially the whole budget. That is **strictly more clock than any real
reserve can give the lower rungs**, so it is a one-way CEILING: a file it does
not decide is out of reach of every reserve, at every share.

Interleaved per-file A/B, **one binary, two env values**, both arms back to back
on the same pinned physical core with the arm order alternating per file, 24 s
wall / 8 GiB `ulimit -v`, s5/s6/s7:

| division | n | base | ceiling arm | net | gain | loss | sat↔unsat flips |
|---|---:|---:|---:|---:|---:|---:|---:|
| UFNIA | 200 | 53 | 55 | **+2** | 2 | 0 | **0** |
| UFLIA | 200 | 73 | 73 | **+0** | 3 | 3 | **0** |
| AUFLIA *(control)* | 200 | 86 | 86 | **+0** | 0 | 0 | **0** |

**46 blocked rows → 2 net files, and the `UFLIA` half is net zero.** The
sizing bracket is `46 → 2`, and 2 is inside the noise: the base arm reads **73**
in the `UFLIA` A/B and **76** in the single-arm census sweep at the same commit
on the same boxes, a 3-file ambient band — larger than the entire effect.

### Every moved row re-run three times per arm, and against both references

    rows re-checked: 8   GAIN 4   LOSS 2   UNSTABLE 2   CONTRADICTED 0
    NO INDEPENDENT CHECK AT ANY BUDGET (ADR-1957): 1 of 8  <-- VACUOUS for those rows

Two of the eight rows the A/B moved were **ambient**: `smtlib.1015458` and
`smtlib.1185183` reproduce as `unknown,unsat,unsat` and `unknown,unsat,unknown`
in the arm. They are not counted in either direction. After the re-check the
whole effect is **+4 / −2 over 400 files**.

All six checkable gains and losses agree with `:status`, z3 4.13.3 and cvc5 1.3.4.
The seventh, `UFNIA/2019-Preiner/combined/t3_rw1159.smt2`, is the [ADR-1957] case
and the board says so on the line rather than in a footnote: it declares
`:status unknown`, cvc5 returns `unknown` at 24 s **and at 600 s**, and z3 emits
no verdict line at all at either budget. **Nothing has confirmed that `unsat`**,
so it is reported as unconfirmed rather than counted in a zero.

### The control is not vacuous, and here is the number that says so

`AUFLIA` is the control, and it is a **quantified** division on purpose — three
lanes this week shipped controls structurally unable to exercise the route they
changed, two of them by controlling a quantifier change on quantifier-free
divisions. So the hit rate is published beside the null, derived from each
division's own `qtrace` column by `route-hit-rate.py`: `q:egraph` is **entered
on 62 % / 60 % / 57 %** of `UFNIA` / `UFLIA` / `AUFLIA` and holds the largest
attributed segment on 41 % / 35 % / 18 %. **The control's null is a null of a
route that runs on 115 of its 200 files**, not of a route that is absent — and
on `AUFLIA` that route decides **zero** of 200 while bounding 35.

## The decision

**Do not ship the reserve on.** The lever stays, defaulted to `WholeBudget`,
registered in the configuration registry, so the next lane can re-ask the
question with one environment variable and no patch — the same disposition as
`AXEYUM_QINST_ROUNDS` after ADR-1956 and `AXEYUM_NIA_REFINEMENT` after its own
A/B. Reasoning and the two things this measurement does NOT say are in
[ADR-1970](../../docs/research/09-decisions/adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md).

## Method

- **Population.** The pinned lists `../parity-lists/UFNIA.txt` and
  `../parity-lists/UFLIA.txt`, committed before either board was measured; the
  control is `../parity-lists/AUFLIA.txt`. Not re-sampled.
- **Envelope.** 24 s wall, 8 GiB `ulimit -v`, one pinned **physical** core
  (`c,c+8` — a core and its SMT sibling), wrapper timeout 24 + 16 s. Identical
  to both pinned boards, so a census row is comparable to the board row it came
  from. `wrapper-killed` and `rc134` are **zero on every row of every run here**.
- **Binaries.** Built by `build.sh`, which refuses to publish a binary that is
  not newer than every `crates/**/*.rs`. Both arms are the SAME binary; the
  base arm runs under `env -u AXEYUM_QUANT_EGRAPH_RESERVE`, so it is an
  environment with no lever in it rather than a lever set to "off".
- **Probe.** `probe.sh` ran on all three hosts before any measurement and
  returned identical verdicts — a missing binary and a hard division produce the
  same empty TSV.
- **Placement.** One division at a time on four core pairs per host.
  `launch.sh`'s header says why: shard numbering restarts per division, so two
  divisions launched together put two of THIS lane's shards on one physical core.
  Hosts were idle at launch (load 0.02 / 0.06 / 0.06).
- **Merging.** `merge-division.py` and `ab-summarize.py` ABORT unless the shards
  cover the pinned list exactly. `cut-to-winnable.py` ABORTS if a winnable file
  has no census row.

## Files

| path | what |
|---|---|
| `census/UFNIA.tsv` `census/UFLIA.tsv` | one row per pinned file: verdict, route fields, `qtrace`, give-up |
| `compact-qtrace.py` | the projection applied to the three full-200 `qtrace` columns before committing: only `egraph@` segments are kept, which is exactly what `route-hit-rate.py` reads. The per-file attribution comes from `decided_by`/`bound_by`/`bound_ms`, which are untouched. 5.8 MB → 416 KB, and every published number re-derives identically. |
| `census/*.winnable.tsv` | the same rows cut to the winnable set — the census denominator |
| `census/AUFLIA.control.tsv` | the control division's trace sweep, which is where its 57 % route hit rate comes from |
| `winnable/*.txt` | the winnable sets, so that denominator is re-derivable |
| `ab/UFNIA.ceiling.tsv` `ab/UFLIA.ceiling.tsv` | the interleaved A/B, per file, both arms |
| `ab/AUFLIA.ceiling-control.tsv` | the quantified control division |
| `moved/*.confirm.raw.tsv` | every moved row, 3 runs per arm plus both references |
| `build.sh` `probe.sh` `launch.sh` `launch-ab.sh` `census-run.sh` `ab-run.sh` `confirm-moved.sh` | the measurement |
| `summarize.py` `census-summarize.py` `route-hit-rate.py` `ab-summarize.py` `confirm-summarize.py` `merge-division.py` `cut-to-winnable.py` | the derivations |

[ADR-1941]: ../../docs/research/09-decisions/adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md
[ADR-1950]: ../../docs/research/09-decisions/adr-1950-a-round-budget-and-a-clock-budget-are-different-findings-and-a-census-must-not-merge-them.md
[ADR-1956]: ../../docs/research/09-decisions/adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: ../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1965]: ../../docs/research/09-decisions/adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md
[ladder-budget-discipline-2026-09-08]: ../../docs/research/12-performance/ladder-budget-discipline-2026-09-08.md
