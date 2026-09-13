# Seven Tier-1 divisions at n = 200 — six probe rates confirmed, one refuted

**2026-09-13, lane `board-tier1`.** The Tier-1 priority list placed AUFLIRA and
UFNIA at #1 and #2 on the strength of a **24-file probe, not a board**. Probes in
this repository have been wrong five times in two days. All seven divisions on
that list are now measured at **200 full-span files each**, three solvers
interleaved per file, with the blockers censused over the **whole** winnable set.

The method is in [`PROTOCOL.md`](PROTOCOL.md); everything below is derived from
the committed TSVs by `summarize.py`, `census-summarize.py`,
`census-crossdiv.py` and `nested-array-reach.py`, not transcribed.

    axeyum   126 / 1400  ( 9.0 %)
    z3       644 / 1400  (46.0 %)
    cvc5     566 / 1400  (40.4 %)

## The board

| division | files on disk | axeyum | z3 | cvc5 | best ref | winnable |
|---|---:|---:|---:|---:|---:|---:|
| UFNIA   | 13,464 | **53** |  96 |  94 | 114 |  61 |
| FP      |  2,669 | **46** | 137 | 104 | 165 | 119 |
| AUFLIRA | 20,011 | **10** | 197 | 196 | 197 | 187 |
| AUFBV   |  1,523 | **10** |  30 |  20 |  46 |  44 |
| ABV     |  4,975 |  **4** |  14 |   4 |  17 |  17 |
| AUFNIRA |  1,480 |  **3** | 138 | 140 | 142 | 139 |
| ALIA    |  3,098 |  **0** |  32 |   8 |  36 |  36 |

`best ref` is the per-file better of the two references, a harder denominator
than either alone. *winnable* = we returned `unknown` and a reference decided.

## The seven probe verdicts

**CONFIRMED** means the board rate falls inside a **Wilson** 95 % interval around
the 24-file probe. Wilson and not the normal approximation: ALIA's probe was
**0 of 24**, where the normal interval is the single point 0.0 and *every*
possible board would "refute" it — a verdict manufactured by the statistic
rather than measured. A mutant swapping Wilson for the normal interval is in the
control table.

| division | probe (n = 24) | 95 % CI | board (n = 200) | verdict |
|---|---:|---|---:|---|
| AUFLIRA |  4 % | 0.7 – 20.2 % | **5.0 %** | CONFIRMED |
| UFNIA   | 20 % | 9.2 – 40.5 % | **26.5 %** | CONFIRMED |
| ABV     |  8 % | 2.3 – 25.8 % | **2.0 %** | **REFUTED** (board lower) |
| ALIA    |  0 % | 0.0 – 13.8 % | **0.0 %** | CONFIRMED |
| AUFNIRA |  4 % | 0.7 – 20.2 % | **1.5 %** | CONFIRMED |
| AUFBV   |  4 % | 0.7 – 20.2 % | **5.0 %** | CONFIRMED |
| FP      | 20 % | 9.2 – 40.5 % | **23.0 %** | CONFIRMED |

**The probe was right about six of seven, and AUFLIRA and UFNIA are correctly
placed at #1 and #2.** That is the answer to the question this lane was created
to ask, and it is the boring answer.

The one refutation is ABV, and it is in the direction that matters least: the
probe said 8 %, the board says 2.0 %. The ABV row's real content is that **the
division is hard for everyone** — z3 decides 14 of 200 and cvc5 4 — not that we
are unusually weak there. A 24-file probe cannot distinguish those.

## Soundness: 126 verdicts, 0 disagreements — and where that zero is empty

| division | we decided | vs `:status` | vs z3 | vs cvc5 | disagreements |
|---|---:|---:|---:|---:|---:|
| AUFLIRA |  10 | 10/10 | 10/10 | 10/10 | **0** |
| UFNIA   |  53 | 14/53 | 49/53 | 46/53 | **0** |
| FP      |  46 |  0/46 | 46/46 |  0/46 | **0** |
| AUFBV   |  10 |  0/10 |  2/10 |  0/10 | **0** |
| AUFNIRA |   3 |   3/3 |   3/3 |   3/3 | **0** |
| ABV     |   4 |  **0** | **0** | **0** | **0 — VACUOUS** |
| ALIA    |   0 |     — |     — |     — | **0 — VACUOUS** |
| **TOTAL** | **126** | **27** | **110** | **59** | **0** |

**Reference-vs-reference conflicts: 0** in all seven divisions, and
**reference-vs-`:status` conflicts: 0**, so the ground truth the checks rest on
is not itself in dispute.

Two of those zeros mean nothing, and the board says so on the line itself rather
than in a footnote — this is [ADR-1957](../../docs/research/09-decisions/adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md),
written by this lane:

    DISAGREEMENTS: 0  <-- VACUOUS: nothing checked any verdict we produced

ALIA produces no verdicts at all. ABV produces four, but the division declares
`:status unknown` on **199 of its 200 sampled files** and both references return
`unknown` on all four — in **0.1 s**, a capability decline rather than a budget
difference, confirmed by re-running both at **600 s**. See
[`findings/README.md`](findings/README.md) §1 and `confirm-ABV.tsv`.

**No row hit the measurement wall.** `wrapper-killed` is **zero for every solver
in every division**, across all 4,200 runs — the thing a previous census got
wrong by putting `timeout 32` around a 24 s budget and manufacturing 17 false
"no reason" rows.

**cvc5's column is a floor, not its capability.** 176 of its 1,400 runs ended
`rc134`, the protocol's 8 GiB address-space cap (AUFNIRA 55, UFNIA 43, AUFBV 40,
FP 36, AUFLIRA 2). The cap is applied identically to all three solvers; z3 and
axeyum hit it **0** times. **Name z3 as the reference when quoting the AUFNIRA,
UFNIA, AUFBV and FP gaps.**

## The blocker census — all 603 winnable rows, not a sample

    by kind:  PARSE 376   SHAPE 111   CLOCK 61   ROUND 19   OTHER 14   INTERNAL 3
              UNCLASSIFIED (ADR-1941) 19

| family | kind | AUFLIRA | UFNIA | ABV | ALIA | AUFNIRA | AUFBV | FP | tot |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| nested array element sort refused | PARSE | 185 | 0 | 17 | 33 | 129 | 0 | 0 | **364** |
| finite quantifier domain too big to expand | SHAPE | 0 | 0 | 0 | 0 | 0 | 0 | 98 | **98** |
| e-matching CLOCK budget | CLOCK | 0 | 21 | 0 | 0 | 2 | 11 | 0 | 34 |
| e-matching instantiation CLOCK | CLOCK | 0 | 15 | 0 | 0 | 3 | 6 | 0 | 24 |
| e-matching ROUND budget | ROUND | 0 | 2 | 0 | 3 | 0 | 14 | 0 | 19 |
| other front-door parse refusal | PARSE | 0 | 2 | 0 | 0 | 0 | 0 | 10 | 12 |
| e-matching has no universal | SHAPE | 0 | 0 | 0 | 0 | 0 | 8 | 0 | 8 |
| mbqi declined an unsupported fragment | SHAPE | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 3 |
| terminal internal error | INTERNAL | 0 | 0 | 0 | 0 | 3 | 0 | 0 | 3 |
| quantified CLOCK, other stage | CLOCK | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 3 |
| instantiation sat, universal unrefuted | SHAPE | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 2 |
| *(OTHER, printed in full by `census-crossdiv.py`)* | OTHER | 0 | 7 | 0 | 0 | 2 | 0 | 5 | 14 |

**These are three different populations, and a single ranked list would have
hidden that.** The four array divisions are one blocker. FP is a completely
different one. UFNIA and AUFBV are a third.

### ADR-1950: which budget, and the family whose label its own data refutes

| family | kind | n | ms_left min | **median** | max | reading |
|---|---|---:|---:|---:|---:|---|
| nested array refused | PARSE | 364 | 23,797 | **23,999** | 24,000 | clock never involved |
| finite domain too big | SHAPE | 98 | 23,953 | **23,990** | 24,000 | clock never involved |
| e-matching CLOCK budget | CLOCK | 34 | −727 | **−68** | −10 | genuinely clock-bound |
| e-matching instantiation CLOCK | CLOCK | 24 | −80 | **6,565** | 11,016 | **MIXED — see below** |
| e-matching ROUND budget | ROUND | 19 | 7,580 | **15,693** | 23,780 | clock NOT binding |
| quantified CLOCK, other stage | CLOCK | 3 | −860 | **−364** | −121 | genuinely clock-bound |

**The round/clock split is 19 ROUND against 61 CLOCK — the opposite proportion
to board-six**, where 177 of 390 were round-bound. On these seven divisions the
round budget is a minor blocker and the clock is real: 37 of the 61 CLOCK rows
give up *past* the deadline.

And ADR-1950's falsification mechanism fired on its own table.
**`e-matching: instantiation time budget exhausted` is named for a CLOCK and its
median row gives up with 6,565 ms of 24,000 still unspent.** Its range spans
−80 to +11,016, so it is genuinely two populations under one message. Per
ADR-1950 step 2 the `ms_left` column reclassifies it **by the data**, and it is
printed as `mixed` rather than quietly counted as clock-bound. Anyone raising a
time budget on the strength of that reason's name would buy nothing on more than
half of its 24 rows.

### ADR-1941 is doing more work here than on any previous board

The discriminator for UNCLASSIFIED is the **`route-open` segment**, not
`attempts=`. On this census the two readings differ enormously:

| division | census rows | `attempts=`-only would discard | actually carry an open segment |
|---|---:|---:|---:|
| AUFLIRA | 187 | **186** | **1** |
| AUFNIRA | 139 | **137** | **0** |
| UFNIA | 61 | 60 | 10 |
| ALIA | 36 | 33 | **0** |
| FP | 119 | 21 | 3 |
| AUFBV | 44 | 17 | 5 |
| ABV | 17 | 0 | 0 |
| **TOTAL** | **603** | **454 (75 %)** | **19 (3 %)** |

**The `attempts=`-only rule would discard 454 of 603 rows.** On AUFLIRA it would
discard 186 of 187 and the division's census would be **empty** — the entire
headline finding suppressed. On AUFNIRA, 137 of 139, and **not one** of them
carries an open segment.

ABV is the case that shows the rule is not merely permissive: its ladder maximum
*is* 2, every row reaches it, and the two readings agree at 0. UFNIA is the case
ADR-1941 exists to keep honest in the other direction — **10 of its 61 rows
really do carry an open segment** (6 after `q:uf-fmf-probe`, 3 after `q:egraph`,
1 after `q:mbqi-quick`) and are excluded from every ranking above.

Both readings are printed on every division, as ADR-1941 step 6 requires.

## The headline question: how much is really the nested-array refusal?

The brief asked this because the `NESTED-ARRAY-IR` lane is sizing an IR change
against a **29,564-file** figure, and asked to be told **loudly and early** if
the true share is much lower. It is not lower. It is higher — and it is
concentrated far more narrowly than the framing suggests.

| division | winnable | nested-array refusal | share of winnable |
|---|---:|---:|---:|
| ABV     |  17 |  17 | **100 %** |
| AUFLIRA | 187 | 185 | **99 %** |
| AUFNIRA | 139 | 129 | **93 %** |
| ALIA    |  36 |  33 | **92 %** |
| UFNIA   |  61 |   0 | **0 %** |
| AUFBV   |  44 |   0 | **0 %** |
| FP      | 119 |   0 | **0 %** |
| **TOTAL** | **603** | **364** | **60 %** |

**In the four array divisions it is 364 of 379 winnable rows — 96 %. In the
other three it is exactly zero.** So the 29,564 figure names the right scope.

But 29,564 is a **population**, not a reach: it is exactly
`AUFLIRA 20,011 + ABV 4,975 + ALIA 3,098 + AUFNIRA 1,480`, the whole contents of
those divisions. `nested-array-reach.py` turns it into a ceiling:

    division   on disk  winnable  nested  of sample   projected ceiling
    AUFLIRA     20,011       187     185      92.5 %             18,510
    AUFNIRA      1,480       139     129      64.5 %                955
    ALIA         3,098        36      33      16.5 %                511
    ABV          4,975        17      17       8.5 %                423
    -------------------------------------------------------------------
    TOTAL       29,564                                            20,399   (69 %)

**18,510 of that 20,399 — 91 % — is AUFLIRA alone.** ABV, ALIA and AUFNIRA
together project to 1,889 files. Framing the work as "four array divisions"
makes it look four times broader than it measures; it is **one division plus a
remainder**, and no census result from the other three could change that,
because their populations are too small.

Two caveats the arithmetic cannot remove, both printed by the script:

- **A ceiling, not a forecast.** The census says the FRONT DOOR refuses the
  file. Whether the solver behind it would then decide the query is not measured
  here and cannot be inferred from these rows.
- **The projection uses share of the SAMPLE**, not share of the winnable set.
  The census shares above (99 %, 100 %, …) are the right number for "what blocks
  the files we lose" and the wrong number to multiply by a division size,
  because `winnable` is itself a measured fraction of the sample.

Every one of the 364 rows returns in about 0.1 s of a 24 s budget — median
23,999 ms of 24,000 unspent. **This is not a slow search that a larger budget
reaches.**

## What blocks the other three divisions

Since the nested-array refusal is *zero* in UFNIA, AUFBV and FP, those divisions
need naming separately — and FP in particular is a single blocker as
concentrated as AUFLIRA's:

- **FP — 98 of 119 winnable rows (82 %) are one reason**:
  `finite quantifier domain (_ FloatingPoint e s) exceeds the eager expansion
  budget`, a SHAPE decline with median 23,990 ms unspent. Plus 10 rows refused
  at the front door for `fp.rem symbolic: format not differentially validated`.
  **108 of 119 FP rows, 91 %, are these two.**
- **UFNIA — the clock is genuinely binding.** 21 rows exhaust the quantified
  solve budget (median 107 ms *over*) and 15 more the instantiation budget. This
  is the one division on the board where more time would plausibly buy verdicts,
  and also the one where we are closest to the references (53 against z3's 96).
- **AUFBV — mixed, and the only division where the ROUND budget leads**: 14
  round-bound rows (median 20,441 ms unspent), 11 clock-bound, 8 where
  `e-matching: no universal is asserted; the nested quantifiers present are
  registered, not instantiated`.

## Three defects, with repros, none fixed here

This is a measurement lane. A board row and a behaviour change in one branch
cannot be told apart afterwards. Details in
[`findings/README.md`](findings/README.md).

1. **A terminal internal error in AUFNIRA, 3 rows.**
   `backend failure: symbol `!int_bv_0` already declared with sort (_ BitVec 32),
   requested (_ BitVec 4)`. Repro: `AUFNIRA/FFT/smtlib.701996.smt2`. This is a
   defect in the code that raised it, not a fragment we cannot decide, and the
   census lists it rather than ranking it beside capability gaps.
2. **Four ABV verdicts (and, pending, several AUFBV ones) that nothing
   confirms** — ADR-1957's motivating case.
3. **`parity-lists/FP.txt` is a plain integer stride**, not full-span. Left
   alone because other lanes' committed artifacts name it; the conformant list
   is `FP-fullspan.txt`.

## The checkers can fail — and two of them could not

`controls/run-all.sh` runs five suites plus a mutation table: **23 mutants, 23
kills**. Every guard is paired with a mutation of the thing it names; every
label has a fixture in which it must appear and one in which it must not.

Three of the five suites found real defects **in their own subjects**, and none
of the three was findable by running the subject over real data:

- `check-core-collisions.sh` printed `NO-CORE-COLLISIONS` over the live fleet
  while being **incapable of reporting a collision** — an off-by-one from awk's
  default space-splitting, and then an apostrophe inside a single-quoted awk
  program that broke the whole script while its control still passed.
- `frame-summary.py` raised `ValueError` on a range pin spec **after** recording
  a frame violation and **before** printing it — an exit status with no finding
  in it.
- `check-core-collisions.sh` again: it reported a clean fleet while two of three
  hosts had nothing pinned and were contributing no evidence.

## Reference frame

BOARD-SIX could write "foreign pinned jobs were ZERO in every one of 363
samples". **This lane cannot** — two other lanes (`quant-rounds`,
`nested-array-ir`) ran pinned work on the same boxes throughout, and the first
launch collided with them. `frame-summary.py` derives the narrower claim that
does hold:

> In all samples, every pin that is not this lane's held physical core **0, 2 or
> 4**. This board used **1, 3, 5, 6, 7**. Disjoint, in every sample.

Load ran 3.3–7.9 (s5), 5.2–7.8 (s6), 4.0–9.9 (s7). The comparison does not rest
on the boxes being hermetic in any case: all three solvers run file N back to
back on the same pinned core, so ambient drift cancels in the *difference*.
Quote the comparison; treat a 1–2 file absolute difference as noise.

## Files

| path | what |
|---|---|
| `AUFLIRA.tsv` `UFNIA.tsv` `ABV.tsv` `ALIA.tsv` `AUFNIRA.tsv` `AUFBV.tsv` `FP.tsv` | the board rows, in pinned-list order |
| `census/*.tsv` | the blocker census over the WHOLE winnable set (603 rows) |
| `winnable/*.txt` | the winnable sets, so the census denominator is re-derivable |
| `confirm-ABV.tsv` `confirm-AUFBV.tsv` | the 600 s re-check of verdicts nothing confirmed |
| `findings/` | the defects, with repros |
| `controls/` | five control suites and the mutation table |
| `PROTOCOL.md` | the method, and the three deliberate differences from board-six |
| `summarize.py` `census-summarize.py` `census-crossdiv.py` `nested-array-reach.py` `frame-summary.py` `check-artifact-integrity.py` | the derivations — every number above is re-derivable |
