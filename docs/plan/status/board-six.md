# Lane: board-six — the six unmeasured non-array divisions

<!-- plan-section: lane-status -->

**Lane board-six (`DONE`, board-six, 2026-09-13).** `NRA` (3,819 files),
`QF_AUFLIA` (1,303), `BV` (6,185), `AUFLIA` (3,327), `UFLIA` (10,128) and
`LRA` (2,439) — **27,201 files** — had never carried a parity row. They do now.
Pure measurement: **no solver code changed.**

    division     files   axeyum    z3   cvc5   best ref
    NRA          3,819      193   199    198        199
    BV           6,185      148   179    182        189
    QF_AUFLIA    1,303      140   200    200        200
    AUFLIA       3,327       84   161    122        162
    UFLIA       10,128       71   139    142        144
    LRA          2,439       56   170    152        187
    total                   692  1048    996       1081   (of 1200)

**All six `blockmap.txt` rows are REFUTED at n = 200.** Three claimed a hard
`unsupported by backend` **error** (NRA and LRA "lazy SMT", BV "term #92"); we
decide 193, 56 and 148 of 200, and **0 of the 178 census rows across those three
divisions names `lazy SMT` or `term #`**. **12,443 files were written off on the
evidence of five sampled files.** The other three rows (`unknown` /
`Timeout` / `Incomplete`) are not false but uninformative: those divisions decide
71 to 140 of 200 — weak, not blocked. The blockmap is annotated in place; **13 of
its 20 rows are now measured at n ≥ 40, 7 are still 3-file samples.**

**Soundness: 0 disagreements across all 3,600 solves**, and the zero is not
vacuous — **all 692 of our verdicts are confirmed by the benchmark's own declared
`:status`**, 685 by z3 4.13.3 and 681 by cvc5 1.3.4. Reference-vs-reference
conflicts 0 in every division. **0 wrapper-killed rows on any solver** — the
measurement wall was never hit. (cvc5 has 138 `rc134` rows, the protocol's 8 GiB
cap, which z3 and axeyum hit 0 times; **quote z3** on AUFLIA and LRA.)

Lists pinned at `5aaa3848b` **before** anything ran. Boards at `5511b7954`
(NRA, BV) and `5cdd11f6d` (the other four).

**The cross-division finding is real, is one finding, and is NOT the predicted
one.** The brief expected `quantified solve time budget exhausted after
e-matching` — a wall clock — to dominate. It is **24 of 390** winnable files. The
dominant blocker is `e-matching instantiation did not refute within the round
budget`: **177 of 390 (45 %), across four divisions** (LRA 117, AUFLIA 48,
BV 10, NRA 1) — and **its median row gives up with 23,994 ms of its 24,000 ms
budget unspent.** Raw rows read `attempts=19 bound_ms=0 total_ms=3`: nineteen
dispatch rungs tried and declined in **three milliseconds**. Two independent
clocks agree — the solver's own `total_ms` and the harness's wall clock, which
shows **106 of 131 LRA and 29 of 41 BV winnable rows returning in under 1 s**.

So the six split into two populations the board alone hides: **LRA and BV
decline (80 % / 70 % of misses in ~0.11 s); UFLIA, QF_AUFLIA and NRA genuinely
burn the clock (99 % / 90 % / 84 % run past 1 s); AUFLIA is mixed.** By remedy:
**ROUND 179, SHAPE 70, ARRAY 56, CLOCK 48.**

**This lane did NOT raise any budget, deliberately** — a cap turns a slow
`unknown` into a fast one, and only an A/B over the pinned population can say
whether it buys anything. The 118 `SHAPE` + `CLOCK` rows are the warning: a
round cap cannot touch them.

**[ADR-1950](../../research/09-decisions/adr-1950-a-round-budget-and-a-clock-budget-are-different-findings-and-a-census-must-not-merge-them.md)
came out of this** — a census must split "budget exhausted" by WHICH budget and
publish the remaining-budget distribution beside the count, because the merged
bucket reads as the wrong one and the remedies do not overlap.

**ADR-1941 is load-bearing again**, harder than on the lane that wrote it: the
`attempts=`-only reading would call **59 of 60** QF_AUFLIA rows UNCLASSIFIED
(only 1 carries an open segment) and 21 of 41 BV rows (only 1). It also cuts the
other way and is honoured: **25 of UFLIA's 73 rows really do carry an open
segment** and are excluded from every ranking, leaving 47 rankable.

**Two defects, with repros, neither fixed here.** (a) `(declare-sort Set 0)` is
refused and the error names ``sort `_` `` — a sort not in the file; two-line
repro, and the *name* alone triggers it (14 other names decide `sat` through the
identical template). Sized honestly: **3 files in 27,201** — fix the message, not
for coverage. (b) `mbqi` routes an uninterpreted sort into the BV bit-blaster and
declines: **38 files** (AUFLIA 24, UFLIA 14), the third-largest reason on the
board. Both return `unknown`; neither is a soundness problem.

Checkers mutation-tested: **nine mutants, nine kills.** Reference frame measured,
not asserted: **363 loadframe samples, zero foreign pinned jobs on every host.**

**Next actions.** (a) A/B the e-matching **round** cap over `winnable/LRA.txt`
(131), `AUFLIA.txt` (79) and `BV.txt` (41) — a sized, pinned population, and the
lever is a count, not a time limit. (b) The 38 `mbqi`→BV-backend declines.
(c) The `declare-sort Set` parse defect. (d) 7 blockmap rows remain unmeasured.

<!-- plan-section: landed-changes -->

| 2026-09-13 | board-six | First parity rows for NRA / QF_AUFLIA / BV / AUFLIA / UFLIA / LRA (27,201 files): 193 / 140 / 148 / 84 / 71 / 56 of 200 vs z3 199 / 200 / 179 / 161 / 139 / 170, **0 disagreements, 0 wrapper kills**; all six blockmap rows refuted; ADR-1950; 177 of 390 winnable files stop at a ROUND cap with 23,994 ms of 24,000 unspent |
