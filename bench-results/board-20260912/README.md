# The board after 2026-09-12 — 20 divisions, one denominator

Every row: 200 files, 24 s budget, one box, serial, three solvers interleaved
per file. `best ref` is the better of z3 4.13.3 and cvc5 1.3.4 **per division**,
which is a harder denominator than either solver alone.

| division | axeyum | best ref | gap |
|---|---:|---:|---:|
| UFDTNIRA * | 5 | 183 | **178** |
| AUFDTLIRA * | 41 | 176 | **135** |
| UFDTLIRA * | 72 | 181 | **109** |
| QF_NIA | 41 | 144 | **103** |
| QF_NRA | 117 | 187 | 70 |
| QF_LRA | 107 | 166 | 59 |
| QF_LIA | 119 | 172 | 53 |
| QF_UFLRA | 146 | 198 | 52 |
| UFDT * | 26 | 78 | 52 |
| QF_IDL | 113 | 140 | 27 |
| QF_DT | 171 | 192 | 21 |
| QF_UFLIA | 167 | 186 | 19 |
| QF_RDL | 152 | 166 | 14 |
| QF_S | 186 | 197 | 11 |
| QF_ABV | 186 | 195 | 9 |
| UF | 90 | 93 | 3 |
| QF_SLIA | 193 | 194 | 1 |
| QF_FP | 199 | 199 | 0 |
| QF_UF | 200 | 200 | 0 |
| QF_BV | 186 | 185 | **-1** |
| **TOTAL** | **2517** | **3432** | **915** |

`*` = measured for the first time on 2026-09-12.

**2,517 of 4,000 (62.9%)** against best-ref **3,432 (85.8%)**.

## Read the direction of that number correctly

On the 16 divisions tracked before today we are at **74.2%**. Adding four
divisions we had never measured takes the figure to **62.9%**. That is not a
regression — it is the number becoming honest. The four new divisions are
quantified-heavy, which is where we are weakest, and they were absent from every
prior percentage anyone quoted.

The same caution applies to what is still unmeasured: **20 of 84 divisions**.
Any headline from this file is a claim about these 20, not about SMT-LIB.

## What moved today, and what did not

| lane | division | moved |
|---|---|---|
| QF-DT-FOLD | QF_DT | **+57** (114 -> 171), two shipped wrong `unsat`s fixed |
| DT-DIVISIONS | four new | **+51** (93/800 -> 144/800), AUFDTLIRA 0 -> 41 |
| WATCHDOG-RESIDUAL | QF_UFLRA | **+2**, watchdog kills 92 -> 81 over 98 files |
| DEADLINE-OVERRUN | QF_UFLIA, QF_UFLRA | **+7** |
| QF-NIA-WIDTH | QF_NIA | **0** — measured "do not build", the lever only |
| QF-NRA-ROUTE | QF_NRA | **0** — a real defect fixed; an error and an `unknown` are both "not decided" |

Two lanes moved nothing and both were worth running: each replaced a wrong
hypothesis with a measurement, and QF-NRA's turned 13 files reported for months
as "the clock ran out" into the CAD wall they actually are.

## Where the gap is

**QF_NIA, QF_NRA, QF_LRA, QF_LIA = 285 files**, and the three new UFDT* rows add
**422** more. Together that is 707 of 915.

What is already known about them, so nobody re-derives it:

- **QF_NIA** — not a width problem (ADR-1921: escalation decides 0 of 110,
  costs 4.6% wall). Next: the preprocessed dispatch timeout, 41 of 110.
- **QF_NRA** — 46 of 77 (60%) is the linear abstraction's own boundary, and the
  rows say so: *"this needs an nlsat/CAD engine"* (ADR-0058 Phase C/D). A
  capability statement, not a performance one.
- **QF_LRA** — not the clock: **0 of 40 decide even at a 120 s budget**. The
  route is wrong for these problems rather than slow.
- **QF_LIA** — 48 of 55 burn the whole budget; 28 are watchdog kills. Nothing
  diagnosed beyond that. The largest gap with no explanation.
- **UFDT\*** — corrected census over the 600 files where the ladder now runs to
  the end: UF applied to a datatype argument **143**, array/UF-sorted datatype
  fields in `datatype_native` **152**. ADR-1920's "build next" covers only the
  first.
- **QF_IDL** — cleanly bimodal: 19 killed, 19 declining early, nothing between.
- Undiagnosed and unclaimed: the **~42 early decliners** in QF_LRA and QF_IDL.

## Four wrong censuses in one session

Recorded because the pattern cost more than any single bug:

1. QF_NIA's width class — 50% in a 14-file sample, 24% over all 110.
2. The watchdog — 57 in a 24-file-per-division sample, 149 board-wide, and only
   **2** of QF_UFLRA's 51 convert. A census of a failure MODE is not a count of
   fixable files.
3. The DT blockmap — 3 files per division named an error appearing in 0 of 160.
4. The DT blocker census — measured the **dispatch ladder**, not the solver. Its
   top blocker was 174 of 200 before a dispatch fix and 3 of 200 after.

The first three are one cause: these file lists are path-sorted, so a small
sample is a sample of one family. The fourth is different and worse — the
instrument was wrong, not the sample. `attempts=` in `--trace` is the check.
