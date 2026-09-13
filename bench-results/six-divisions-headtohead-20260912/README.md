# NRA, QF_AUFLIA, BV, AUFLIA, UFLIA, LRA — six divisions measured, six blockmap rows refuted

**2026-09-13, lane `board-six`.** Six divisions totalling **27,201 files** had
never carried a parity row. `blockmap.txt` marked every one of them blocked or
stuck, on a **three-file sample** each. Not one of those six rows survives
n = 200.

    axeyum   692 / 1200  (57.7 %)
    z3      1048 / 1200  (87.3 %)
    cvc5     996 / 1200  (83.0 %)

| division | files on disk | axeyum | z3 | cvc5 | best ref | winnable |
|---|---:|---:|---:|---:|---:|---:|
| NRA       |  3,819 | **193** | 199 | 198 | 199 |   6 |
| BV        |  6,185 | **148** | 179 | 182 | 189 |  41 |
| QF_AUFLIA |  1,303 | **140** | 200 | 200 | 200 |  60 |
| AUFLIA    |  3,327 |  **84** | 161 | 122 | 162 |  79 |
| UFLIA     | 10,128 |  **71** | 139 | 142 | 144 |  73 |
| LRA       |  2,439 |  **56** | 170 | 152 | 187 | 131 |

`best ref` is the per-file better of the two references, which is a harder
denominator than either alone. *winnable* = we returned `unknown` and a
reference decided.

## The six blockmap verdicts, each with its n

`bench-results/session-20260911-smtlib/coverage/blockmap.txt` carries a
`PARTLY REFUTED` banner because four of its rows had already been measured
wrong. These six make it **ten**. Each row records whichever refusal the first
sampled file happened to hit and prints that as the division's verdict.

| division | blockmap row (n = 1–3) | verdict at n = 200 |
|---|---|---|
| NRA | `auto error 6 unsupported by backend: lazy SMT:` | **REFUTED.** 193/200 — within 6 of z3 and 5 of cvc5. |
| BV | `auto error 0 unsupported by backend: term #92` | **REFUTED.** 148/200. No file in the 41-row census ends on any `unsupported by backend` reason. |
| LRA | `auto error 3 unsupported by backend: lazy SMT:` | **REFUTED.** 56/200. Not one census row names lazy SMT. |
| QF_AUFLIA | `auto unknown 6114 UnknownReason { kind: Timeout` | **REFUTED as a blocker; the *kind* survives.** 140/200, and `Timeout` is the top census reason (37 of 60) — but the division decides 70 %, which the row does not suggest. |
| AUFLIA | `auto unknown 5 UnknownReason { kind: Incomplete` | **REFUTED as a blocker; the *kind* survives.** 84/200; `Incomplete` is 73 of 79 census rows. |
| UFLIA | `auto unknown 3 UnknownReason { kind: Incomplete` | **REFUTED as a blocker; the *kind* survives.** 71/200. |

Three rows claimed a hard `unsupported by backend` **error**. All three are
wrong: those divisions decide 193, 148 and 56 of 200. **12,443 files were
written off on the evidence of five.** The other three rows are not false so
much as uninformative — a division that decides 71 to 140 of 200 is weak, not
blocked, and the row cannot tell you which.

## Soundness: 0 disagreements in 3,600 solves, and the zero is not vacuous

Every verdict **we** produce, against three independent checks:

| division | we decided | vs `:status` | vs z3 4.13.3 | vs cvc5 1.3.4 | disagreements |
|---|---:|---:|---:|---:|---:|
| NRA       | 193 | 193/193 | 193/193 | 193/193 | **0** |
| QF_AUFLIA | 140 | 140/140 | 140/140 | 140/140 | **0** |
| BV        | 148 | 148/148 | 146/148 | 148/148 | **0** |
| AUFLIA    |  84 |   84/84 |   83/84 |   73/84 | **0** |
| UFLIA     |  71 |   71/71 |   70/71 |   71/71 | **0** |
| LRA       |  56 |   56/56 |   53/56 |   56/56 | **0** |
| **TOTAL** | **692** | **692/692** | **685/692** | **681/692** | **0** |

The middle columns are what make the zero mean something. A zero-disagreement
figure over verdicts nothing else checked is worth nothing; here **every one of
the 692 verdicts is confirmed by the benchmark's own declared `:status`**, 99.0 %
by z3 and 98.4 % by cvc5. **Reference-vs-reference conflicts: 0** in all six
divisions, so the ground truth the checks rest on is not itself in dispute.

**No row in any of the six boards is `wrapper-killed`, on any solver.** The
measurement wall was never hit — the thing a previous census got wrong by using
`timeout 32` around a 24 s budget and manufacturing 17 false "no reason" rows.

**cvc5's column is a floor, not its capability.** 138 of its 1,200 runs ended
`rc134` — the protocol's 8 GiB address-space cap — and all 138 score undecided
(LRA 48, UFLIA 43, AUFLIA 27, BV 18, NRA 2). The cap is applied identically to
all three solvers; z3 and axeyum hit it **0** times. **Name z3 as the reference
when quoting the AUFLIA and LRA gaps.**

We decide 7 files z3 does not (LRA 3, BV 2, AUFLIA 1, UFLIA 1) and 11 that cvc5
does not (all AUFLIA).

## The one cross-division finding, and it is not the one that was predicted

This lane's brief expected the dominant non-array blocker to be
**`quantified solve time budget exhausted after e-matching`** — a wall-clock
budget — and asked whether it is one finding across four divisions or five
separate ones. It is one finding across four divisions. **It is a different
one.**

That clock reason is **24 of 390** winnable files. The dominant blocker is its
neighbour, and the difference between them is the whole point:

    family                                  kind    NRA  QF_AUFLIA   BV  AUFLIA  UFLIA   LRA   tot
    e-matching ROUND budget                 ROUND     1          0   10      48      1   117   177
    array lazy-ROW / extensionality         ARRAY     0         56    0       0      0     0    56
    mbqi -> BV backend, uninterpreted sort  SHAPE     0          0    0      24     14     0    38
    e-matching CLOCK budget                 CLOCK     4          0    0       0     20     0    24
    e-matching instantiation CLOCK          CLOCK     0          0    2       5     10     6    23
    finite BV domain too big to expand      SHAPE     0          0   18       0      0     0    18
    instantiation sat, universal unrefuted  SHAPE     0          0    6       1      0     0     7
    e-matching has no universal             SHAPE     0          0    1       0      1     5     7

    by kind:  ROUND 179   SHAPE 70   ARRAY 56   CLOCK 48   OTHER 5

**`e-matching instantiation did not refute within the round budget` is 177 of
390 winnable files (45 %), across four divisions.** And it is not a slow search:

    family                    n   ms_left: min      median      max
    e-matching ROUND budget 177          -205      23,994   23,999

**The median such row gives up with 23,994 ms of its 24,000 ms budget
unspent.** Raw rows from `census/LRA.tsv` read `attempts=19  bound_ms=0
total_ms=3` — nineteen dispatch rungs tried and declined in **three
milliseconds**.

That is measured twice, by two instruments that do not share a clock. The
`--trace` `total_ms` above is the solver's own accounting; the board TSV's
`ax_s` is the harness's wall clock around the whole process. They agree:

    division   winnable   axeyum wall on winnable rows: med      under 1 s
    LRA             131                                0.11 s    106  (80 %)
    BV               41                                0.11 s     29  (70 %)
    AUFLIA           79                               10.21 s     11  (13 %)
    QF_AUFLIA        60                               24.13 s      6  (10 %)
    UFLIA            73                               24.13 s      1  ( 1 %)
    NRA               6                               24.03 s      1  (16 %)

**So the six divisions are two populations, not one**, and the board's shape
hides that while the census makes it obvious:

- **LRA and BV decline, they do not time out.** 80 % and 70 % of what we fail to
  decide comes back in ~0.11 s of a 24 s budget. z3 decides 170 LRA and 179 BV.
  We are leaving 24 seconds unused on files a reference decides.
- **UFLIA, QF_AUFLIA and NRA genuinely burn the clock.** 99 %, 90 % and 84 % of
  their winnable rows run past 1 s, most to the full budget.
- **AUFLIA is mixed**, and its own census splits the same way: 48 round-budget
  rows beside 24 `mbqi`-declines and 5 clock exhaustions.

### Is the round budget worth raising, or is it a capability gap?

**This lane does not answer that and must not** — a cap turns a slow `unknown`
into a fast one, and an A/B is the only thing that can tell the difference. What
it can say, and did measure:

- The lever is a **round count**, not a time budget. The clock is not the
  binding constraint on 177 of 390 files; something gives up after N rounds with
  the budget almost untouched.
- The prize is **sized and pinned**: `winnable/LRA.txt` (131), `AUFLIA.txt`
  (79), `BV.txt` (41), and the exact 177 rows are greppable out of
  `census/*.tsv` by their give-up detail.
- The warning is in the same table. 48 rows in these divisions *are* clock-bound
  (`CLOCK`), and 70 are `SHAPE` — fragments where neither budget helps, like the
  38 `mbqi`-to-BV-backend declines and the 18 BV-domain expansions. Raising a
  round cap cannot touch those 118, and on the 177 it may simply move the time.

### `attempts=` would have suppressed most of this — ADR-1941 again

[ADR-1941](../../docs/research/09-decisions/adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md)
makes the **`route-open` segment**, not `attempts=`, the discriminator for
`UNCLASSIFIED`. This board is its second independent test and it matters more
here than it did on the lane that wrote it:

| division | rows | `attempts=`-only would call UNCLASSIFIED | actually carry an open segment |
|---|---:|---:|---:|
| QF_AUFLIA | 60 | 59 | **1** |
| LRA | 131 | 3 | **2** |
| BV | 41 | 21 | **1** |
| AUFLIA | 79 | 5 | **0** |
| NRA | 6 | 4 | **0** |
| UFLIA | 73 | 64 | **25** |

On `QF_AUFLIA` the naive rule discards **59 of 60 rows** and the division's
census becomes empty. Ladder length is query-dependent — QF_AUFLIA rows end at
`attempts=` 7, 10, 12, 15, 19, 20, 21 and 25 on the *same* reasons. Both
readings are published side by side on every division, as ADR-1941 step 6
requires.

`UFLIA` is the case ADR-1941 exists to keep honest in the other direction: **25
of its 73 rows really do carry an open segment** (17 after `q:egraph`, 4 after
`q:mbqi-quick`, 4 after `q:uf-fmf-probe`) and are excluded from every ranking
above. Its census is 47 rankable rows of 73, and that is stated rather than
papered over.

## Two defects, with repros, neither fixed here

See `findings/README.md`.

1. **`(declare-sort Set 0)` is refused, and the error names `_` instead of
   `Set`.** Two-line repro. Legal SMT-LIB; the sort name alone triggers it
   (14 other names decide `sat` through the identical template). Sized honestly:
   **3 files in 27,201**, so fix it for the wrong error message, not for
   coverage.
2. **`mbqi` routes an uninterpreted sort into the BV bit-blaster and declines**
   — 38 files (AUFLIA 24, UFLIA 14), the third-largest reason on the board.

Both return `unknown`. Neither is a soundness problem.

## Protocol

Matches `bench-results/fpbv-divisions-headtohead-20260912` (lane BOARD-FPBV,
ADR-1941) and `bench-results/dt-divisions-headtohead-20260912`.

- **200 files per division, sampled FULL-SPAN**, committed at **`5aaa3848b`
  BEFORE anything was measured.** That commit is what makes these rows
  non-cherry-picked. Indices are 200 points evenly spaced over `0 .. N-1`
  inclusive (`mklist.py`), **not** the plain `N//200` integer stride, which
  stops at `199*(N//200)` and drops the tail families. Family coverage of each
  sample is printed by `mklist.py` and is 2/3, 6/7, 13/15, 3/3, 9/14, 5/5; every
  family missed is 1–32 files, which is what 200 draws from 10,128 is expected
  to miss, not a defect in the span.
- **24 s wall, 8 GiB address space**, three solvers **interleaved per file**
  (all three finish file N before any starts N+1) on one pinned physical core,
  with the solver that goes first **rotating** per file.
- **Units differ and mixing them silently corrupts a board**: `z3 -T:24`
  SECONDS, `cvc5 --tlimit=24000` MILLISECONDS.
- **Wrapper timeout is 24 + 16 s** and every run records its own outcome in a
  `*_k` column. **Zero rows hit the measurement wall.**
- **The row key is the PATH, not the basename.**
- **Live probe before any measurement**, on every host: all three solvers had to
  decide something across the six divisions with the exact binaries and flags
  the board would use. `probe.sh`, `PROBE-OK` on s5, s6 and s7.
- Two divisions per box, run in sequence, two modulo-interleaved shards each on
  distinct physical cores (`0,8` and `2,10`). Two shards, not three: the 8 GiB
  cap is per run and these boxes have 26 GB. `merge-division.py` and
  `census-merge.py` **abort** on an incomplete shard set rather than writing a
  smaller denominator.
- Solvers: axeyum built from this branch, z3 4.13.3, cvc5 1.3.4. Boxes s5/s6/s7,
  Ryzen 7 7840HS, 26 GB.

### The reference frame, measured rather than asserted

`loadframe.tsv` sampled each box's 1-minute load and its count of foreign
`taskset` pins every 30 s for the life of the run — **363 samples, and foreign
pinned jobs were ZERO in every one.** load1 ran 0.16–4.04 (s5), 1.02–4.28 (s6),
1.94–4.12 (s7), almost all of it this lane's own two shards plus roughly 2.0 of
ambient *unpinned* work. The comparison does not rest on the boxes being
hermetic in any case: all three solvers run file N back to back on the same
pinned core, so ambient drift cancels in the *difference*. Quote the comparison;
treat a 1–2 file absolute difference as noise.

### The binary

Built from scratch in an empty target dir on this branch
(`build.sh`, 3 m 24 s) and verified newer than every `crates/**/*.rs` before use
— the check is inside `build.sh` and aborts, because cargo decides freshness by
mtime and a stale prebuilt binary reported a false ABSENT four times in this
repository on 2026-09-12.

**No solver code changed in this lane.**

## The checkers can fail

`controls/run-controls.sh` runs each checker against a fixture containing
exactly the finding it exists to report — including a row where every solver
agrees, which must produce **nothing**, because a checker that flags everything
has a zero worth as little as one that flags nothing.
`controls/mutants.py` breaks each subject and requires the naming guard to die:
**nine mutants, nine kills**, including two that revert ADR-1941 and one that
publishes only one of its two readings.

## Files

| path | what |
|---|---|
| `NRA.tsv` `QF_AUFLIA.tsv` `BV.tsv` `AUFLIA.tsv` `UFLIA.tsv` `LRA.tsv` | the board rows, in pinned-list order |
| `census/*.tsv` | the blocker census over the WHOLE winnable set (390 rows) |
| `winnable/*.txt` | the winnable sets, so the census denominator is re-derivable |
| `findings/` | the two defects, with repros |
| `controls/` | the checkers' fixtures and mutants |
| `mklist.py` `build.sh` `probe.sh` `launch.sh` `chain-run.sh` `shard-run.sh` `census-run.sh` `loadframe.sh` | the runners |
| `merge-division.py` `census-merge.py` `summarize.py` `census-summarize.py` `census-crossdiv.py` | the derivations — every number above is re-derivable, not transcribed |
