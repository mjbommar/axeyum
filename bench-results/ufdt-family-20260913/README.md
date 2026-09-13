# The three UFDT siblings, censused whole — and they are held by three different things

**2026-09-13, lane `UFDT-FAMILY`.** `UFDTNIRA` (4,424 files), `UFDTLIRA`
(7,749) and `UFDT` (4,569) were briefed as one target: the same
datatype+arithmetic shape, the siblings of `AUFDTLIRA`, which went
0 → 41 → 69 → 71 → 90 → 110 in one day on datatype and dispatch work
(ADR-1927 / ADR-1935 / ADR-1942 / ADR-1946 / ADR-1966). The question was how
much of that transfers.

**It transferred enormously, and it is already on `main`.** The first thing
this census found is that the brief's own board row is stale by 69 files.

## 1. The board row, re-measured on the current tree

Our verdicts are this lane's run at `9fe59f4e2`; the z3 / cvc5 / `:status`
columns are read from the **pinned boards**
(`bench-results/dt-divisions-headtohead-20260912/`) and are not re-derived — a
reference verdict at a fixed budget on a fixed file does not change. Same
envelope as those boards: **24 s wall, 8 GiB `ulimit -v`, one pinned physical
core** on idle `s5`/`s6`/`s7`. Re-derive with `summarize.py`.

| division | pinned board | **here** | z3 | cvc5 | best ref | winnable (was) |
|---|---:|---:|---:|---:|---:|---:|
| UFDTNIRA | 5 / 200 | **74 / 200** | 173 | 183 | 183 | **109** (178) |
| UFDTLIRA | 66 / 200 | **105 / 200** | 181 | 158 | 181 | **76** (115) |
| UFDT | 22 / 200 | **31 / 200** | 66 | 78 | 80 | **51** (60) |

`UFDTNIRA` is **5 → 74**, not 5. The brief sized it at "5 of 200, 178 winnable,
the biggest refutation-bound population on any board"; on the tree as it stands
that population is **109**, and the 69 files that closed were closed by other
lanes' datatype and dispatch work landing on `main` between the board being
taken and this census. **Verify a blocker still exists before treating it as
one** is this repository's own rule, and the brief that sent this lane did not.

**Soundness, with the comparable denominator on the same line (ADR-1957):**

    UFDTNIRA  74 verdicts   vs :status 67/67   vs z3 74/74   vs cvc5 74/74   DISAGREEMENTS: 0
    UFDTLIRA 105 verdicts   vs :status 105/105 vs z3 105/105 vs cvc5 105/105 DISAGREEMENTS: 0
    UFDT      31 verdicts   vs :status 27/27   vs z3 27/27   vs cvc5 29/29   DISAGREEMENTS: 0

No zero here is vacuous: **215 + 315 + 83 = 613 independent comparisons** stand
behind them. `summarize.py` exits non-zero on any disagreement, so the exit
status depends on the finding.

**Polarity of the remaining winnable set** (re-derived on the NEW winnable
sets, not inherited from the stale `winnable-polarity-20260913` table):
`UFDTNIRA` 109 unsat / **0 sat**, `UFDT` 50 unsat / 1 sat, `UFDTLIRA` 53 unsat
/ 23 sat. The bimodal shape the polarity table describes survives the
correction; the absolute sizes do not.

## 2. The census — all 236 winnable rows, not a sample

One pass over each pinned 200 yields BOTH the board row and the census row, so
this is a projection of one measurement rather than two
(`census-run.sh` → `merge-division.py` → `cut-to-winnable.py` →
`census-summarize.py`). ADR-1936 / ADR-1941 / ADR-1950 / ADR-1956 all apply and
all are enforced by the summarizer, not by prose.

    by kind:  SHAPE 123   CLOCK 101   OTHER 2
              UNCLASSIFIED (ADR-1941) 10       no route trail at all 0
              rc=124 wrapper-killed 0          rc=134 (8 GiB cap) 0

| family | kind | UFDTNIRA | UFDTLIRA | UFDT | tot |
|---|---|---:|---:|---:|---:|
| **valid-universal elimination CLOCK** | CLOCK | **56** | 0 | 0 | **56** |
| **mbqi: datatype ARGUMENT congruence not exact** (ADR-1935) | SHAPE | 0 | **29** | **20** | **49** |
| ladder CLOCK exhausted after e-matching | CLOCK | 25 | 2 | 3 | 30 |
| **mbqi: datatype RESULT expansion not exact** (ADR-1946) | SHAPE | 0 | 9 | 16 | 25 |
| e-matching FIXPOINT (no instance left to admit) | SHAPE | 2 | 7 | 6 | 15 |
| instantiation sat, universal unrefuted | SHAPE | 0 | 13 | 0 | 13 |
| e-matching instantiation CLOCK | CLOCK | 12 | 0 | 0 | 12 |
| **mbqi: UF on a non-atomic datatype term** (ADR-1920/1942) | SHAPE | 0 | 11 | 0 | 11 |
| mbqi: uninterpreted sort the BV backend cannot blast | SHAPE | 3 | 3 | 0 | 6 |
| bounded integer width | SHAPE | 2 | 1 | 0 | 3 |
| e-matching GROWTH-HEADROOM (a clock exit) | CLOCK | 2 | 0 | 1 | 3 |
| *(OTHER, printed in full by `census-summarize.py`)* | OTHER | 1 | 1 | 0 | 2 |
| mbqi declined, other cause | SHAPE | 0 | 0 | 1 | 1 |

### Two splits this census had to make, and what a merged bucket would have said

**`quantified solve time budget exhausted after <stage>` is four different
rungs.** ADR-1950's rule is about which BUDGET; the same collapse happens one
level up, over which STAGE. Merged, `UFDTNIRA` reads "56 rows, the quantified
ladder ran out of time" — a finding with no lever in it. Split, it reads
"56 rows, **valid-universal elimination** ran out of time", which names one
function.

**`mbqi declined an unsupported fragment: …` is at least four causes.** This is
ADR-1956's defect verbatim, one stage over: a shared prefix with the
discriminating text after a colon. Merged it is one 92-row bucket. Split, the
**three named datatype-exactness preconditions** of ADR-1920 / ADR-1935 /
ADR-1946 are **85 of those 92**, and the largest of them is a single named
precondition on 49 files across two divisions.

### ADR-1950: which budget, and the labels' own test

| family | kind | n | ms_left min | **median** | max | reading |
|---|---|---:|---:|---:|---:|---|
| valid-universal elimination | CLOCK | 56 | −77 | **−46** | −30 | genuinely clock-bound |
| mbqi: ARGUMENT congruence (1935) | SHAPE | 49 | 19,049 | **23,982** | 23,998 | clock never involved |
| ladder CLOCK after e-matching | CLOCK | 30 | −982 | **−49** | −12 | genuinely clock-bound |
| mbqi: RESULT expansion (1946) | SHAPE | 25 | 22,379 | **23,948** | 23,999 | clock never involved |
| instantiation sat, unrefuted | SHAPE | 13 | 23,408 | **23,997** | 23,999 | clock never involved |
| e-matching instantiation | CLOCK | 12 | 1,030 | **5,945** | 10,948 | MIXED — two populations |
| mbqi: UF on datatype term (1920/1942) | SHAPE | 11 | 23,864 | **23,967** | 23,997 | clock never involved |

Counting rows that gave up **past** the 24,000 ms deadline, per kind, is the
direct test of the labels:

    CLOCK   86 of 101      SHAPE   1 of 123      OTHER   1 of 2

**ADR-1956 holds on three more divisions.** `e-matching ... did not refute
within the round budget` — the string that was 45 % of the six-division board —
appears **0 times** in 236 winnable rows here. The loop's exits that do appear
are FIXPOINT (15) and GROWTH-HEADROOM (3), both of which ADR-1956 established
are not round budgets. No row in any of the three divisions reaches the
instantiation round ceiling.

**No nested-array refusal appears anywhere** — 0 of 236 — so ADR-1965's array-IR
ceiling does not reach these divisions.

## 3. The answer to "why is UFDTNIRA at 5 when UFDTLIRA is at 102"

The brief called the 20x gap "the most informative number you have". It was,
but not for the reason the brief expected: **on the current tree the gap is
74 vs 105, and the two divisions are held by completely different things.**

- **`UFDTNIRA` is COST-bound.** 93 of its 103 classified winnable rows are
  CLOCK, and 56 of them are one rung: valid-universal elimination. Zero rows
  carry a datatype-exactness refusal.
- **`UFDTLIRA` and `UFDT` are SHAPE-bound, by the SAME family.** 49 + 25 + 11 =
  85 of their 127 classified rows are the three datatype-exactness
  preconditions, every one of them declining with **essentially the whole 24 s
  budget unspent** (median 23.9 s of 24 s). Two CLOCK rows between them.

All three are the same benchmark family on disk — `UFDTNIRA`, `UFDTLIRA` and
`AUFDTLIRA`'s pinned 200 are **200/200 SPARK 2014** (`20200306-Kanig`), and
`UFDT` is a different corpus entirely (`20170428-Barrett`, the CVC4 datatype
papers). So the split is not a corpus artifact: the same generator produces
files that are clock-bound in the nonlinear division and shape-bound in the
linear one. `UFDTNIRA`'s files are also **3.6x larger** (median 41 KB against
11.5 KB).

**What transfers, then:** the `AUFDTLIRA` work already transferred — it is what
took `UFDTNIRA` from 5 to 74 and `UFDTLIRA` from 66 to 105 before this lane
started. **What is left over is two separate targets, and only one of them is
a datatype capability at all.**

## 4. Target A — valid-universal elimination holds the whole clock (56 rows)

`finish_quantified_solve` runs valid-universal elimination near the top of the
quantified ladder. The pass is a sat-side universal-closure validity check: a
top-level `∀x. body` with a quantifier-free body is valid iff `¬body[x := c]`
is unsat for a fresh `c`, and a proven-valid universal is replaced by `true`.
It runs **one quantifier-free SUB-SOLVE per top-level assertion**, each handed
`config_with_remaining_timeout(config, deadline)` — the ladder's whole
remaining wall clock.

On `UFDTNIRA` that is what happens: **56 winnable rows (and 69 of the pinned
200) spend the entire budget inside the pass and give up PAST the deadline**,
median 46 ms over, and the seventeen-odd rungs below it never run at all. This
is the exact shape ADR-1970 measured for `q:egraph` on `UFNIA`/`UFLIA`, in a
different rung, on a division where it is three times bigger.

Polarity is right for it: `UFDTNIRA`'s 109 winnable are **109 unsat, 0 sat**, so
handing clock to the refutation rungs below is aimed at a population made
entirely of refutations (the ADR-1971 check, applied before sizing).

Decline time is right for it too, in the direction ADR-1971 warns about in
reverse: these rows do not decline in 0.11 s with no route running — they
consume 24,000 ms. A route IS running. The question is only whether a
DIFFERENT route would decide the file with that clock, and that is what the
ceiling arm measures.

**Sizing bracket, stated before the arm ran: between 0 and 56.** The running
blocker→reachable tally in this project (143→6, 51→2, 173→10, 84→49,
27,150→1,135, 19,620→0, 177→0, 934→0, 46→2) says the distribution is
concentrated near zero, and the two nearest precedents are the two nulls:
ADR-1970's reserve on the same shape was worth +4/−2 inside its own noise band,
and ADR-1971's target was worth 0. A blocker count is not a reachable count
(ADR-1945).

The measurement is in section 6.

## 5. Target B — the datatype-exactness preconditions (85 rows), sized and handed off

Not built here. It is the bigger number and it is the one that is actually a
datatype capability, so it is written down with what the census can say about
it rather than guessed at.

| precondition | ADR | UFDTLIRA | UFDT | tot | median ms_left |
|---|---|---:|---:|---:|---:|
| congruence over a datatype ARGUMENT whose expansion is not exact | 1935 | 29 | 20 | **49** | 23,982 |
| a UF whose RESULT datatype's expansion is not exact | 1946 | 9 | 16 | **25** | 23,948 |
| a UF applied to a datatype term that is neither a free variable, a constructor application, nor another UF | 1920/1942 | 11 | 0 | **11** | 23,967 |

What is known, and what a lane taking this must establish before building:

- **Polarity differs sharply between the two divisions.** `UFDT`'s winnable is
  50 unsat / 1 sat; `UFDTLIRA`'s is 53 unsat / **23 sat**. MBQI is a MODEL
  builder, so on `UFDTLIRA` it is aimed at both halves — which is unusual for
  this project's targets and makes it more attractive, not less. But a
  refutation-only fix has a ceiling of 53, not 76.
- **These are conservative refusals, not missing code.** Each names an
  exactness precondition that exists because the encoded equality would be
  WEAKER than the real one — the failure mode is a wrong `unsat`, which is
  why ADR-1935 chose exactness over scalarity in the first place. This is
  soundness-critical work and the standard is ADR-1965's: delete one guard and
  require that exactly one test dies, over SATISFIABLE fixtures.
- **ADR-1966's check has not been run on these three refusal sites.** A rung
  BELOW may own the construct, in which case the refusal should be a DECLINE
  and not the query's verdict, and the fix is much smaller than a capability.
  `scripts/enumerate-dispatch-refusal-propagation.py` enumerates the sites.
  **This is the cheapest thing to try first and this lane did not try it.**
- The declines are free: median 23.9 s of the 24 s budget is unspent, so
  whatever runs after them has the whole clock.

## 6. The A/B

See `AB.md` in this directory.

## Artifacts

| path | what |
|---|---|
| `census/<div>.tsv` | the full pinned 200, one row per file, board + census columns |
| `census/<div>.winnable.tsv` | the census denominator, projected from the above |
| `winnable/<div>.txt` | the winnable set, re-derivable by `summarize.py` |
| `build.sh` | fresh build in an EMPTY target dir + a stale-binary refusal |
| `census-run.sh` / `launch.sh` / `merge-division.py` | the run and its coverage guard |
| `summarize.py` | board row + soundness, **exits non-zero on a disagreement** |
| `cut-to-winnable.py` / `census-summarize.py` | the census, under ADR-1936/1941/1950/1956 |
| `ab-run.sh` / `launch-ab.sh` / `ab-summarize.py` | the interleaved per-file A/B |

The `qtrace` column of the committed census files is projected down to the
`egraph` stage only (`compact-qtrace.py`); the full trails are 5.8 MB and the
published numbers come from the `decided_by` / `bound_by` / `bound_ms` /
`total_ms` columns, which are untouched.
