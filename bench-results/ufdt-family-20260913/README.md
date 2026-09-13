# The three UFDT siblings, censused whole — and the target had already moved

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
| AUFDTLIRA *(sibling)* | 0 / 200 | **96 / 200** | 176 | 176 | 176 | **80** (176) |

`AUFDTLIRA` is measured here as the sibling the brief's five ADRs were aimed at,
on the same envelope as the other three, so "how much transferred" is a
comparison and not an inheritance. It reads **96 / 200 at 24 s** on this lane's
run; the brief's `110` comes from ADR-1966's 10 s per-file A/B on the same
pinned list, which is a different measurement and not averageable with this one.

`UFDTNIRA` is **5 → 74**, not 5. The brief sized it at "5 of 200, 178 winnable,
the biggest refutation-bound population on any board"; on the tree as it stands
that population is **109**, and the 69 files that closed were closed by other
lanes' datatype and dispatch work landing on `main` between the board being
taken and this census. **Verify a blocker still exists before treating it as
one** is this repository's own rule, and the brief that sent this lane did not.

**Soundness, with the comparable denominator on the same line (ADR-1957):**

    UFDTNIRA   74 verdicts  vs :status 67/67   vs z3 74/74   vs cvc5 74/74   DISAGREEMENTS: 0
    UFDTLIRA  105 verdicts  vs :status 105/105 vs z3 105/105 vs cvc5 105/105 DISAGREEMENTS: 0
    UFDT       31 verdicts  vs :status 27/27   vs z3 27/27   vs cvc5 29/29   DISAGREEMENTS: 0
    AUFDTLIRA  96 verdicts  vs :status 96/96   vs z3 96/96   vs cvc5 96/96   DISAGREEMENTS: 0

No zero here is vacuous: **215 + 315 + 83 + 288 = 901 independent comparisons**
stand behind them. `summarize.py` exits non-zero on any disagreement, so the
exit status depends on the finding.

**Polarity of the remaining winnable set** (re-derived on the NEW winnable
sets, not inherited from the stale `winnable-polarity-20260913` table):
`UFDTNIRA` 109 unsat / **0 sat**, `UFDT` 50 unsat / 1 sat, `UFDTLIRA` 53 unsat
/ 23 sat. The bimodal shape the polarity table describes survives the
correction; the absolute sizes do not.

## 2. The census — all 316 winnable rows, not a sample

One pass over each pinned 200 yields BOTH the board row and the census row, so
this is a projection of one measurement rather than two
(`census-run.sh` → `merge-division.py` → `cut-to-winnable.py` →
`census-summarize.py`). ADR-1936 / ADR-1941 / ADR-1950 / ADR-1956 all apply and
all are enforced by the summarizer, not by prose.

    by kind:  SHAPE 170   CLOCK 125   OTHER 2
              UNCLASSIFIED (ADR-1941) 19       no route trail at all 0
              rc=124 wrapper-killed 0          rc=134 (8 GiB cap) 0

| family | kind | UFDTNIRA | UFDTLIRA | UFDT | AUFDTLIRA | tot |
|---|---|---:|---:|---:|---:|---:|
| **mbqi: datatype ARGUMENT congruence not exact** (ADR-1935) | SHAPE | 0 | **29** | **20** | **23** | **72** |
| **valid-universal elimination CLOCK** | CLOCK | **56** | 0 | 0 | 0 | **56** |
| ladder CLOCK exhausted after e-matching | CLOCK | 25 | 2 | 3 | 19 | 49 |
| **mbqi: datatype RESULT expansion not exact** (ADR-1946) | SHAPE | 0 | 9 | 16 | 14 | **39** |
| e-matching FIXPOINT (no instance left to admit) | SHAPE | 2 | 7 | 6 | 2 | 17 |
| e-matching instantiation CLOCK | CLOCK | 12 | 0 | 0 | 5 | 17 |
| instantiation sat, universal unrefuted | SHAPE | 0 | 13 | 0 | 0 | 13 |
| **mbqi: UF on a non-atomic datatype term** (ADR-1920/1942) | SHAPE | 0 | 11 | 0 | 2 | **13** |
| mbqi: uninterpreted sort the BV backend cannot blast | SHAPE | 3 | 3 | 0 | 1 | 7 |
| mbqi declined, other cause | SHAPE | 0 | 0 | 1 | 5 | 6 |
| bounded integer width | SHAPE | 2 | 1 | 0 | 0 | 3 |
| e-matching GROWTH-HEADROOM (a clock exit) | CLOCK | 2 | 0 | 1 | 0 | 3 |
| *(OTHER, printed in full by `census-summarize.py`)* | OTHER | 1 | 1 | 0 | 0 | 2 |

**The three bolded rows are ONE predicate.** 72 + 39 + 13 = **124 of 316
winnable rows across all four datatype divisions** — the largest single blocker
family anywhere on this board, and larger than every CLOCK family put together
on three of the four divisions. Section 5 sizes it.

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
ADR-1946 are **124 of 316 winnable rows**, and the largest of them is a single
named precondition on **72 files across three divisions**.

### ADR-1950: which budget, and the labels' own test

| family | kind | n | ms_left min | **median** | max | reading |
|---|---|---:|---:|---:|---:|---|
| mbqi: ARGUMENT congruence (1935) | SHAPE | 72 | 19,049 | **23,951** | 23,998 | clock never involved |
| valid-universal elimination | CLOCK | 56 | −77 | **−46** | −30 | genuinely clock-bound |
| ladder CLOCK after e-matching | CLOCK | 49 | −982 | **−45** | −3 | genuinely clock-bound |
| mbqi: RESULT expansion (1946) | SHAPE | 39 | 12,709 | **23,924** | 23,999 | clock never involved |
| e-matching FIXPOINT | SHAPE | 17 | −279 | **18,484** | 23,999 | clock never involved |
| e-matching instantiation | CLOCK | 17 | 158 | **5,123** | 10,005 | MIXED — two populations |
| instantiation sat, unrefuted | SHAPE | 13 | 23,408 | **23,997** | 23,999 | clock never involved |
| mbqi: UF on datatype term (1920/1942) | SHAPE | 13 | 23,864 | **23,964** | 23,997 | clock never involved |

Counting rows that gave up **past** the 24,000 ms deadline, per kind, is the
direct test of the labels:

    CLOCK   106 of 125     SHAPE   1 of 170     OTHER   1 of 2

**ADR-1956 holds on four more divisions.** `e-matching ... did not refute
within the round budget` — the string that was 45 % of the six-division board —
appears **0 times** in 316 winnable rows here. The loop's exits that do appear
are FIXPOINT (17) and GROWTH-HEADROOM (3), both of which ADR-1956 established
are not round budgets. No row in any of the four divisions reaches the
instantiation round ceiling.

**No nested-array refusal appears anywhere** — 0 of 316 — so ADR-1965's array-IR
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

### What the rung buys, on the same run

ADR-1970's decisive column was "how often is the rung entered, and how often
does it decide?" The census's own `decided_by` / `bound_by` columns answer it
here without a second sweep:

| division | files where `bound_by` = `q:valid-universal-qf` | files where `decided_by` = it |
|---|---:|---:|
| UFDTNIRA | 50 | **0** |
| UFDTLIRA | 50 | **0** |
| AUFDTLIRA | 59 | **0** |
| UFDT | 8 | **0** |
| **total** | **167 of 800** | **0 of 800** |

It is the bounding route on **167 of 800 files and produces a verdict on none of
them.** `q:egraph`, the rung ADR-1970 declined to reserve against, at least
decided 1 of 200 and 8 of 200. This one decides zero.

That is a statement about these four divisions and not about the rung in
general — it exists because some other fragment needs it, and nothing here
measures that. It is the reason the lever is a RESERVE rather than a removal.

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

## 5. Target B — one predicate holds 124 of 316 rows, and it is a nested field

Not built here. It is nearly **three times** Target A and it is the one that is
actually a datatype capability, so it is written down with what the census and
one static instrument can establish, rather than guessed at.

| precondition | ADR | UFDTLIRA | UFDT | AUFDTLIRA | UFDTNIRA | tot | median ms_left |
|---|---|---:|---:|---:|---:|---:|---:|
| congruence over a datatype ARGUMENT whose expansion is not exact | 1935 | 29 | 20 | 23 | 0 | **72** | 23,951 |
| a UF whose RESULT datatype's expansion is not exact | 1946 | 9 | 16 | 14 | 0 | **39** | 23,924 |
| a UF applied to a datatype term that is neither a free variable, a constructor application, nor another UF | 1920/1942 | 11 | 0 | 2 | 0 | **13** | 23,964 |

### All three rest on one function, and it is false for exactly one reason

`datatype_expansion_is_exact` (`crates/axeyum-solver/src/datatype_native.rs`)
is `field_sort_expands` over every field of every constructor, and
`field_sort_expands` admits `Bool` / `BitVec` / `Int` / `Real` /
`Uninterpreted` and datatype-free arrays — and **nothing else**. So exactness
fails precisely when some constructor field has sort `Datatype(_)`: a
**nested or recursive datatype**. `build_sym_vars` declares no expansion
variable for such a field, so the encoded equality is a relaxation, a weaker
congruence antecedent is a stronger axiom, and the failure mode is a wrong
`unsat`. That is why the guard is there and it must not be relaxed into a
comment.

### Which shape, measured

`scripts/dt-exactness-field-shape.py` parses the `declare-datatypes` blocks out
of the benchmark TEXT — not through the solver, so a refusal cannot hide the
answer, and because the shape is a property of the benchmark rather than of our
encoding. It reads both the SMT-LIB 2.6 and the 2.0 legacy spellings; reading
only 2.6 reports every SPARK file as `no-datatype`, which is how the first run
of it was wrong. Its exit status is non-zero if any file fails to parse,
because an unparsed file reads as "no datatype" and would shrink the
denominator silently.

| population | n | nested (terminating) | recursive | flat | no datatype |
|---|---:|---:|---:|---:|---:|
| **the 124 exactness-refused rows** | 124 | **97** | 27 | **0** | 0 |
| the other 192 winnable rows *(control)* | 192 | 101 | 2 | 86 | 3 |

Two things follow, and the control is what makes them sayable:

1. **Not one refused file is flat**, and 86 of the control's 192 are — so the
   refusal population is exactly where the predicate says it should be, and the
   instrument is measuring the right thing.
2. **78 % of the refused population (97 of 124) is NESTED but not recursive**,
   with a bounded field-chain depth: 8 at depth 1, 51 at depth 2, 28 at depth 3,
   and 10 at depth 4–6. **A recursive tag/field expansion terminates on those
   97 with no depth bound and therefore no new soundness story** — it is the
   same move ADR-1965 made one level out, for the nested ARRAY sort. Only the
   27 recursive files need a bounded unfolding and its own argument.

The control also shows what the instrument cannot say: **101 control files are
nested too and are not refused**, so nesting is necessary but not sufficient
for the refusal, and no lane should quote "nested ⇒ reachable". The 124 is the
blocker count; the reachable count is unmeasured and this project's own tally
(143→6, 173→10, 934→0, 27,150→1,135) says it is usually much smaller.

### What a lane taking this must establish before building

- **Run ADR-1966's check on these three refusal sites first.** A rung BELOW may
  own the construct, in which case the refusal should be a DECLINE and the fix
  is far smaller than a capability.
  `scripts/enumerate-dispatch-refusal-propagation.py` enumerates the sites.
  **This is the cheapest thing to try and this lane did not try it.**
- **Polarity differs sharply by division.** `UFDT` 50 unsat / 1 sat,
  `AUFDTLIRA` 80 unsat / 0 sat, `UFDTLIRA` 53 unsat / **23 sat**. MBQI is a
  MODEL builder, so on `UFDTLIRA` it can produce both halves — unusual for this
  project's targets. A refutation-only fix ceilings at 53 there, not 76.
- **The standard is ADR-1965's**: delete one guard, require that **exactly one**
  test dies, over SATISFIABLE fixtures whose plausible wrong answer is `unsat`.
  `dt_capability_1935` (20 tests), `dt_constructor_arg_1942` (11) and
  `dt_valued_result_1946` (12) are the suites that must move.
- The declines are free: a median 23.9 s of the 24 s budget is unspent, so
  whatever runs after them already has the whole clock. Nothing here is a
  budget problem.

## 6. The A/B, and what shipped

Full protocol, every arm and the noise floor: [`AB.md`](AB.md). The result:

| arm | UFDTNIRA | UFDTLIRA | UFDT | AUFDTLIRA | UF (control) |
|---|---:|---:|---:|---:|---:|
| ceiling `=1` | **74 → 93 (+19 / −0)** | 105 → 105 | 31 → 31 | 96 → 96 | 90 → 88 (**−2**) |
| **shipped `=4`** | **73 → 92 (+19 / −0)** | 105 → 105 | 31 → 31 | 96 → 96 | 90 → **90 (0 / 0)** |

**0 sat↔unsat flips in 4,000 solves.** The two arms gain the **identical set**
of 19 files — checked as a set, not a count — so the gain is not an artefact of
an extreme setting; and the `UF` control separates them, which is what decided
the shipped constant. All 19 re-run three times per arm: **19 of 19 stable
GAIN, 0 unstable**, and 55 independent comparisons against `:status`, z3 and
cvc5 with **0 disagreements and 0 rows nothing could check**. The two `UF`
losses under the ceiling arm are equally stable and are reported as a real cost,
which is why `share = 1` does not ship.

Noise floor, measured on this lane's own arms: three independent base-arm runs
over 800 files disagree on **one** file, and that file is named in `AB.md`. A
band of 0–1 against a +19 effect.

**`AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE` ships ON at `share = 4`**, and `off`
selects the historical whole-budget arm so the A/B stays runnable.

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
| `ab-run.sh` / `launch-ab.sh` / `ab-summarize.py` | the interleaved per-file A/B, **exits non-zero on a flip** |
| `ab/ceiling/<div>.tsv` / `ab/reserve4/<div>.tsv` | both arms, full pinned 200, five divisions |
| `confirm-moved.sh` / `confirm-launch.sh` / `confirm-summarize.py` | the 3x-per-arm re-check and the reference comparison |
| `confirm/<div>.tsv` | every row either arm moved, re-checked |
| `AB.md` | the A/B protocol, the noise floor, and both arms |
| `scripts/dt-exactness-field-shape.py` *(in `scripts/`)* | why the exactness predicate fails, with a control |

The `qtrace` column of the committed census files is projected down to the
`egraph` stage only (`compact-qtrace.py`); the full trails are 5.8 MB and the
published numbers come from the `decided_by` / `bound_by` / `bound_ms` /
`total_ms` columns, which are untouched.
