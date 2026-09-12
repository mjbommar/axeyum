# QF_NIA — re-census of all 110 winnable files, after the ADR-1925 relabel fix

Lane `qf-nia-dispatch`, 2026-09-12, measured at `611b72958`.

This directory holds the **population**, the **method**, and the **raw per-file
attribution** for the QF_NIA row of the 2026-09-11/12 head-to-head board
(`bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv`: axeyum 41 of
200, z3 144, cvc5 87, best-of 144, gap **+103**).

It exists because the previous census
([`qf-nia-is-not-a-width-problem-2026-09-12.md`](../../docs/research/03-measurements/qf-nia-is-not-a-width-problem-2026-09-12.md))
put `preprocessed dispatch timeout after reduced solve` at the top with **41 of
110**, and lane `qf-nra-route` then proved that sentence is a **relabel**
([ADR-1925](../../docs/research/09-decisions/adr-1925-an-engine-internal-unsupported-is-a-decline-and-a-relabel-must-carry-what-it-replaces.md)):
`dispatch_reduced` REPLACED the reduced solve's own reason instead of carrying
it. In QF_NRA 13 of 18 files behind that sentence turned out to be the CAD wall.
So the QF_NIA 41 had to be re-run on a tree that carries the inner reason.

## Population — all 110, not a sample

**Winnable** = axeyum's board verdict is not in `{sat, unsat}` **and** at least
one reference verdict is. That is 110 of 200 (we decide 41; nobody decides 49),
listed in `winnable-110.txt` (absolute corpus paths, sha256
`516a6bb1a3a46db7f12ed3a922b2d40ad193760d250b5bb7ee94c365de4f6d7f`). Derived by
`scripts/qf-nia-dispatch-population.py`; all 110 board basenames resolve to
**exactly one** file in the 25,443-file corpus subtree — 0 missing, 0 ambiguous.
The set is byte-identical to the previous lane's 110.

**This division IS one family**, and that is stated rather than left for a
reader to assume: 101 of 110 are `20170427-VeryMax`, then `AProVE` 4,
`20210219-Dartagnan` 3, `20230328-sqrtmodinv-hoenicke` 1,
`UltimateLassoRanker` 1. A finding here is a finding about VeryMax
termination-analysis queries first and about QF_NIA second.

### Ground truth is not in dispute on these 110

Declared `(set-info :status …)` against the board's two references: **0 rows
where any authority contradicts another**.

| declared | z3 | cvc5 | files |
|---|---|---|---:|
| sat | sat | sat | 38 |
| sat | sat | unknown | 34 |
| unsat | unsat | unsat | 17 |
| unknown | unsat | unknown | 8 |
| unsat | unsat | unknown | 8 |
| unknown | unsat | unsat | 5 |

72 declare `sat`, 25 `unsat`, 13 declare `unknown` and are refuted `unsat` by
z3. Any verdict we newly produce has an uncontested expected answer.

## Method

`smtcomp_cli <file> --timeout-ms 24000 --trace`, one file per process, release
build of this lane's tree, pinned to a scratchpad copy so a concurrent lane's
rebuild could not swap the binary mid-sweep
(sha256 `73d8de29abaafd1bc9e2468e58ef6afd20593dd8f4f113af21d8b438bcaffd29`).
Three workers on s4 under concurrent lane load (load average 7–19).

**Timeout wall: `timeout -k 5 180`** — 7.5x the budget. A previous census in
this repository wrapped a 24 s budget in `timeout 32` and killed 17 processes
under load, manufacturing false "no reason" rows. **0 of 110 hit the wall here
(`rc=0` on all 110) and 0 rows are reasonless.**

**The dispatch is confirmed to have run to the END**, not stopped at an early
rung: `attempts=` against the ladder length. A pure-integer query's full trail
is 19 rungs (`fd:parse`, `probe`, `dl-online`, `lia-simplex`, `lia-dpll`,
`nia-square`, `int-real-relax`, `nia-linearize`, `nia-bounded-blast`,
`int-blast-ladder`, then 9 string front-door wrappers that decline on budget).
Measured: **103 of 110 ran 19–22 attempts**, one ran 44. The two exceptions are
themselves the finding, not a gap — 6 watchdog kills have no route line at all
(`attempts` unrecorded) and 1 file is refused at ingest (`attempts=1`,
`bound_by=fd:parse`).

Three fields are recorded per file and deliberately **not** collapsed: the
`give-up kind=… detail=…`, the `route decided_by=/bound_by=/last=` trail, and
the watchdog phase breadcrumb. Raw rows: `census-110.tsv`.

## Result 1 — the relabel was real here too, and it decomposes cleanly

All 110 returned `unknown`. Classified by the outer `give-up detail` (the
previous census's classes) and again with the ADR-1925 carrier decomposed:

| the census as the OLD code reported it | files | | the HONEST cause | files |
|---|---:|---|---|---:|
| `preprocessed dispatch timeout after reduced solve` | **44** | → | `integer bit-blast width ladder: wall-clock timeout reached` | **41** |
| | | → | `combined-theory timeout after scalar backend` | 3 |
| `estimated N CNF clauses … exceeds budget` | 31 | | (unchanged) | 31 |
| `bounded integer model overflowed at width 32` | 25 | | (unchanged) | 25 |
| watchdog fired before the worker thread returned | 6 | | (unchanged) | 6 |
| `integer constant does not fit the bounded width 32` | 2 | | (unchanged) | 2 |
| `distinct` pairwise-expansion ingest limit | 1 | | (unchanged) | 1 |
| `no model within the bounded integer width 32` | 1 | | (unchanged) | 1 |

**Unlike QF_NRA, nothing was hiding behind the sentence.** In QF_NRA the
carrier concealed a capability wall (13 of 18 were the CAD boundary, a
different class entirely). Here all 44 carrier rows decompose into the **same
bit-blast route the census already knew about** — 41 say the width ladder ran
out of wall clock and 3 say the scalar backend did. The relabel cost
QF_NIA its precision, not its diagnosis.

The honest table, all 110:

| honest cause | files | share |
|---|---:|---:|
| `integer bit-blast width ladder: wall-clock timeout reached` | **41** | 37% |
| `estimated N CNF clauses before lowering exceeds budget N` | 31 | 28% |
| `bounded integer model overflowed at width 32 … widen the bound` | 25 | 23% |
| watchdog fired before the worker thread returned | 6 | 5% |
| `combined-theory timeout after scalar backend` | 3 | 3% |
| `integer constant does not fit the bounded width 32` | 2 | 2% |
| `distinct` pairwise-expansion ingest limit | 1 | 1% |
| `no model within the bounded integer width 32` (in-range `unsat`) | 1 | 1% |

By kind: `ResourceLimit` 42, `EncodingBudget` 31, `Incomplete` 28,
`Watchdog` 6, `Timeout` 3.

**103 of 110 are the bit-blast route in one form or another** — it timed out,
it refused the encoding as oversized, or its model failed exact-integer replay.
The remaining 7 are 6 watchdog kills and 1 ingest refusal.

## Result 2 — what refused and what spent the clock are different routes

`bound_by` is the route that consumed the most budget; `detail` is what finally
refused. They disagree on 49 of 110, and the disagreement is the finding:

| honest cause | `bound_by` | files |
|---|---|---:|
| ladder-clock | `int-blast-ladder` | 41 |
| cnf-budget | **`nia-linearize`** | **30** |
| replay-overflow | **`nia-linearize`** | **18** |
| replay-overflow | `int-blast-ladder` | 7 |
| watchdog | (none — killed) | 6 |
| scalar-clock | `int-blast-ladder` | 3 |
| cnf-budget | `int-blast-ladder` | 1 |
| `distinct` ingest limit | `fd:parse` | 1 |
| const-width | `int-real-relax` | 1 |
| const-width | `nia-linearize` | 1 |
| in-range-unsat | `int-real-relax` | 1 |

**On 49 of 110 files the budget is spent by `nia-linearize` and the verdict is
then decided by a route that had whatever was left.** On the 30 `cnf-budget`
rows that is starkest: the linearizer burns the largest share of a 24 s budget,
and the refusal that ends the file is an *instantaneous pre-lowering estimate*
that could have been produced in the first second.

Every `last=` is `fd:bounded-completeness-unsat` on 103 of 110 — a **string**
front-door wrapper with nothing to do with QF_NIA, re-reporting the integer
decline it was handed. Classifying this division by `last` would have named a
string route as the cause of 103 of 110 losses. That is the fourth recorded
instance of that failure mode in this repository, and it is why `bound_by` and
`last` are both printed.

## Result 3 — the largest honest class is not a clock problem

The 41 `ladder-clock` files re-run at **150 s** (6.25x the competition budget,
`timeout -k 5 260`, three workers): **1 of 41 decided** (`sat`, 58.5 s, on
`From_AProVE_2014__juLinkedListCreateAddAllAt.jar-obl-17__p8434_safety_0.smt2`).
Raw rows: `deep-ladder-clock-150s.tsv`.

At six times the budget the class also decomposes further, which is itself the
answer to "was 24 s simply too short":

| at 150 s, the 41 ladder-clock files become | files |
|---|---:|
| `estimated N CNF clauses … exceeds budget` | 13 |
| watchdog fired before the worker thread returned | 10 |
| `integer bit-blast width ladder: wall-clock timeout reached` (still) | 10 |
| `bounded integer model overflowed at width 32` | 4 |
| `combined-theory timeout after scalar backend` | 3 |
| no reason (killed) | 1 |

So "give the ladder more of the budget" is a measured negative. The watchdog row
grew from 6 to 10 because this probe ran concurrently with the A/B below; that
inflation can only move files out of the structural classes, never into them.

## Result 4 — the wraparound is ADDITIVE, and one side-constraint decides 40 files

[ADR-1921](../../docs/research/09-decisions/adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md)
closed the width lead and left one hypothesis standing, marked unmeasured:
`blast_integers` emits a no-overflow constraint for `int_mul` and for **nothing
else**, so the replay failures that survive must be **additive** wraparound.

Measured, it is right.
[ADR-1937](../../docs/research/09-decisions/adr-1937-the-blaster-pins-products-and-nothing-else-and-the-wraparound-is-additive.md)
adds the analogous constraint on `int_add`/`int_sub`/`int_neg`.

### The A/B

One release binary (sha256 `c4ee2cf01be611ff6fcbb0a2a11fede1702c794988e637b1497f864533d75880`),
two environments, arms alternating per file, both arms of a file run back to back
inside one worker so the pair shares ambient load. Three workers on s4 pinned to
cores 8–15, `--timeout-ms 24000`, wall `timeout -k 5 180`.

**The whole division** (200 board rows, 201 paths — `106.smt2` is an ambiguous
basename and BOTH candidate copies are included rather than guessed; its board
row is `unknown` for all three solvers so neither copy can produce a gain or a
loss). Rows: `ab-division-200.tsv`.

| | baseline | armed |
|---|---:|---:|
| decided | **39** | **78** |
| gains | — | **40** |
| losses | — | 1 raw, **0 after re-check** |
| verdict flips between arms | — | **0** |
| wall total | 3,607 s | 3,239 s (**−10.2 %**) |
| both-decided wall ratio | — | 0.995 |

It is **faster**, which is the shape the mechanism predicts: the constraint
removes the wrapping models the exact-integer replay was going to reject anyway.

**Cost on what already works** (`ab-crossdiv-cost-298.tsv`): 298 already-decided
files, every fourth, from QF_LIA, QF_UFLIA, QF_IDL, QF_RDL, QF_NRA, QF_ABV,
QF_SLIA, QF_DT and UF — `crossdiv-cost-298.txt`. Baseline 290 decided, armed
289; **0 real losses, 0 flips, +1.9 % wall** (both-decided ratio 1.027).

That sample **resolves before it samples**. Sampling first and dropping what
would not resolve gave QF_LIA 7 files instead of 27, because 92 of its 119
decided rows share a basename with another corpus directory and the board cannot
say which one it ran. QF_LIA is the division this constraint taxes most, so a
sample size decided by basename collisions would have measured the wrong thing.

### Every single-pairing surprise was re-run serially, and every one was a flake

Pinned to cores 0–7, arms back to back, nothing else of this lane's running:

| file | parallel A/B | serial re-check, both arms |
|---|---|---|
| `From_T2__n-7.t2_fixed__p4922…` (QF_NIA) | A `unsat` 6.7 s / B `unknown` 24.3 s | `unsat` 6.3 s / `unsat` 6.3 s, 4 of 4 |
| `xy.12.x.12.r.3…gph` (QF_IDL) | A `sat` 19.2 s / B `unknown` | `sat` ≈9.8 s both, 3 of 3 |
| `ex8280_2400_100` (QF_LIA) | A `sat` 18.8 s / B `unknown` | `sat` 16.9 s both, 3 of 3 |
| `hash_uns_04_20` (QF_UFLIA) | A `unsat` 15.8 s / B `unknown` | `unsat` 8.6 s both, 3 of 3 |

Three gains re-checked the same way all reproduce: `LessLeaves…p10018`
(`unknown` 24.1 s vs `sat` 15.1 s, 3 of 3), `fun1.t2_fixed…p697` (`unknown`
24.6 s vs `sat` 15.4 s, 2 of 2), `SAT14/571` (`unknown` 24.9 s vs `sat` 7.6 s,
2 of 2).

Both the raw and the re-checked numbers are given, because a 16 s baseline
against a 24 s budget flips under ambient load and this repository has already
published one false convert from exactly that.

### Against the board, not only against the arm

The board's baseline for this division is 41; this host's baseline arm
reproduced **39** under three-way load. The two it missed are host effects, not
treatment effects — `From_T2__n-21.t2__p3959…` was missed by **both** arms and
decides `unsat` in 8.3 s in both arms serially. On equal footing:

> **41 → 80 of 200** (78 measured armed, plus `n-21` and `n-7`, each verified
> serially in both arms), closing **39 of the 103-file gap** to z3's 144.

### Soundness

All **78** verdicts the armed arm produced — not only the 40 gains — checked
against three authorities keyed by full path: the benchmark's own
`(set-info :status …)`, `z3 -T:60`, and `cvc5 --tlimit 60000`. Rows:
`refcheck-78.tsv`.

> **78 verdicts, 0 disagreements, 0 verdicts with no authority.**

The checker was verified able to fail: inverting every verdict yields **78**
disagreements. A checker that cannot fail is worse than no checker, so the zero
is only worth reading next to that 78.

## Files

| file | what it is |
|---|---|
| `winnable-110.txt` | the pinned winnable population (absolute paths) |
| `census-110.tsv` | per-file census rows: verdict, rc, wall, kind, detail, decided_by, bound_by, last, bound_ms, total_ms, attempts, phase |
| `classes/class-*.txt` | the census population split by honest cause |
| `deep-ladder-clock-150s.tsv` | the 41 ladder-clock files at 150 s |
| `division-201-paths.txt` | the whole division, resolved (201 paths for 200 board rows) |
| `ab-division-200.tsv` | the interleaved A/B over the whole division |
| `crossdiv-cost-298.txt` | the cross-division cost population |
| `ab-crossdiv-cost-298.tsv` | the interleaved A/B over already-decided files in nine divisions |
| `refcheck-78.tsv` | every armed verdict against `:status`, z3 and cvc5 |

Scripts: `scripts/qf-nia-dispatch-{population,census,classify,crosstab,ab,refcheck,deeptrace,groundtruth}.py`.

## Caveats, stated so nobody quotes them as load-independent

`ladder-clock` (41), `scalar-clock` (3) and `watchdog` (6) are load-sensitive
rows and this sweep ran at three-way parallelism on a shared box. Each
inflation can only move files **out of** the structural classes, never into
them, so 31 and 25 are floors for the CNF-budget and width classes and 41 is a
ceiling for the ladder-clock class. No timing claim is made from this census.
