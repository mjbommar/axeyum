# What our work since the 2026-09-09 board is worth, and where the gap actually is

**Date:** 2026-09-11
**Method:** interleaved per-file A/B. For every file both arms run back to back
on the same core, so ambient load is shared and cancels in the comparison.
24 s wall / 8 GiB, the parity protocol. Absolute-budget probes are marked as
such, because only those are load-sensitive.

## Why this note exists: a board row is not evidence of a code change

`bench-results/PARITY.md` ran three divisions repeatedly on 2026-09-09 at one
commit (`e99d08848f`):

| division | same-commit runs | spread |
|---|---|---|
| QF_UFLIA | 127, 113, 121, 136, 128 | **23** |
| QF_LIA | 119, 110, 115, 121, 119 | 11 |
| QF_LRA | 97, 96, 97, 99, 97 | 3 |

The spread tracks host load (QF_UFLIA: 136 at load 2.64, 121 at load 9.00).
Most deltas quoted in this repository are smaller than the QF_UFLIA spread.
Everything below is measured against a **built binary of the 09-09 commit**.

## 1. QF_UFLIA gained 36 files, and the gain is sound

| arm | decided | sat | unsat |
|---|---|---|---|
| `e99d08848f` (09-09 board) | 122 | 84 | 38 |
| `5e84b3073` (HEAD) | **158** | 114 | 44 |

**+36 | 36 gains | 0 losses | 0 sat↔unsat flips**, 200 files.

Two independent cross-checks: the 09-09 arm's 122 falls inside that commit's own
board spread (113–136), and the HEAD arm's 158 brackets today's board row of 161
measured on a different host under a different harness.

Gains are two families: `hash_sat_05..09` (22) and
`mathsat/EufLaArithmetic/medium` (6). The `hash_sat` ladder is gained whole from
05 through 09, so this scales with instance size rather than fixing a corner.

## 2. The +36 is NOT this session's three fixes

`e4e6378b8` (EUF disequality propagation), `318930806` (e-matching routing) and
`c35941f9b` (deferred-pool release) all land after `f09652489`. Running
`f09652489` vs HEAD:

| division | files | delta |
|---|---|---|
| QF_LRA | 200 | **0** — zero differing rows, wall ratio 0.9962 |
| QF_UFLIA gains, sampled | 12 | **0** — all already decided at `f09652489` |

The +36 belongs to the 320-commit window BELOW the three fixes.

**But two of the three cannot act on those divisions at all.** `auto.rs`'s fix is
the e-matching loop and `qinst_egraph.rs` is quantifier instantiation; QF_LRA and
QF_UFLIA are quantifier-free. Measuring them there is close to tautological. On
**UF**, the division they target, `f09652489` vs HEAD is **+4 at 166 files, 0
losses** -- consistent with `c35941f9b`'s own claim of +6 on 358 UF files. And
the QF_UFLIA null above was ALSO a sampling artifact: the complete 200-file run
gives **+5, 0 losses** (`hash_sat_09_17` through `hash_sat_10_20` -- the TOP
rungs of the ladder the 320-commit window had taken to 09_14, each landing at
18.6-19.1 s against a 24 s budget, which is what cutting conflicts 94,100 -> 623
buys on the largest instances). Both nulls came from reading a PREFIX of a run
whose list is path-sorted, so the hard families cluster at the head.

## 3. The QF_UFLIA gap decomposes, and half of it is already closed

200 files against cvc5 1.3.4 (plain invocation):

| class | files |
|---|---|
| both decide | 161 |
| neither decides — wide integer literal | 20 |
| cvc5 only — wide integer literal | 6 |
| **cvc5 only, no wide literal — addressable** | **13** |

The wide-literal population is **exactly 26 files, every one an 78-digit 2^256
EVM word**, verified by scanning the corpus independently of ADR-1702, which
states the same 26. ADR-0376's ablation closed them: strip every wide literal and
6 of 6 are still `unknown`. So the honest denominator for this division is
**174, not 200**, and we decide 161 of it.

## 4. "Too slow" is the SMALLER class

All addressable-gap files re-run at a **120 s** budget (their 24 s verdict is
already known from the board). 151 of 177 complete at time of writing:

| outcome at 5x budget | files | share |
|---|---|---|
| decided | 19 | 13% |
| **gave up early, budget unused** | **41** | **27%** |
| burned the full budget | 91 | 60% |

Twice as many files ABANDON the budget as are rescued by extending it. This
probe is absolute-budget, so load can only make a file LESS likely to decide:
13% is a floor.

Per division the two biggest gaps need OPPOSITE work:

| division | gap | decided at 5x | early give-up |
|---|---|---|---|
| QF_LRA | 40 | **0** | 9 |
| QF_NIA | 37 | 4 | **14** |
| UF | 28 | **0** | **23 (82%)** |
| QF_LIA | 18 | 2 | 3 |
| QF_IDL | 14 | 4 | 0 |
| QF_UFLIA | 13 | **8 (62%)** | 0 |
| QF_ABV | 12 | 0 | 3 |
| QF_BV | 8 | 3 | 0 |
| QF_SLIA | 7 | 0 | 5 |

QF_LRA is the largest gap on the board and 5x the clock decides **none** of it.

## 5. Half the early give-ups are not give-ups — the process DIED

7 of 14 traced non-verdicts emitted no `; give-up` line at all. The cause is not
missing instrumentation: **the process aborts**. `QF_ABV/wchains140se.smt2` dies
with `memory allocation of 127632960 bytes failed`, rc=134 (SIGABRT), under the
8 GiB `ulimit -v`. It never reaches its own reporting path, so nothing
solver-side can describe it.

The defect was in the RUNNER, and is fixed (`1d391d900`): `parity-run.sh` piped
the solver into `grep`, sent stderr to `/dev/null`, and never read the exit
status, so a reasoned `unknown`, a harness `timeout` kill, an OOM abort and a
crash all printed `unsolved`. Non-verdicts now record solver, file, reason and
stderr to `bench-results/parity-nonverdicts.tsv`. Scored strings are unchanged,
so every existing baseline stays comparable. Control:
`scripts/tests/test-parity-nonverdict-classifier.sh`, mutation-tested.

Named reasons in the other half: `EncodingBudget`; `int↔real coercion
relaxation: candidate fails the original coupling`; `lazy linear arithmetic
pre-SAT skeleton exceeds the joint resource bound`; array equality over a 32-bit
index.

## 6. THREE caps investigated, and all three are currently CORRECT

Each looked like an unexploited win and each was measured to not be one.

**`ABSOLUTE_CLAUSE_CEILING = 64_000_000`** — refuses QF_NIA files on estimates of
109.8M / 150.7M / 286.8M clauses *before lowering*. Its registry entry concedes
the estimator "over-estimates pre-lowering" and that "no measurement or ADR is
cited at the definition site", and roadmap 3.9 item 3 measured it **2.83x
pessimistic** elsewhere. Rebuilt with the ceiling at 2e9 (**31x**) and re-ran the
four refused files: **4 of 4 still `unknown`**, now burning 89–122 s each instead
of being refused at 30 s. The cap is SAVING ~90 s apiece and costing nothing
here. (3.9 item 3's original finding was on QF_BV's generated width family, where
admitting *did* decide the file in 41 s — same cap, opposite verdict on two
populations. Quote the population with the claim.)

**`MAX_ARRAY_EQ_INDEX_BITS = 8`** — roadmap 4.2 proposes removing this refusal.
It cannot be removed: bounded extensionality **enumerates 2^iw indices**, and
**10 of the 12 QF_ABV addressable files carry 32-bit indices**. 4.2's row already
records that its motivation is wrong; the widths confirm why.

**`UF_ARITH_LADDER_RESERVE_SHARE = 4`** — `hash_uns_05_20` decides in ~22.8 s but
the CEGAR receives only 3/4 of a 24 s budget (18 s), times out, and declines:

| policy | 24 s | 32 s | 48 s |
|---|---|---|---|
| `probe` (shipped) | unknown | unsat 22.6 s | unsat 27.3 s |
| `terminal` | **unsat 22.8 s** | unsat 22.6 s | unsat 22.5 s |
| `skip` | unknown | unknown | unknown |

`terminal` wins this file at the real budget and **must not be adopted**: it is
the pre-2026-09-08 behaviour whose removal gained **+9** files. It trades 9 for
1. `skip` failing confirms the CEGAR is the deciding route. The registry note
predicted this case and named this file.

## 7. 387 of 481 caps have no measurement behind them

`config_registry.rs`, counted:

| | count |
|---|---|
| registered entries | 481 |
| dated (a measurement, a commit, a basis) | 94 |
| **`undated` — `measured_on: None`** | **387** |

Narrowing to caps that can turn a decidable file into `unknown` — `Protects::
Completeness` with `RefuseUnknown` or `DeclineRoute`, and undated:
**74**. Values are round numbers (8, 8, 10, 16, 128, 512) and **`env_override`
is `None` on essentially all of them**, so testing one costs a rebuild. That is
why none has been tested.

Section 6 is the caution against a crusade: three caps investigated, three
correct as shipped. "Unmeasured" does not mean "wrong" — it means unanswerable.
**The cheap, mechanical change is giving those 74 env overrides**, which converts
one unanswerable question into 74 one-command A/Bs.

## 8. Roadmap 3.8 is DO NOT BUILD — its own falsifier fired

3.8's exit criterion: *"force the lazy-ROW path on `wchains060-200`; if it is
also slow, a cost predicate does not fix it."* Forced via
`route_solo --route abv-lazy-row` against `--route array-elim`, 60 s budget,
28 files, depths 60–200:

| | value |
|---|---|
| identical verdicts | **28 / 28** |
| eager decided | 2 |
| lazy-ROW decided | **the same 2** |
| lazy-ROW-only wins | 0 |
| eager-only wins | 0 |
| total wall | eager 1404 s, lazy-ROW 1408 s (**1.003**) |

ADR-1902's cost predicate selects *between* these two routes. On the family that
motivated it they are indistinguishable, so selecting better between them buys
nothing. **3.8 flips BUILD → DO NOT BUILD, leaving Phase 3 with no BUILD items.**

Depths 110–200 give up at 24–51 s rather than using the 60 s budget: those are
the SIGABRT deaths of section 5, and both routes die the same way at the same
depth. The failure is below both of them, in bit-blasting.

## What this says about where to work

The 24 s budget is not the binding constraint — 60% of the addressable gap
survives 5x the clock and only 13% is won by it. The two largest gaps need
opposite work: QF_LRA is a capability wall (0 of 40 at 5x), QF_NIA is dominated
by early refusals (46%). And the single highest-leverage *mechanical* change
found is not an algorithm: it is that 74 completeness-guarding caps cannot be
A/B-ed without a rebuild.
## Addendum, same day: the front door was refusing a whole family

Sections 1-8 measured how much solver work moved the board. This section is a
different kind of finding, reached by the instrument section 5 installed.

### QF_UFLRA had never been benchmarked, and it hid both

Its first row, 2026-09-11: **76/200 against cvc5's 198/200** -- a 122-file gap,
the worst on the board. The family breakdown was the tell:

| family | we decided | cvc5 |
|---|---|---|
| `RandomDecoupled` | **1 of 69** | 69 |
| `RandomCoupled` | 49 of 67 | 67 |
| `cpachecker-induction` | 25 of 58 | 58 |

73% on one family from a generator and **1.4%** on its sibling is a mechanism,
not weakness.

### The failures were 35 ms, not 24 s

`--trace` on any `RandomDecoupled` file:

    ; route decided_by=none bound_by=fd:parse last=fd:parse bound_ms=24
      total_ms=24 attempts=1

`attempts=1`. An 18 KB file with one assert, refused in 24 ms, **no solver route
ever entered**. `route_solo` forced each of `auto`, `uflra-online`,
`uf-arithmetic`, `uf-arith-lazy`, `lra-online-cdclt`, `lra-dpll`: all six
returned the identical `term error: operands must share a sort: Real vs Int`.

### `distinct` never coerced numerals

Minimal case, and the controls that locate it:

| term (x : Real) | before | cvc5 |
|---|---|---|
| `(distinct x 3)` | **unknown** | sat |
| `(distinct x 3.0)` | sat | sat |
| `(= x 3)` | sat | sat |
| `(<= x 3)` | sat | sat |

`=` and `ite` run `numeric_args` FIRST -- the SMT-LIB `Reals_Ints` rule that an
`Int` subterm in a `Real` context embeds via `to_real`. `distinct` type-checked
for identical sorts first and coerced never.

An empirical audit of every operator that can pair a `Real` with a bare numeral
(`=`, `distinct`, `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, `/`, `ite`, unary `-`)
found **`distinct` was the only one missing the rule**. `abs` on a `Real` also
diverges from cvc5, but `(abs ` appears **0 times in 15,446 corpus files** across
QF_UFLRA / QF_LRA / QF_NRA / QF_RDL, so it is not worth building.

### The near-miss

`distinct`'s own comment records this defect being found from the STRING side on
2026-08-20 -- *"`=` has no such pre-check and has always accepted them"* -- and
fixed with a **narrow packed-sequence exemption** instead of the general
coercion. Correct diagnosis, patched one case wide.

### Measured

`RandomDecoupled`, all 69 files, after the fix: **46 sat, 21 unsat, 2 unknown =
67 decided**, against 1 on the board. The two stragglers are the largest
parameters in the family.

For scale against everything else measured today:

| source | files |
|---|---|
| the `distinct` coercion, one division | **+66** |
| 320 commits (09-09 to 09-10), QF_UFLIA | +34 |
| this session's three solver fixes, all divisions | +7 |

### Why it survived

These files were recorded `unsolved`. Until `1d391d900` that was the same word
the harness printed for a reasoned `unknown`, a harness timeout kill, an OOM
abort and a crash. **A file refused at the door in 35 ms and a file that thought
for 24 s were indistinguishable in every row of PARITY.md.** The fix in section 5
is what made step two of this chain possible.

### The generalisation does NOT hold

Probing the addressable-gap files of the other divisions for the same shape
(`attempts=1 last=fd:parse`): QF_ABV, QF_BV, QF_IDL and QF_LIA return **zero**.
Those gaps are real solver work. The front-door refusal was specific to
QF_UFLRA.

## Final attribution, all runs complete

Five divisions measured head to head against a BUILT BINARY of `e99d08848f`
(the 2026-09-09 board commit), interleaved per file on one host:

| division | 09-09 | HEAD | delta | gains | losses | flips |
|---|---|---|---|---|---|---|
| QF_UFLIA | 122 | 158 | **+36** | 36 | **0** | **0** |
| QF_LRA | 97 | 107 | **+10** | 10 | **0** | **0** |
| UF | 85 | 90 | **+5** | 5 | **0** | **0** |
| QF_ABV | 186 | 186 | 0 | 0 | 0 | 0 |
| QF_BV | 185 | 185 | **0** | 0 | **0** | 0 |
| QF_IDL | 50 | 50 | 0 (90 files) | 0 | 0 | 0 |

**QF_BV's board `-2` is not a regression.** 200 files, zero gains and zero
losses: no code since 09-09 touches this division at all. Consistent with the
+-1.5 spread measured at fixed code.

**QF_IDL needs its baselines named.** arm A reads +0, but QF_IDL's last prior
board row is **2026-09-06** (105) while arm A's baseline is **09-09**. The
board's +8 landed in the 09-06 -> 09-09 window, which no arm here covers. The
two numbers are not in conflict; they measure different intervals.

### This session's three fixes, isolated

`f09652489` (their parent) vs HEAD, both divisions run to 200 files:

| division | base | HEAD | delta | losses |
|---|---|---|---|---|
| QF_UFLIA | 156 | 161 | **+5** | 0 |
| UF | 84 | 89 | **+5** | 0 |

QF_UFLIA's five are `hash_sat_09_17` .. `hash_sat_10_20` — the TOP rungs of a
ladder the 320-commit window had carried to 09_14 — each landing at 18.6-19.1 s
against a 24 s budget. UF's five include `smtlib.1116374.smt2`, the file
roadmap item 3.10 named BY PREDICTION when `318930806` landed.

Both of these were reported as **+0** earlier in the day from 60- and 12-file
prefixes. The pinned lists are path-sorted, so hard families cluster at the
head and a prefix structurally cannot show the effect. Two nulls, same cause.

## The front-door refusal did NOT generalise

All 177 addressable-gap files across nine divisions, probed for the
`last=fd:parse` signature that found the QF_UFLRA bug:

| division | probed | at `fd:parse` |
|---|---|---|
| QF_LRA | 40 | 0 |
| QF_NIA | 37 | 0 |
| UF | 28 | 0 |
| QF_LIA | 18 | 0 |
| QF_IDL | 14 | 0 |
| QF_UFLIA | 13 | 0 |
| QF_ABV | 12 | 0 |
| QF_BV | 8 | 0 |
| QF_SLIA | 7 | **2** |
| **total** | **177** | **2** |

Both QF_SLIA hits are benign: one is `str.replace_all over a non-constant
operand is outside the wired sound subset` — a deliberate, documented boundary
— and the other declines elsewhere. **The QF_UFLRA bug was local**, and the
campaign it suggested does not exist.

### The `distinct` fix costs nothing

All 67 `RandomCoupled` files, pre-fix vs post-fix binaries interleaved:
**67/67 identical, 0 gains, 0 losses.** The coercion only fires when an operand
is already `Real`, so it unlocks the family that could not parse and touches
nothing else. An apparent `-8` seen while comparing a LOADED s4 run against the
board's quiet-host row was entirely that confound.

## CORRECTION: the board uses THREE references, and I reported them all as cvc5

`scripts/parity-run.sh` selects the reference binary PER DIVISION by logic
family. Today's sixteen rows use three different solvers:

| reference | divisions |
|---|---|
| cvc5 1.3.4 | QF_DT, QF_IDL, QF_LIA, QF_LRA, QF_NIA, QF_NRA, QF_RDL, QF_S, QF_SLIA, QF_UF, QF_UFLIA, UF |
| **bitwuzla 0.9.1** | **QF_ABV, QF_BV, QF_FP** |
| **Z3 4.13.3** | **QF_UFLRA** |

Throughout this session I wrote "vs cvc5" for every row. That is wrong for
**four of sixteen divisions**, including two results I highlighted:

- `QF_FP` **199/200** is near-parity with **bitwuzla**, a specialist FP solver
  — arguably a HARDER bar than cvc5, so the result reads stronger, not weaker.
- `QF_UFLRA` 76 -> 142 is measured against **Z3 4.13.3** on BOTH rows.

The repository already carries this rule
(`reference-solvers-are-not-the-frontier`: *always name the reference when
quoting a gap*). I broke it by assuming one referee and never reading the
field, in nearly every summary today.

**The QF_UFLRA before/after is therefore CLEANER than `a6d4709b5` claims.**
That commit message says the 16:44Z row used cvc5 and warns the pair is not a
clean reference-side A/B. Both rows use Z3 4.13.3 and both score it at 198/200.
Same list, same protocol, same reference, one commit apart: **76 -> 142, +66,
zero files lost**. The warning in that message is withdrawn.
