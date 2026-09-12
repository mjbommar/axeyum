# What to build to move the number

**Written 2026-09-12 at `1f36f28b3`.** The board is
[`bench-results/board-20260912/`](../../bench-results/board-20260912/README.md):
**2,517 of 4,000 (62.9%)** against best-of-z3/cvc5 at **3,432 (85.8%)**. Gap
**915**.

This file is the build queue, ordered by measured files-per-unit-work. Every row
cites the measurement that sized it. **A row with no measurement is not on this
list** — that is the rule the last session earned the hard way, with four wrong
censuses.

---

## 1. Datatype fields and UF over datatypes — 295 of 600 sampled

**The single largest identified, actionable capability gap.** Two halves of one
feature, and the measurement is explicit that they must be priced together:

| capability | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| UF applied to a datatype argument | 32 | 54 | 57 | **143** |
| array/UF-sorted datatype FIELDS in `datatype_native` | 70 | 29 | 53 | **152** |

ADR-1920 named the first as BUILD NEXT — *"Ackermann congruence over expanded
datatype arguments … restricted to datatypes whose fields are all scalar, and
that restriction has to be a checked precondition in the scan, not a comment"*.

**The second half is why the restriction is the problem.** These divisions are
SPARK/Ada verification conditions and the Barrett/Reynolds codatatype family;
their records have `(Array Int Int)`-valued fields — exactly what "all fields
scalar" excludes. **Doing only the ADR-1920 slice leaves 152 of 600 where they
are.**

Source:
[`the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md`](../research/03-measurements/the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md) §5.

Divisions in play: AUFDTLIRA (gap 135), UFDTLIRA (109), UFDT (52) = **296 board
files**.

**Soundness note, non-negotiable.** SMT-LIB leaves `sel(t)` UNSPECIFIED when `t`
was not built by that constructor. A chosen-total convention is sound to READ
and unsound to ASSERT. Two wrong `unsat`s shipped this week from exactly that,
both in datatype code. Any lane here writes a soundness-negative test that fails
on the unsound version.

## 2. QF_NIA's preprocessed dispatch timeout — 41 of 110

QF_NIA is the largest single-division gap on the old board (**103**). Two
hypotheses are already closed by measurement, so do not re-open them:

- **Width escalation: DO NOT BUILD.** ADR-1921 — decides 0 of 110, costs +4.6%
  wall, and destroys 23 precise diagnoses. 14 of 20 residual files overflow at
  width 64, the blaster's hard ceiling; 128 needs a bigint model read-back.
- **CNF clause budget: measured negative.** Lifting it by the estimator's own
  9.4x slack decides 0 of 49.

What is left is the **preprocessed dispatch timeout, 41 of 110 (37%)** — the
largest class and the only one with no measurement against it.

**Check this first, cheaply:** QF-NRA proved that this exact sentence is a
RELABEL — `dispatch_reduced` replaced the reduced solve's reason instead of
carrying it, and 13 of 18 such rows were really the CAD wall. That fix landed in
`f278b54e2`. **Re-census QF_NIA on current main before building anything**; the
41 may already have decomposed into honest causes.

## 3. QF_LIA — the largest gap with no diagnosis at all

**53 board files.** 48 of 55 winnable files burn the entire budget (28 watchdog
kills, 20 near-budget); only 7 decline early. z3 does them in 3.4 s mean.

Nothing else is known. This is the one large gap where no lane has ever run a
census. **Diagnose before building** — and use the phase-breadcrumb instrument
from `8860e2a60`, which is what makes a watchdog kill legible at all.

## 4. The residual watchdog — 49 of QF_UFLRA's 51, plus QF_IDL

`8860e2a60` took watchdog kills 92 → 81 across 98 files and converted 2. The
remaining 81 still overrun their own deadline. Two named families dominate
QF_UFLRA (`32_1_cilled…`, `minepump_spec*_product*`).

The lane left a precise next reading: on `minepump_spec1_product56` at 24 s,
`uf-arith-lazy-overbound` declines in good order at 17,998 ms with
`reason=budget` and `euf-online` at 6 ms, and **the remaining ~6 s goes to a
route after `euf-online` that has no breadcrumb frame yet**. Add the frame,
re-read, fix.

Value is mostly contract rather than capability — but a killed run loses the
model, the proof and the evidence, so it also blocks diagnosis everywhere else.

## 5. The early decliners — ~42 in QF_LRA and QF_IDL

Unclaimed, and cheap to diagnose because they state a reason before the budget:
QF_LRA 23, QF_IDL 19. QF_IDL is cleanly bimodal — 19 killed, 19 declining early,
nothing between.

Constraint already measured: **QF_LRA is not the clock.** 0 of 40 gap files
decide even at a 120 s budget, so the route is wrong for these problems rather
than slow. Do not propose more time.

## 6. QF_NRA needs an engine, not a fix — 70 files

Do not send a bug-fixing lane here. After `f278b54e2` the division reads **46 of
77 (60%) the linear abstraction's own boundary**, and the rows say so
themselves: *"this needs an nlsat/CAD engine"* (ADR-0058 Phase C/D). 26 are
clock, 5 other.

QF-NRA-ROUTE already fixed a real defect in the largest class (20 files) and
moved **zero** files, because an error and an `unknown` are both "not decided".
That is the evidence that the remaining work here is a decision procedure, not a
repair. It needs an ADR and a design, not a lane brief.

---

## Not on this list, deliberately

- **Nested arrays — 29,564 files.** `ArraySortKey` is a flat non-recursive enum
  so `Sort` stays `Copy`. Structural; needs an ADR and a design decision about
  the IR before any lane. The size is tempting and that is the trap.
- **The 64 divisions still unmeasured.** 20 of 84 are on the board. Three more
  (`QF_ABVFP` 18,129, `QF_BVFP` 17,249, `QF_UFBV` 1,510 = **36,888 files**) are
  marked REACHED-SOLVER and need **only a measurement run, no code**. That is
  coverage, not capability — cheap, and it belongs to whoever wants the
  divisions-covered number rather than the gap number.
- **Anything justified by a count of a failure MODE.** 149 watchdog kills
  yielded 2 converts in QF_UFLRA. A census says how often something happens, not
  how many files a fix wins.

## How to size the next lane

1. Census the WHOLE winnable population, never a prefix — these lists are
   path-sorted, so a small sample is a sample of one family.
2. Confirm the dispatch ran to the end before ranking reasons: `attempts=` in
   `--trace` against the ladder length. A census can measure the ladder instead
   of the solver.
3. Interleave A/B arms per file on one core, and re-run any single-pairing
   surprise — a 16 s baseline against a 24 s budget flips under load.
4. Assert the `test result:` line and its numbers for every gate. A killed run
   prints test names and no result; exit 15 and 143 are both OOM here.
