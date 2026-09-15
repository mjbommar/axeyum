# Lane: core-select — which ASSERTIONS to look at, and whether that is an axis at all

<!-- plan-section: lane-status -->

**Lane core-select (`DONE`, core-select, 2026-09-15).** Censused the minimal
refutable subset across the undecided rows of all seven Tier 1 divisions and
**closed the assertion-selection axis**: [ADR-2090]. Rules
[pre-registered](../../../bench-results/core-select-20260915/PREREGISTRATION.md)
before any measurement, with amendments A1–A5 written before the census counted
a row.

Branch base: `git merge-base main HEAD` is
`b78b887b3064b1075783ba6f4528519d07b1bbb6`, which **is** local `main`'s HEAD.

**Three senses of "selection", and this lane measured the third.** [ADR-2005]
measured *which representative TERM to substitute* (+0 of 129). [ADR-2020] named
*which INSTANCES to admit* as its open axis. This lane measured *which
ASSERTIONS to look at*. No number transfers between them.

## The answer, in one line

**The cores ARE small, a two-line rule DOES find them, and we still do not
decide them.** [ADR-2050]'s median-of-1 generalises — median `minimal` **3**
against a haystack median of **37**, `REF-UNSAT` **36.9 %**, both halves of R5
PASS — and it converts nothing: the ceiling on perfect selection is **36 of 645
undecided rows (5.6 %)** and the best reference-free rule reaches **7 of 645
(1.1 % `[0.5, 2.2]`)**. **R9 build gate FAILS; no lever built.**

## What the next lane should take from it

- **Do not size a lane against premise selection, relevance filtering or
  assertion pruning on Tier 1.** `suffix(1)` is two lines and is already near
  the top of the family.
- **The divisions are not one population.** Ceiling `UF` 8/12 = 66.7 % against
  `QF_NIA` **0 of 36 `[0.0, 9.6]`**. A lane briefed on the Tier 1 aggregate aims
  at neither.
- **`UFNIA` has a median haystack of TWO conjuncts** (81 of 146 undecided rows
  at ≤ 2), so the division with the largest undecided mass has nothing to select
  from before any solver runs.
- **The successor axes are named with their own denominators** in ADR-2090 §7,
  from the verbatim give-up details over the 193 rows where the ceiling is
  negative: 12 rows where e-matching reaches a fixpoint and says *more rounds
  cannot help*; 17 where `mbqi` declines a datatype fragment in three distinct
  wordings; 5 where instantiation does not reach nested or existential
  quantifiers; 4 bounded at integer width 32. **None of these is selection.**
- **64 of those 193 gave up in under 2 s of a 24 s budget and 73 ran ≥ 20 s** —
  a refusal and an exhausted clock behind the same `unknown`, roughly a third
  each.

## Method notes worth carrying

- **The board TSVs are snapshots.** Its `+4` hid **8 rows moving** (2 now
  decided, 6 newly undecided, 639 agreeing) — a third of the movement and the
  wrong direction for most of it. Re-derive, and report BOTH directions.
- **A disagreement and a non-answer are different findings.** This lane's first
  authority partition put 42 rows in `AUTHORITY-SPLIT`; the real split is 0
  disagreements at a comparable denominator of 194, 34 cvc5 non-answers kept and
  flagged, 8 rows z3 cannot re-check.
- **A minimal core of 1 means there is nothing to select**, not that the needle
  is easy to find: the single conjunct is the whole verification condition.

## Landed

| SHA | what |
|---|---|
| `ee8db8ebe` | preregistration, population, haystack census; two parser defects found by the census's own exit status |
| `9a49ea274` | the core instrument, validated against [ADR-2050]'s numbers and against constructions with a known answer |
| `f28bf4d4c` | weighted sharder, join, subset builder, pilot |
| `2cf3b4828` | `core-shape.py` — what a core IS, not only how many conjuncts |
| `91eff84e9` | preregistration amendments A1–A4 |
| `34a3f90ac` | the traced pass |
| `e9cec319e` | `collect.sh` (refuses a short sweep) and amendment A5 |
| `43a6b8dad` | the SInE-style relevance rule |
| `65fc272c3` | R1 — the re-derived population, both directions |
| `3198871be` | mutation control on the headline test |
| `2c42d84c0` | the census: 645 undecided, 236 `REF-UNSAT`, median minimal 3, R5 PASS |
| `e533aa5e7` | R6 — the ceiling, 36 of 645 |
| `94874b70d` | R7/R9 — best rule 7 of 645, build gate FAILS; 318-subset soundness audit |
| `f5b684f32` | the give-up contrast |
