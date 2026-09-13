# Lane: qf-nia-sat — QF_NIA is model-bound, ADR-1937 already took the sat half, and the one hypothesis left is worth four

<!-- plan-section: lane-status -->

**Lane qf-nia-sat (`DONE`, qf-nia-sat, 2026-09-13).** The brief's hypothesis —
*QF_NIA is held by model production, not refutation power* — is **confirmed**,
on the strongest evidence available: every one of ADR-1937's **32 gains on the
winnable population was `sat`, zero were `unsat`**. Its *sizing* is stale in the
same breath. The "64 sat of ~110 winnable" is read from a board snapshot taken
before ADR-1937, which harvested exactly those files. **Remaining winnable is
78 = 40 `sat` + 38 `unsat`** — near balanced, not 65 % sat.

The brief's three-way sat-half split collapses to one bucket: **the
"model produced, replay failed" class is EMPTY** (25 files at the previous
census). ADR-1937 closed it. All 78 remaining losses are *no model produced*.

The one unrefuted hypothesis in the tree — an **eager** small-domain
multiplication split — was built as a **sound one-way surrogate outside the
solver** and sized at **3–5 of 29 against a ±1 noise floor**. **Do not build.**
No solver code changed.

ADR: [ADR-1976](../../research/09-decisions/adr-1976-qf-nia-is-model-bound-adr-1937-took-the-sat-half-and-the-eager-split-is-worth-four.md)
· artifact: [`bench-results/qf-nia-sat-20260913/`](../../../bench-results/qf-nia-sat-20260913/README.md)

## The polarity census — the whole winnable set, not a sample

| ADR-1937 armed verdict | ground truth | files |
|---|---|---:|
| `sat` | `sat` | **32** |
| `unknown` | `sat` | 40 |
| `unknown` | `unsat` | 38 |

## The sat half by cause, and the clock asymmetry

| failure mode | sat | unsat |
|---|---:|---:|
| no model produced | **40** | 38 |
| model produced, replay failed | **0** | 0 |
| model produced, too late | 0 | 0 |

| | spends ≥98 % of the 24 s budget | median budget used |
|---|---:|---:|
| `sat` half (40) | 8 of 40 (20 %) | **45 %** |
| `unsat` half (37) | 33 of 37 (89 %) | **100 %** |

**29 of the 40 sat files refuse at the pre-lowering CNF clause estimate at a
median 11.8 s, leaving a median 13,172 ms — 55 % of the budget — used by
nothing** (ADR-1950 by-budget split, ADR-1971 decline times, ADR-1941 `bound_by`
= `nia-linearize` on all 29). Raising that budget is a closed question: a
previous lane measured its own 9.4x slack lifted at **0 of 49**, and all 30
estimates here sit inside that factor (1.16x–4.49x, median 2.00x).

## The sizing, committed before any solver code

| condition | decided |
|---|---:|
| surrogate, whole 24 s budget | 6 of 29 |
| **in-solver, rung at its natural position** | **4 of 29** |
| noise floor, 3 repeats at one commit | **4 / 3 / 5** |

`29 → 3–5`, four files of a 78-file gap, noise half the effect. The upper end
needs the split moved ahead of `int-real-relax` and `nia-linearize`, taxing
every integer query in every division.

## The finding worth carrying — a sat-side reference control is vacuous

The surrogate's natural control (z3 + cvc5 on the transformed file vs the
original `:status`) reported **0 disagreements on 29 of 29, 0 no-opinion rows**
— and reported **0 disagreements on a deliberately broken transform too**, 5 of
5. A satisfiable underconstrained query stays satisfiable under a wrong rewrite;
it just gets a different model. The control with teeth runs the transform over
the **unsat** half:

| arm | unsat files z3 turned `sat` | requirement |
|---|---:|---|
| correct | **0** | must be 0 |
| mutant (off-by-one scaling) | **6 of 10** | must be ≥ 1 |

`scripts/qf-nia-sat-transform-control.py` exits non-zero on either violation, so
its zero cannot be quoted without its six.

## Landed changes

| change | what |
|---|---|
| `bench-results/qf-nia-sat-20260913/` | population, census, surrogate, 3 noise repeats, two-arm control, README |
| `docs/research/09-decisions/adr-1976-*.md` | the decision and the vacuity finding |
| `scripts/qf-nia-sat-*.py` (8) | population, census split, budget detail, surrogate, residual shapes, realistic budget, in-slice budget, transform control |

No `crates/**` changes; no new Rust suites, so no `hooks/pre-push` entry is due.

## What should happen next at this division

1. The **38 `unsat` files are now the larger half** and are genuinely clock-bound
   (89 % spend the whole budget). Quote the post-ADR-1937 polarity, not 65 %.
2. **Thirteen seconds per sat file are used by nothing.** A route producing a
   candidate model without blasting the whole query runs in a free budget. A
   direct small-witness enumerator over the declared `[-2,2]` boxes is unsized
   and is the obvious next candidate — those variables are exactly what a witness
   search would branch on.
3. `estimate_blast_clauses` has no numeral-operand case for `Op::BvMul`: 6 % on
   the original files (measured, correctly dropped) but **19 % measured here**
   once a rewrite introduces constant multiples. Matters for the next rewrite.
