# The remaining gap is two populations, not one

**2026-09-13.** For every division with a board, every file where **we return
`unknown` and a reference decides**, split by *what the answer is*. Derived
mechanically from the committed board TSVs — `polarity.tsv` is the output, and
the generator is in this README's sibling commit message so it can be re-run.

**2,166 winnable files: 606 `sat`, 1,560 `unsat` — 28% satisfiable overall.**

That aggregate is misleading. The per-division split is **bimodal**:

## Refutation-bound — a model finder buys nothing here

| division | sat | unsat | sat share |
|---|---:|---:|---:|
| AUFDTLIRA | 0 | 135 | **0%** |
| UFDTNIRA | 0 | 178 | **0%** |
| AUFNIRA | 0 | 139 | **0%** |
| UF | 0 | 29 | **0%** |
| AUFLIRA | 1 | 186 | 1% |
| UFLIA | 1 | 72 | 1% |
| UFDT | 1 | 55 | 2% |
| UFNIA | 2 | 59 | 3% |
| FP | 7 | 112 | 6% |
| AUFLIA | 8 | 71 | 10% |

## Model-finder-bound — refutation work has a hard ceiling here

| division | sat | unsat | sat share |
|---|---:|---:|---:|
| QF_IDL | 34 | 4 | **89%** |
| ABV | 15 | 2 | 88% |
| QF_UFLRA | 43 | 11 | 80% |
| QF_S | 11 | 3 | 79% |
| ALIA | 24 | 12 | 67% |
| QF_UFBV | 57 | 30 | 66% |
| QF_NIA | 72 | 38 | **65%** |
| QF_DT | 52 | 29 | 64% |

## Why this is worth having

**It explains a result rather than just describing one.** ADR-1965 moved 273
verdicts in AUFLIRA and AUFNIRA and **every single one was `unsat`**. That was
not luck: those divisions are 1% and 0% satisfiable. A congruence capability is
a refutation capability, and it was pointed at a population made of refutations.

**It predicts where refutation work will fail.** ADR-1971 sized outer
read-over-write at 934 files and measured **0**, with its first and decisive
reason being that 39 of 53 winnable ALIA+ABV files are satisfiable — read-over-
write is a refutation mechanism and cannot produce a `sat`. That reasoning
generalises to QF_IDL, QF_UFLRA, QF_S, QF_UFBV, QF_NIA and QF_DT: **~340 files
across eight divisions sit behind quantified model construction**, and no amount
of refutation capability reaches them.

**It flags a misaimed target.** QF_NIA is #5 on the Tier-1 list and is **65%
satisfiable** — the opposite of its four neighbours. Lanes aimed at it have
chased refutation paths (the width ladder, the CNF budget) and two returned
zero. That is consistent with this table and was not consistent with the brief.

## How to use it

Before sizing any capability, ask which half it can produce. A refutation rule
has a ceiling equal to the `unsat` column, **before** you ask whether it reaches
anything — which is the check ADR-1971 recommends running first, and the one
that would have killed a 934-file target in an afternoon.

## Caveats

- "Winnable" means a reference decides it at the board's 24 s budget. A file
  neither reference decides is excluded from both columns, so this is a
  statement about the *reachable* gap, not the whole corpus.
- The polarity is the reference's verdict, not ours. Where z3 and cvc5 disagree
  (0 rows on every board measured so far) this would need a tiebreak.
- Divisions with fewer than 10 winnable rows are in the TSV but omitted from the
  tables above.
