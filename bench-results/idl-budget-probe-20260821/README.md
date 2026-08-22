# QF_IDL budget probe — does more wall clock convert the `dl-online` timeouts?

Measured 2026-08-21 for §9.0.1 of the
[SMT capability gap analysis](../../docs/plan/gap-analysis-smt-solvers-2026-08-21.md).

## The question

The linear-arithmetic diagnosis found `dl-online` returning
`budget exhausted in the online difference-logic driver` on **64 of 65** traced
QF_IDL misses. That invites a budget-reallocation fix, because `dl_probe_budget`
holds back `min(t/4, 6 s)` for routes below the probe, and on those misses the
reserve goes to `lia-dpll`, which declines instantly on a size constant it could
have evaluated at `t = 0`.

Before building a conditional reserve, the prior question: **does more clock
convert these at all?**

## Method

Ten QF_IDL files from the pinned competition list that the diagnosis records as
missed and that z3 4.13.3 decides. Each run twice through the shipped front door
(`smtcomp_cli`, which is `solve_smtlib`): the competition budget of 24 s, and 5x
that at 120 s. Same binary, same box, runs adjacent in time.

## Result

**1 of 10 converted** (`a9.8.11.asp.smt2`, `unknown` → `unsat`).

One file (`DTP_k2_n35_c245_s18.smt2`) already decides at 24 s, where the
diagnosis recorded it as a miss — either contention in the earlier loaded run or
a gain from a same-day fix; not investigated, and it is excluded from the
conversion count either way since it converts at neither budget.

## What it decides

The achievable reallocation is 18 s → 24 s, i.e. **1.33x**, against a **5x**
experiment that converted 10%. So reallocating the reserve is not worth
building, and the QF_IDL/QF_RDL timeouts are not one constant factor from
finishing. This agrees with the QF_NIA diagnosis, which measured 4x wall clock
converting 3 of 35 and **0 of 20** timeout files.

Row 1's remainder is therefore algorithmic work — a faster difference-logic
search — rather than tuning.
