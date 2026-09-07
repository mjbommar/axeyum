# coordinator-math — the five topics of 2026-09-06

Status: **all five landed and pushed** (origin `fcc988900`, 126 commits).
ADRs 1672–1679. Detail, corrections and process notes:
[notes/coordinator-math-five-topics-2026-09-06.md](../notes/coordinator-math-five-topics-2026-09-06.md).

| # | topic | result | ADR |
|---|---|---|---|
| 1 | retrieval index | builders 17/31 → **31/31**, derived from one table, census test fails on divergence | 1672 |
| 2 | ledger blind spots | a coverage ratchet that can fail; 8 capability facts; headline reworded | 1674 |
| 3 | SoS fallback | theorem name derived from the axiom footprint, not chosen | 1673 |
| 4 | ideal + `R/I` | 31 declarations; an ideal is one field more than an additive subgroup | 1676 |
| 4 | product space | 10 declarations; k-fold product rule **derived** | 1677 |
| 4 | metric completion | 16 declarations; carrier, embedding, isometry, estimate | 1678 |
| 5 | production metric | three-layer producer census; a held-out family priced | 1679 |

Topic 1's payoff was downstream: `check-trust-closure.py` was red with 21
`SUBJECT-ABSENT` rows whose subjects all existed and were proved, because the
projection example it reads built 22 of 32 preludes. Coverage took `absent`
21 → 0, failures 23 → 2. The residual 2 were left deliberately — `--update`
was NOT run, because silently accepting a new equivalence class to green a
gate is the defect the gate exists to catch.

Open, deliberately: deleting the SoS fallback (its frequency census has no
result); the ring first isomorphism theorem (gated as a test that reddens if
it stops being blocked); Hoeffding (waits on the marginal law); the
completion's remaining slice (no obstruction, stopped for budget).
