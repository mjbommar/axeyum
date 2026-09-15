# coordinator-solver — the dispatch and instrumentation plan of 2026-09-15

<!-- plan-section: lane-status -->

Status: **in progress**, one lane measuring. Phases 1, 2 and 3 of
[dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md)
are on `main`, each with an ADR and a measured exit criterion; Phase 1b's
nine-division A/B is the open item. Phase 4 has not started and is conditional.

## What landed, in order

| phase | ADR | what it closed | measured |
|---|---|---|---|
| sizing | — | 254 routing-output readers classified by reading each; the Tier 1 harness never kept per-file output | 47 direct readers, 28 blind to `; partial`; ladder STOPPED on `Unknown` in **604 of 645** undecided rows |
| 2 | 2101 | `partial` is a field, `Route` is a type, one reader replaces seven greps | three live consumer defects found by the migration; ADR-2075's 12 → 9 |
| 1 | 2100 | ownership declared per rung; `hand_back_unless_refuted` deleted; rustc named 17 sites | 1,800-row A/B net 0 (+2/−2), 0 flips; sizing **0 of 645** — for the bug class, not a gain |
| 2b | 2104 | 25 free-string decline details are closed enums (ADR-2101 counted 44: helper callers) | one mutation, one kill; three orphan controls registered |
| 3 | 2102 | one ledger, three writers, staleness rule | ADR-2065's 14 movers exact; ADR-2045's 74 → 59 on today's tree; ADR-2075's 7 of 9; `--trace` moved 0 of 100 verdicts |
| 3b | 2105 | typed name and construct set in the trail JSON; the process-global recorder deleted | first-writer-wins proven on a quantified query; ledger's two empty columns fill |
| — | 2090 | assertion selection: z3's minimal cores are median 3 conjuncts and we still fail 193 of 230 of them | ceiling **36 of 645**; nothing built |

## What the instruments now agree on

Two independent measurements point at the same place. PLAN-SIZING: the ladder
stops on an owning rung's `Unknown` in 93.6 % of undecided Tier 1 rows.
CORE-SELECT: handed the reference's own minimal core, the quantified engine
gives up at 13 s after ~20 attempts — 12 e-matching fixpoints, 17 mbqi datatype
declines, 5 unreached nested quantifiers, 4 bounded at integer width 32. Neither
ladder had a routing gain hiding in it (Phase 1: 0 of 645; Phase 1b: 0 of 482).
The next capability lanes go at those four give-up classes, at their own
denominators.

## Open

- **QUANT-LADDER-OWNERSHIP (ADR-2103)** — the `q:*` ladder under the ownership
  rule plus a bounded continuation share. Live defects closed on the way (eight
  bare `?`s in `q:checked-fast-path`; `q:egraph` asking what `q:mbqi` supports).
  600 of 1,800 rows: +2, 0 losses, 0 flips, and both of ADR-2100's lost files
  decide again. Six divisions and the 3× movers recheck outstanding; merges when
  the criterion is measured, not before.
- Phase 4 (derived ladder order) runs only if the ledger shows structure.
- Not this plan's: `check-merge-hygiene.sh` fails on any host with a fresh
  `shape_search` binary — two unadjudicated `AlgS` duplicate groups.

## Corrections worth keeping

- Two consecutive push logs ended in `failed to push some refs` with no
  `pre-push: FAILED` line; I blamed the tool timeout, relaunched detached, and
  it died at the same step. The step after the last `ok` — the unit sweep — was
  red on main (an unregistered sentinel constant). Run that step by hand.
- ADR-2101's "44 free-string sites" counted callers of two unchanged helpers;
  rustc's number was 25.
- A Sonnet lane's forked helpers inherited the whole brief and rebuilt both
  deliverables in parallel. Helpers get their slice only, as fresh agents.
