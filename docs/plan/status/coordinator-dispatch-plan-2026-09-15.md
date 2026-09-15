# coordinator-solver — the dispatch and instrumentation plan of 2026-09-15

<!-- plan-section: lane-status -->

Status: **phases 1–3 landed and pushed** (`origin/main` `db31113fa`). Every
unconditional phase of
[dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md)
is on `main` with an ADR and a measured exit criterion. Phase 4 is conditional
on the ledger showing structure; lane LEDGER-STRUCTURE is measuring that
condition over 1,400 fresh Tier 1 rows.

## What landed, in order

| phase | ADR | what it closed | measured |
|---|---|---|---|
| sizing | — | 254 routing-output readers classified by reading each; the Tier 1 harness never kept per-file output | 47 direct readers, 28 blind to `; partial`; ladder STOPPED on `Unknown` in **604 of 645** undecided rows |
| 2 | 2101 | `partial` is a field, `Route` is a type, one reader replaces seven greps | three live consumer defects found by the migration; ADR-2075's 12 → 9 |
| 1 | 2100 | ownership declared per rung; `hand_back_unless_refuted` deleted; rustc named 17 sites | 1,800-row A/B net 0 (+2/−2), 0 flips; sizing **0 of 645** — for the bug class, not a gain |
| 2b | 2104 | 25 free-string decline details are closed enums (ADR-2101 counted 44: helper callers) | one mutation, one kill; three orphan controls registered |
| 3 | 2102 | one ledger, three writers, staleness rule | ADR-2065's 14 movers exact; ADR-2045's 74 → 59 on today's tree; ADR-2075's 7 of 9; `--trace` moved 0 of 100 verdicts |
| 3b | 2105 | typed name and construct set in the trail JSON; the process-global recorder deleted | first-writer-wins proven on a quantified query; ledger's two empty columns fill |
| 1b | 2103 | the `q:*` ladder under the ownership rule; eight bare `?`s in `q:checked-fast-path` closed; a bounded continuation share | sizing **0 of 482**; 1,800-row A/B net +4, 0 flips, 0 stable losses; ADR-2100's two lost files decide again |
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

- **LEDGER-STRUCTURE** — fills the ledger with 1,400 Tier 1 rows on
  `db31113fa` and answers the plan's §5 condition per feature class. Phase 4
  runs only if it reports STRUCTURE, with the ceiling in files.
- The four give-up classes CORE-SELECT located (e-matching fixpoint, mbqi
  datatype decline, unreached nested quantifier, integer width 32) are the
  capability lanes that follow this plan; none is dispatch.
- Not this plan's: `check-merge-hygiene.sh` fails on any host with a fresh
  `shape_search` binary — two unadjudicated `AlgS` duplicate groups.

## Corrections worth keeping

- Two consecutive push logs ended in `failed to push some refs` with no
  `pre-push: FAILED` line; I blamed the tool timeout, relaunched detached, and
  it died at the same step. The step after the last `ok` — the unit sweep — was
  red on main (an unregistered sentinel constant). Run that step by hand.
- ADR-2101's "44 free-string sites" counted callers of two unchanged helpers;
  rustc's number was 25.
- Both Rust lanes' briefs asked for `cargo check`, not clippy; the push battery
  found two lint errors after the merges. Briefs now name clippy on touched
  crates.
- A Sonnet lane's forked helpers inherited the whole brief and rebuilt both
  deliverables in parallel. Helpers get their slice only, as fresh agents.
