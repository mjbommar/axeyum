# coordinator-solver — the three improvement lists (cindergraph, Glaurung, Axeyum)

<!-- plan-section: lane-status -->

Status: **round one in flight, 2026-09-16 evening**. The user's goal is to
work through the three lists written the same afternoon:
[Axeyum](../improvement-list-2026-09-16.md) (committed, `8df853252`),
cindergraph `docs/improvement-list-2026-09-16.md` and Glaurung
`docs/development/improvement-list-2026-09-16.md` (both untracked in the
user's clones at `../cindergraph` and `../glaurung`). Foreign-repo lanes work
in their own `git worktree` under `/data0/axeyum/scratch/wt-*` on a branch,
commit there, and never push; Axeyum lanes use the usual isolated worktrees.


## Round one (parallel)

| lane | repo | items | model | notes |
|---|---|---|---|---|
| CG-EXPORT | cindergraph | 1, 2, 4, 5, 6, 8, 9, 10, 11, 14 | Opus | branch `cg-export-2026-09-16`; must keep the Axeyum consumer's table unchanged |
| GL-PIN | Glaurung | 1, 2, 6, 8, 9 + a `solver-NNN` decision record | Opus | branch `gl-pin-2026-09-16`; pin → Axeyum `8df853252`; 733 malformed corpus files quarantined, 107 valid become a verdict set |
| AX-BINDINGS | Axeyum | 1, 2, 3, 4, 13 | Sonnet | example on `axeyum.smt`, overflow predicates, `axeyum-bench` `full` feature, doc pointers, Python example inventory |
| AX-PROPTEST | Axeyum | 5 | Opus | ADR-2141 if a decision; inventory of every boxed generator, reachability per row, mutation control per finding |
| AX-POLICY | Axeyum | 6, 7, 9 | Opus | ADR-2140; `ModelPreference {Any, PreferZero, LeastUnsigned}`, bounded minimisation, `stats()` in the bindings; QF_BV A/B on s7 |

## Round two (after round one lands)

| lane | repo | items | depends on |
|---|---|---|---|
| CG-OPS | cindergraph | 3 (typed operations export) | CG-EXPORT merged (one lane per foreign repo at a time) |
| GL-SIXCELL | Glaurung + `scripts/run-glaurung-six-cell-neutral.py` | 3 (the timing campaign) and Axeyum 14 | GL-PIN merged |
| AX-CACHE | Axeyum | 8 (canonical constraint cache in the incremental engine) | AX-POLICY merged (same file) |
| AX-LIFTER | Axeyum | 10, 11, 12 (loop unrolling, more sinks, real inputs) | AX-BINDINGS merged; CG-EXPORT's attributes reduce the lifter |
| AX-GATE | Axeyum | 16 (wire `check.py` into a gate) | cindergraph `__version__` and a pinned dependency |
| A13 | Axeyum | 15 (the solver queue) | last, per the user's ordering |

## Merge discipline

Axeyum lanes: verify on the branch (battery clippy, workspace check, the
suites the lane names, fmt, hygiene, gating, anchors, registry, links, PLAN
and ADR index current), merge `--no-ff -F msgfile`, regenerate PLAN.md and the
ADR index on conflict, run the cheap gates, push in a batch. Foreign lanes:
merge the branch into the clone's default branch locally after the same
verification in that repo's own terms; pushing those two repositories is the
user's call and is not done by this coordinator.
