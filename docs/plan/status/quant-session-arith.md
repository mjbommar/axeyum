# Lane: quant-session-arith

**Focus.** The quantifier-instance session hosts the arithmetic theory beside its
`EUF` e-graph instead of abstracting the arithmetic away, so its `unsat` can be a
Farkas conflict rather than only a congruence one (ADR-2130, building on
[ADR-2124]).

**Status.** Level 2 implemented and measured. The lever ships **OFF**
(`GROUND_SESSION_LEVEL = 0` unchanged). See ADR-2130 for the decision and the
numbers.

## What landed

| what | where |
|---|---|
| exit-1 sizing, with ADR-2124's own population re-derived | `bench-results/quant-session-arith-20260916/sizing-ledger.py` |
| the composite theory (`EUF` + `LIA`, one shared atom index space) | `crates/axeyum-solver/src/qinst_session_theory.rs` |
| level 2 of the ground-session lever | `crates/axeyum-solver/src/qinst_egraph.rs` |
| the two ground-check schedules, named and registered | `GroundCheckSchedule`, `ground_check_split_round` |
| the engagement probe and its comparison | `bench-results/quant-session-arith-20260916/engagement-*.{sh,py}` |

## Three corrections to the brief, each verified in-tree

- **`TheorySolver::take_new_atoms` is not the hook for this route**, and using it
  would have been a wrong-answer defect: it is polled inside a solve, so it
  cannot hand an index back to a caller still building the clause the variable
  belongs to (`native_cdclt.rs:340-352`). The warm route registers through the
  driver-side channel. The composite's `take_new_atoms` returns `0` always, with
  a fixture pinning it.
- **ADR-2125 did not build a bound trail to reuse.** It built `sync_cube` for the
  offline cube loop and its lever ships `off`; the bound trail is older
  (ADR-1701 / ADR-2122) and lives on `LraTheory`, not `LiaTheory`. There is
  nothing to reuse — and nothing to build: `IntSimplexEngine::sync` re-derives
  the imposed bounds from the live set on every check, so `LiaTheory::pop` IS the
  retraction.
- **`LiaTheory` lives in `lia_online.rs`**, not `lra_online.rs`.

## What is left

- `simplex::Incremental` has no row- or column-append method, so a growth event
  REBUILDS the arithmetic tableau. A real `add_row` is the next increment.
- No interface equalities are propagated between the two sub-theories. That is
  an incompleteness, free here because the session's `Sat` is never a verdict,
  and it is what `CombinedIncrementalLia`'s machinery would supply.

[ADR-2124]: ../../research/09-decisions/adr-2124-incremental-ground-closure-for-quantifier-instances.md
