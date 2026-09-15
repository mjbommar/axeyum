# Lane: route-ownership — the ladder consults a declaration, not an error variant

<!-- plan-section: lane-status -->

**Lane route-ownership (`DONE`, route-ownership, 2026-09-15).** Phase 1 of
[docs/plan/dispatch-and-instrumentation-2026-09-15.md](../dispatch-and-instrumentation-2026-09-15.md),
closed by [ADR-2100](../../research/09-decisions/adr-2100-typed-route-ownership.md).
Whether a ladder rung's non-decision stops the ladder is now decided by an
**ownership declaration on the route**, not by which error variant the rung
happened to return. `hand_back_unless_refuted` — the same rule hand-written for
one rung by ADR-2065 — is deleted.

Branch base: `git merge-base main HEAD` is `6ac97756c`, local `main`'s HEAD after
the TRACE-API (ADR-2101) and PLAN-SIZING merges.

## What changed

**The rule, stated once.** `route_ownership` in `auto.rs` declares per rung the
construct classes it owns (eleven classes, one per `Features` flag) and whether
it is the ladder's `Decider` for that fragment or a `FastPath` above one.
`settle_rung` and `record_route_refusal` apply one table at every rung:

| the route's answer | `Decider` that owns the query | anything else |
|---|---|---|
| `Sat` / `Unsat` | decides | decides |
| `Unknown` | terminal | **decline**, ladder continues |
| `Err(Unsupported)` | **reported inconsistency** | **decline**, ladder continues |

**`RouteKind` is the distinction ownership ALONE gets wrong**, not a softening
of it. `datatype-elim` (ADR-0022 step A) refuses BY DESIGN so `datatype-native`
(step B) gets the query; under ownership alone that hand-off reads as an
inconsistency on every `QF_DT` file.

**The compiler enumerates the sites.** `DispatchError` has no
`From<SolverError>`, so every `?` and `return Err` in `check_auto_dispatch_inner`
is a type error until its site names a rung. `rustc` named **17**.

## Numbers

| | |
|---|---|
| Phase 1 ceiling on Tier 1 (`stopped_by_unknown` rows with an owning, enterable route below) | **0 of 645** |
| undecided Tier 1 rows that never reach the QF dispatch ladder at all | **482 of 643 (75 %)** |
| `Err(Unsupported)` sites in the ladder, enumerated by `rustc` | **17** |
| ADR-1966's pinned propagation population, before / after | **63 / 63**, two entries swapped, one real site closed |
| mutation: the ownership check deleted | **kills exactly 1** named fixture |
| mutation: the inconsistency report deleted | kills 1 |
| mutation: `FastPath` collapsed into `Decider` | kills 2 |
| A/B: rows / flips / `:status` disagreements | **1,800 / 0 / 0 of 865** |
| A/B: stable gains / stable losses, all 11 movers re-run 3x per arm | **2 / 2**, net **0** |
| solver lib sweep, `corpus_regression`, `progress_frontier` | 1,805-0 / 2-0 / **12-0, no frontier regression** |

## What the lane's own instruments caught, that reading did not

- **The regression fixture was vacuous and the mutation control said so** —
  SURVIVED, 20 tests, none depending on the guard. Preprocessing folds the
  read-over-write before dispatch, so `lira-dpll` never ran. Its own
  non-vacuity guard missed it because the guard accepted `nra` as well as
  `lira-dpll`: **a non-vacuity check that admits a route other than the one
  under test is not one.**
- **This lane's trace runner had ADR-2075's bug** — anchored on `^; route `,
  dropped the 103 rows whose watchdog path prints `; partial route `.
- **The sizing's first answer was 102 and its second was 5**; both were
  artifacts of modelling the ladder from source text rather than from control
  flow, and from confusing "owns a construct" with "is enterable on it".

## Left undone, named

- **Exit criterion 3 is NOT MET on losses: 2 of them, reproducible 3/3.** The
  A/B is 1,800 rows over nine divisions, both arms back to back on one pinned
  core, order alternating, 24 s / 8 GiB, 12 shards on s5/s6/s7 (`ab-run.sh`
  refuses if the two binaries hash the same). **0 flips, 0 `:status`
  disagreements over 865 comparisons, 0 exit-status differences after re-check,
  +2/-2 net 0.** Both losses are the documented cost mechanism, measured off
  both arms' trails: routing does not change (`q:egraph` both sides, `q:mbqi`
  binding to the millisecond) -- the same fifteen seconds buys 25 attempts
  instead of 35 and 45, because a sub-solve that used to stop at a terminal
  `Unknown` now runs the rest of the QF ladder. One of the two files is
  literally in ADR-1966's own loss list.
- **The two losses are named, not absorbed**:
  `AUFDTLIRA/.../Q525-025__controlling_result__fixed_string.adb_18_11_length_check`
  and `AUFDTLIRA/.../R509-011__higher_order_proof__why_bfafe7_...fold-T-defqtvc`.
  The obvious narrowings all put a route back in the position of deciding on
  another route's behalf, which is the defect.
- **The quantified ladder in `solve` is untouched.** It is a different ladder
  with its own decline discipline (ADR-1927), and 75 % of Tier 1's undecided
  mass ends there. Typing its rungs the same way is the obvious next slice and
  is NOT claimed here.
- **`dispatch_nonlinear_int_tail` and the bit-blast fallback carry no route.**
  Both are terminal by position, which is ADR-1966's own classification of the
  first; an ownership declaration decides nothing about a rung with nothing
  below it.

<!-- plan-section: landed-changes -->

| 2026-09-15 | `1b895bf68` | The design note and the ownership table, before any dispatch code moved. |
| 2026-09-15 | `d1bdd020b` | The rule: `route_ownership`, `settle_rung`, `record_route_refusal`. `hand_back_unless_refuted` and `ArithRun::abstracted_opaque_reals` deleted. |
| 2026-09-15 | `eeecd4e48` | Five ownership tests, each deriving its population from the authority; ADR-2065's five assertions relocated to where the guard now lives (ADR-1980's method). |
| 2026-09-15 | `b6c0498bc` | `DispatchError`, the channel with no `From<SolverError>`; the seventeen sites `rustc` named, each closed by its rung. |
| 2026-09-15 | `99a02b66a` | The mutation control found the regression fixture vacuous, and the trace runner found to have ADR-2075's prefix bug. Both fixed; the ADR-2101 partition check added. |
| 2026-09-15 | `f7fcbe65d` | The sizing: **0 of 645**, with the three corrections that got there and the 75 % that never reach this ladder. |
| 2026-09-15 | `8a07eb2e0` | ADR-1966's ratchet re-pinned, 63 → 63, with a control proving it still fires on a re-introduced site. |
