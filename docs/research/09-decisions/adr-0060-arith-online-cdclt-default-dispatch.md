# ADR-0060: Default dispatch for the arithmetic online CDCL(T) routes

Status: accepted
Date: 2026-07-07

## Context

Gap 3 (step 2b) of the
[2026-07-07 Z3/cvc5 gap analysis](../../../docs/plan/gap-analysis-z3-cvc5-2026-07-07.md)
frames the online CDCL(T) migration's next increment as "the default-dispatch
ADR — the routes are built but opt-in ('built, not yet banked'); termination /
livelock re-verify, then default-on + broad re-measure." This ADR resolves that
step for the **arithmetic** online routes (`QF_UFLIA` / `QF_UFLRA`), the sibling
of ADR-0055's decision for the string (`QF_S`) route.

**The "built but opt-in" framing is stale for the arith routes** — the same
class of staleness the gap doc itself flags for the "still eager Ackermann"
claim. Direct code inspection of `check_auto`'s dispatch
(`auto.rs::dispatch_uf_fast_paths`) shows the online EUF + linear-arithmetic
combination is **already first**, ahead of the eager Ackermann fallback, gated
only on the query's *features* — not behind any opt-in / `dark` config flag:

- On a mixed UF + linear-arithmetic query (`features.has_function &&
  has_arithmetic_function`), `dispatch_uf_arith_online` runs **before**
  `check_with_uf_arithmetic` (the eager route). Reals route to
  `check_qf_uflra_online`, integers to `check_qf_uflia_online`.
- The online route is **strictly additive**: it runs on a *clone* of the arena,
  returns only a `sat` (replayed inside the decider) or a verify-guarded
  `unsat`, and on any `unknown` (cap / unsupported shape) the caller falls
  through byte-unchanged to the eager route. The in-tree
  `uf_arith_dispatch_differential` is the load-bearing gate on this invariant
  (the online route never yields a verdict the eager route would not also
  reach — only sooner, or it declines).

Both online routes share one driver: the Boolean-structured case drives a
`crate::lra_online::Dpll` (1-UIP over the mixed implication graph, VSIDS, Luby
restarts, learned-clause reduction) over a live `CombinedIncremental` /
`CombinedIncrementalLia` (EUF + LRA/LIA Nelson–Oppen with registered
interface-equality variables); the conjunctive fast-path uses the same
`LiaTheory` / interface DFS. This is a *second* CDCL(T) driver alongside the
generic `crate::cdclt::CdclT` (which carries the EUF + string adapters of
ADR-0055).

**So step 2b for arith is primarily "ratify + document," not "flip a flag."**
The one substantive gap the termination re-verify surfaced is closed here.

## Termination re-verify (the soundness gate)

ADR-0055 established the default-on bar for a CDCL(T) driver: it must terminate
under an adversarial / non-monotone theory **even with no wall-clock deadline**,
degrading to `unknown` within budget rather than livelocking. Re-verifying the
arith driver against that bar:

- **Deadline polling — present and thorough.** `config.timeout` threads through
  the whole arith path as an absolute deadline: `check_qf_uflia_online` /
  `check_qf_uflra_online` derive it; `decide_conjunction` and the interface DFS
  (`Search::run`) poll `past_deadline` at every recursion node; `LiaTheory` /
  the combined state carry `.with_deadline`; `cdclt_combined` polls it while
  encoding the skeleton, adding interface clauses, and inside
  `Dpll::solve_with_deadline`, which checks the deadline at the **head of the
  search loop** and inside every unit- and theory-propagation fixpoint. A
  *deadline-set* run therefore cannot spin — it declines within the deadline
  plus one propagation round. This is not the "bounded-but-non-polling"
  anti-pattern.

- **The one asymmetry vs. ADR-0055 — the no-deadline case — now fixed.** Unlike
  `CdclT` (which carries a `DEFAULT_STEP_BUDGET = 16_000_000` defense-in-depth
  belt for exactly the `deadline == None` case — `SolverConfig::default()` has
  `timeout: None`, and `wasm32`), the shared `lra_online::Dpll` had **no**
  step-budget belt. With no timeout its termination rested solely on the
  structural argument (finite atom set ⇒ finite propagation fixpoint ⇒ CDCL
  over a finite variable set terminates). That argument holds for the concrete
  `LiaTheory` / `LraTheory` deciders, but the driver is generic over
  `T: TheorySolver` (any adversarial theory could be plugged in), and the
  default `SolverConfig` runs it with `deadline == None`. This ADR closes that
  gap: `lra_online::Dpll::solve_with_deadline` now carries the identical
  `DEFAULT_STEP_BUDGET = 16_000_000` belt, checked at the loop head, degrading
  to a graceful decline (`None` ⇒ `Unknown` upstream) on exhaustion — **sound
  (never a wrong `sat`/`unsat`) and additive** (16M main-loop iterations is
  unreachable for any in-corpus instance, so no real query is turned into
  `Unknown`). Both online CDCL(T) drivers now carry the same termination
  guarantee.

- **Regression coverage.** A new `step_budget_termination_tests` module in
  `lra_online.rs` pins the belt with **no deadline**: (a) the default budget
  decides a hard `PHP(5,4)` instance UNSAT (the additivity anchor — the belt
  never trips on a real query); (b) a tiny budget forces a graceful decline
  attributed to the step budget (the livelock belt fires, never a hang, never a
  verdict); (c) a sound theory with hostile varying-shape conflict cores
  terminates with the correct verdict inside the default budget.

## Decision

**The arithmetic online CDCL(T) routes (`QF_UFLIA` / `QF_UFLRA`) are default-on
at the front door — this ADR ratifies the landed first-route ordering — now
that both drivers carry the same termination guarantee.**

- **`QF_UFLIA` / `QF_UFLRA` (default-on, ratified).** The online EUF +
  linear-arithmetic combination is tried first in `dispatch_uf_fast_paths`,
  ahead of eager Ackermann. It is additive (arena-clone probe, budget-split,
  fall-through on `unknown`), soundness-gated (`sat` replayed, `unsat`
  verify-guarded), deadline-polled, and now step-budget-belted. Measured:
  DISAGREE = 0 and `model_replay_failures = 0` on the committed `QF_UFLIA` /
  `QF_UF` slices; the online route decides the disjunctive / Boolean-structured
  mixed-theory class the eager route cannot.

- **`QF_UF` status:** this ADR did not decide the pure-EUF route. The later
  2026-07-09 update to ADR-0055 records that its criterion (2) fired: production
  QF_UF online solving now uses the generic replay-checked `CdclT` route at the
  existing `euf-online` front-door position, with offline `check_qf_uf` retained
  as fallback after an online `unknown`.

- **Out of scope (future Gap-3 work).** Porting arrays-lazy onto the spine with
  real theory propagation (Gap 3 step 2, [P2.2](../../plan/track-2-theories/P2.2-arrays-lazy.md))
  and migrating the arithmetic theories fully onto the generic `CdclT` spine
  (#35, shelved) are **not** decided here. They ride on this ADR proving the
  spine's default dispatch is sound and terminating — which it now does.

## Evidence

- **Dispatch position:** `auto.rs::dispatch_uf_fast_paths` runs
  `dispatch_uf_arith_online` before `check_with_uf_arithmetic`, gated only on
  features; `uf_arith_dispatch_differential` is the additivity gate.
- **Termination:** the deadline is polled at the `Dpll::solve_with_deadline`
  loop head + every propagation fixpoint; the new `DEFAULT_STEP_BUDGET` belt
  closes the `deadline == None` case; `step_budget_termination_tests` pins it.
- **Re-measure (2026-07-07, `--backend solver --compare-z3 --timeout-ms
  10000`), DISAGREE = 0 and `model_replay_failures = 0` on every slice:**
  - `QF_UFLIA/cvc5-regress-clean-bounded`: 4 sat / 2 unsat / 0 unknown (6/6
    decided) — unchanged from baseline.
  - `QF_UFLIA/cvc5-regress-clean-overbound`: 2 instances that straddle the 10s
    wall (both decide `unsat` at 30s in ~13s each) — timeout-boundary, not a
    capability change; the additive belt is never hit.
  - `QF_UF/cvc5-regress-clean-bounded`: 30 sat / 19 unsat / 9 unknown (49/58
    decided) — a net gain over the older baseline from unrelated landed work,
    still DISAGREE = 0.
  - `QF_UF/cvc5-regress-clean-overbound`: 1 sat / 3 unsat / 2 unknown —
    unchanged from baseline.
  - `QF_UFLRA`: no curated corpus slice present to re-measure; the
    `qf_uflra_differential_fuzz` (vs. Z3) carries the DISAGREE = 0 evidence for
    the real route.
- **Soundness gates:** the arith-route differential fuzzes vs. Z3
  (`uflia_differential_fuzz`, `qf_uflra_differential_fuzz`,
  `qf_uf_differential_fuzz`, `uf_arith_dispatch_differential`,
  `qf_lra_differential_fuzz`) at DISAGREE = 0; the full `--lib` sweep,
  `progress_frontier`, and `corpus_regression` green.

## Alternatives

- **Leave the step-budget belt out (rely on structural termination).**
  Rejected: the default `SolverConfig` runs the driver with `deadline == None`,
  the driver is generic over any `T: TheorySolver`, and the project's standing
  rule treats "bounded but non-polling" as a defect that has cost multi-hour
  sweeps. Matching `CdclT`'s belt is cheap, additive, and closes the asymmetry.
- **Flip `QF_UF` online default-on too.** Rejected here: this arithmetic ADR was
  not the place to change pure-EUF dispatch. ADR-0055 later revisited the pure
  QF_UF criterion after the embedded-DPLL → generic-`CdclT` migration landed.
- **Gate the arith routes behind a user-facing config flag.** Rejected: they
  are already first-route, additive, and soundness-gated; a routing-policy
  surface is a P1.8 (strategy/tactics) concern, not this ADR.
- **Overwrite the committed baselines with this run.** Rejected: the run was
  taken under machine load; committing `QF_UFLIA/overbound` at 0/2 would falsely
  bank a timeout-boundary "regression" (the instances decide with headroom), and
  the `QF_UF` gain is unrelated landed work, not this change. The measurement is
  recorded here; the shared baseline JSONs are left to a dedicated,
  load-controlled re-baseline.

## Consequences

- **Easier:** the arith online CDCL(T) routes' default-first position is now a
  recorded decision, and both online drivers carry the identical termination
  guarantee — the spine is proven sound + terminating for the array-lazy port
  and the eventual arithmetic-theory migration to build on.
- **Harder / cost:** two CDCL(T) drivers (`CdclT` and `lra_online::Dpll`)
  coexist until a future consolidation; the step-budget belt now lives in both
  and must stay in sync.
- **Revisited when:** arrays-lazy lands on the spine (Gap 3 step 2); the
  arithmetic theories migrate onto the generic `CdclT` (#35 unshelved); or a
  dedicated re-baseline banks the `QF_UF` decide-rate movement. The pure-QF_UF
  default-dispatch status is now tracked by ADR-0055's 2026-07-09 update.

## Foundational-DAG / register updates

- Record the arith online CDCL(T) routes (`QF_UFLIA` / `QF_UFLRA`) as
  default-first in `check_auto` dispatch, additive over the eager Ackermann
  fallback, with deadline polling + a `DEFAULT_STEP_BUDGET` termination belt
  matching `CdclT` (ADR-0055).
