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
  real theory propagation (Gap 3 step 2,
  [P2.2](../../plan/track-2-theories/P2.2-arrays-lazy.md)) and theory combination
  with BV remain future work. The 2026-07-09 updates below move pure and combined
  linear arithmetic onto the generic spine.

## Update (2026-07-09): pure LIA/LRA default probes use generic `CdclT`

The shared-spine migration now includes the pure arithmetic front doors:

- `check_with_arith_dpll` gives pure `QF_LIA` a bounded first probe through
  `check_qf_lia_online_cdclt`; the established arithmetic-DPLL route receives
  only the remaining timeout after an online `Unknown`.
- `check_with_lra_dpll_within` gives pure `QF_LRA` the full remaining deadline
  through `check_qf_lra_online_cdclt`. A timeout or deterministic resource cap
  is terminal; structural/arithmetic incompleteness still falls through to the
  mixed-theory abstraction/refinement route.
- LRA deadlines now cover atom normalization, every incremental
  Fourier–Motzkin feasibility/propagation/model pass, combined UFLRA
  construction, and per-derived-row elimination polling. Linear real queries no
  longer enter the NRA/CAD cube route first; exact numeric coefficients include
  SMT-LIB's `IntToReal(IntConst(_))` shape.
- Generic LRA admits at most 1,024 distinct theory atoms. This deterministic cap
  avoids the eager per-assert Fourier–Motzkin route's stack/cost cliff and returns
  `ResourceLimit` before theory construction.

Five-second curated A/B measurements, raw and `--preprocess`, preserve every
verdict with zero expected-status disagreements and zero model-replay failures:

- `QF_LIA/cvc5-regress-clean-bounded`: 6 sat / 4 unsat / 1 unknown before and
  after (10/11 decided).
- `QF_LRA/cvc5-regress-clean`: 6 sat / 3 unsat / 2 unknown before and after
  (9/11 decided). The two unknown rows improve from 5.250 s / 11.853 s to
  4.838 s / 5.031 s; their final reasons are the 2,468-atom resource cap and a
  deadline timeout respectively.

Route-pinning tests assert the default wrappers reach the generic drivers;
LIA/LRA differential fuzz, NRA/auto/route-trace regressions, and UFLIA/UFLRA
combination suites preserve the existing soundness gates. This update was a
partial consolidation; the combined-arithmetic migration is recorded below.
Theory combination with BV remains the next P1.6 boundary.

## Update (2026-07-09): combined UFLIA/UFLRA use canonical `CdclT`

The default Boolean-structured `QF_UFLIA` and `QF_UFLRA` routes now drive
`CombinedIncrementalLia` / `CombinedIncremental` through
`crate::cdclt::CdclT`, using the same generic online loop as QF_UF, QF_S, and
the pure arithmetic first probes. The combined theory's atom numbering,
registered interface `eq`/`lt`/`gt` variables, structural clauses,
asserted-only conflict cores, leaf reconstruction, and original-assertion replay
gate are unchanged. Only the owning Boolean driver changed.

The propagation diagnostic entry points now exercise that production route and
read `CdclT`'s propagation counter. The older enumerative combination remains a
conservative fallback when an incremental combined state cannot be built. The
arithmetic-local `lra_online::Dpll` remains for standalone arithmetic fallback
paths and test-only learned-lemma diagnostics; it no longer owns the production
combined routes.

Verification and measurement:

- UFLIA online integration: 31/31; UFLRA online integration: 21/21, including
  production-path theory-propagation fire checks and Boolean differential cases.
- Z3 differential fuzz: UFLIA 2,500 cases and UFLRA 1,500 cases, zero
  disagreements. The online-first vs eager-Ackermann dispatch differential is
  also clean.
- Five-second curated UFLIA: bounded remains 4 sat / 2 unsat / 0 unknown,
  `DISAGREE=0`, replay failures 0; overbound remains two timeout unknowns. The
  two-file regression slice remains 1 sat / 1 unsat.

This is routing consolidation, not the end of driver modernization. The first
canonical-driver heuristic slices are recorded below; LBD-based learned-clause
reduction remains to migrate before the arithmetic-local engine can be retired.

## Update (2026-07-09): canonical `CdclT` gains VSIDS and phase saving

Canonical `CdclT` now uses the same deterministic conflict-side VSIDS and phase
saving policy as the arithmetic-local driver:

- 1-UIP analysis bumps each variable when it first enters the conflict side;
  the bump increment decays once per analyzed Boolean or theory conflict and
  rescales all activities uniformly before floating-point overflow.
- Decisions choose the highest-activity unassigned variable, breaking ties by
  the lowest variable index. Every assignment records its polarity, and a later
  re-decision reuses that saved phase; untouched variables preserve the previous
  true-first default.
- Learned clauses, theory cores/reasons, backjump levels, step/deadline budgets,
  and model/evidence replay are unchanged. This is a deterministic search-order
  change, not a new trust surface.

Direct mechanism tests pin conflict-variable bumps, non-uniform decision
reordering, deterministic ties/repeated runs, and phase persistence across
backtracking. The existing adversarial non-monotone-theory sweep still decides
20,000/20,000 cases within the belt and agrees with brute force. Adapter and
oracle gates remain clean: QF_UF, QF_S, pure LIA/LRA, UFLIA, and UFLRA focused
suites pass; Z3 differentials cover 3,000+ QF_UF, 1,500 QF_S, 2,500 UFLIA, and
1,500 UFLRA cases with zero disagreements. The long UFLIA oracle sweep is
runtime-neutral (426.17 s before, 426.19 s after). Five-second UFLIA corpus
results remain bounded 6/6 and overbound 0/2 timeout, with no disagreements or
replay failures. No performance win is claimed from this first mechanism slice.

## Update (2026-07-09): canonical `CdclT` gains Luby restarts

Canonical `CdclT` now uses the same deterministic reluctant-doubling Luby
schedule as the arithmetic-local and proof-producing CDCL engines. After each
analyzed Boolean or theory conflict, the interval counter advances. Once
`luby(restart_index) * 100` conflicts have accumulated above level zero, the
driver backjumps through its existing lockstep theory-pop path to level zero,
retains every learned clause, VSIDS activity, and saved phase, resets only the
interval counter, and advances the restart index. Deadline and no-deadline step
budgets remain authoritative.

The restart mechanism gate lowers the unit on a conflict-heavy pigeonhole
instance and proves: a restart actually fires, the verdict matches a
never-restart baseline, the theory push/pop depth returns to zero, and repeated
runs have the same restart trajectory. The first 15 Luby values are pinned.
The 20,000-run adversarial theory sweep and all current theory adapters remain
green. Z3 differentials again cover QF_UF, QF_S, UFLIA, and UFLRA with zero
disagreements; the long UFLIA run stays neutral (426.19 s before, 425.18 s
after). Five-second UFLIA remains bounded 6/6 and overbound 0/2 timeout with no
replay failures. This is a mechanism landing, not a claimed performance win.

## Update (2026-07-09): canonical `CdclT` gains LBD clause reduction

Canonical `CdclT` now carries aligned learned-clause metadata and deterministic
database reduction. Each learned 1-UIP clause records its literal-block distance
(the number of distinct decision levels), a monotone recency stamp, and a stable
tombstone slot. The first reduction is triggered above 2,000 live learned
clauses; the budget grows additively by 300 after each reduction. Original
clauses, LBD <= 2 glue clauses, and every clause currently recorded as an active
trail reason are permanent. The latter check follows reason ids directly because
this whole-clause scanner does not maintain a distinguished watched-literal
position.

Eligible clauses are totally ordered worst-first by descending LBD, oldest
recency, then newest stable slot; the worst half are tombstoned. Propagation
skips tombstones and clause slots are never reused. Deletion cannot change a
verdict: every candidate is a redundant learned resolvent already entailed by
the original Boolean clauses plus theory lemmas, while originals and all active
implication reasons remain present.

A forced-reduction PHP(7,6) test proves that reduction fires, tombstones learned
clauses, preserves the UNSAT verdict against a never-delete baseline, leaves no
deleted active reason, and repeats the same trajectory. A direct policy test
protects glue and a locked clause whose current implied literal is deliberately
not its first slot. All eight canonical-driver mechanism/adversarial tests and
the EUF, string, UFLIA, and UFLRA adapter suites pass. Z3 differentials for QF_UF,
QF_S, UFLIA, and UFLRA remain at zero disagreements; the 2,500-case UFLIA sweep
is runtime-neutral (425.18 s before, 425.90 s after). Five-second UFLIA corpus
results remain bounded 6/6 and overbound 0/2 timeout, with zero disagreements
and replay failures. No performance win is claimed.

This completes the planned canonical search-feature migration of deterministic
VSIDS, phase saving, Luby restarts, and LBD reduction. It does not make the two
drivers identical or retire `lra_online::Dpll`, which remains on standalone
fallback and diagnostic paths; P1.6 BV/array combination is the next shared-spine
boundary.

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
- **Harder / cost:** two CDCL(T) implementations (`CdclT` and
  `lra_online::Dpll`) still coexist for standalone fallback/diagnostic paths;
  their termination belts and any remaining driver-specific policies must stay
  coherent until the arithmetic-local implementation is fully absorbed.
- **Revisited when:** arrays-lazy lands on the spine (Gap 3 step 2); BV theory
  combination reaches canonical `CdclT`; or a dedicated re-baseline banks the
  `QF_UF` decide-rate movement.
  The pure-QF_UF default-dispatch status is now tracked by ADR-0055's 2026-07-09
  update.

## Foundational-DAG / register updates

- Record the arith online CDCL(T) routes (`QF_UFLIA` / `QF_UFLRA`) as
  default-first in `check_auto` dispatch, additive over the eager Ackermann
  fallback, with deadline polling + a `DEFAULT_STEP_BUDGET` termination belt
  matching `CdclT` (ADR-0055). Their Boolean-structured combined theories now
  implement the canonical `CdclT` path directly; direct conjunctive combination
  remains the model/replay oracle and conservative fallback. Canonical search
  now includes deterministic VSIDS, phase saving, Luby restarts, and LBD-based
  learned-clause reduction with stable tombstones and glue/active-reason
  protection.
