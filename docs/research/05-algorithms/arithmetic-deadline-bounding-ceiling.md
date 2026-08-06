# Deadline-bounding the NRA/NIA solve: what works, and the architectural ceiling

Status: **resolved deadline/resource slice** (tasks #84 / #85; ADR-0377), with
the separate disjunction case-split lever (#87) still requiring remeasurement.

## 2026-08-05 resolution

The earlier diagnosis below correctly found missed polls, but incorrectly
localized the remaining `ext-rew` cost in foundational `axeyum-ir` polynomial
primitives. Stage timing on current main found two independent causes:

1. `check_auto_dispatch` created an absolute deadline for feature scanning but
   then passed the original timeout to sequential arithmetic routes. On the
   public `ext-rew-aggr-test`, real relaxation declined after roughly 0.64 s and
   `nia_linearize` then consumed another fresh roughly 1.00 s. This timeout reset
   was the dominant top-level overrun.
2. The exact multivariate real-root path did have a smaller solver-local polling
   gap inside `MultiPoly` arithmetic, exact division, determinant expansion,
   projection, and rational-cell traversal. Those operations are in
   `axeyum-solver`, not `axeyum-ir`, so the existing thread-local deadline can be
   polled without a cross-crate callback or foundational API change.

ADR-0377 therefore makes the dispatch deadline query-global, recomputes the
remaining duration before every sequential real/NIA route, and adds inner CAD
polls. Optimized 8 GiB-wrapped timings for the exact public row changed as
follows:

| requested budget | before | after |
|---:|---:|---:|
| 250 ms | 1.10 s | 0.30 s |
| 500 ms | 1.60 s | 0.60 s |
| 1 s | 2.10 s | 1.10 s |
| 3 s | 4.11 s | 3.10 s |

The remaining approximately 0.10 s is process/wrapper and bounded cleanup
overhead, not another fresh solver budget. A committed debug regression requires
the 250 ms request to return in under 1 s and to report
`Unknown(Timeout)`; it currently completes in 0.28 s.

The same slice also closes the independent QF_LRA abort class. `AtomBuilder`
previously retained every intermediate dense `LinExpr`; nested sums could retain
quadratic coefficient maps and the 1,492-atom `sc-39.base.cvc.smt2` experiment
aborted at 8 GiB when the front-door cap was raised. LRA construction now counts
normalization nodes, coefficient work, and cached coefficient entries under
deterministic ceilings and returns `Unknown(ResourceLimit)` on exhaustion. The
existing 1,024-atom front-door cap remains; the new defense protects direct and
sibling constructors rather than just that one dispatcher.

The sections below are retained as historical evidence for the earlier partial
fix and its dead-end probes. Their claim that a foundational callback was
required is superseded by the measured resolution above.

## The problem

A large lazy-SMT cube routed through the real-polynomial decision
(`decide_real_poly_constraint` → `decide_system` / `decompose_multivariate`, in
`crates/axeyum-solver/src/nra_real_root.rs`) ran many seconds past
`config.timeout` with no interception point — `ext-rew-aggr-test` took ~16s under
a 3s budget. This is a hang/OOM risk (the box OOMs on unbounded NIA blowups), and
it separately blocks any per-branch case-split: a branch given a small sub-budget
overruns it (so the disjunction case-split #87 made `rewriting-sums` take 33s at a
20s budget and was reverted).

## What was landed (the clean ceiling)

Two mechanisms honor the deadline for the bulk of the cost:

1. **`config.timeout` threaded through the decision loops** (#84): per-atom /
   per-sample polls in `decide_system`, the `dpll_t` round-budget, and the
   `sort_roots` O(n²) comparator.
2. **A thread-local `ISOLATE_DEADLINE`** (#85, `nra_real_root.rs`): set by an RAII
   guard at `decide_real_poly_constraint`'s entry (so the ~20 `isolate_roots`
   call sites need no signature change), polled at the isolation and multivariate
   CAD **entry points** — `isolate_roots`, `isolate_roots_sturm` (before the
   O(deg²) Sturm-chain build), `sturm_isolate_rec` (each recursive subdivision),
   and `decompose_multivariate` / `strict_cad_along` / `project_strict` /
   `resultant_univariate`.

A fired poll only turns a would-be-slow computation into `None` ⇒ the caller
declines to the sound grid fallback / `unknown` — **soundness-neutral**, never a
changed verdict (verified: `nra_differential_fuzz` DISAGREE=0, frontier 8/8,
corpus_regression, `--lib` all green). Effect: `ext-rew` 16.2s → 9.6s @ 3s,
`nl-eq-infer` now honors its budget.

## Historical residual diagnosis (superseded)

`ext-rew` still overruns (~9.6s @ 3s) and `rewriting-sums` (~6.4s @ 3s). The
remaining cost is a **single fixed-cost computation *inside* a function**, not at
an entry an `ISOLATE_DEADLINE`-poll can guard. Two dead ends were ruled out by
measurement:

- **It is not `sylvester_determinant`.** That primitive is already the fast
  Bareiss-interpolation form (O(num_points·n³), not O(n!)). Adding a
  cancellation-callback poll to its interpolation loop (a wasm-safe
  `&dyn Fn() -> bool`, since `axeyum-ir` has no `std::time` access) gave **zero**
  measured improvement to `ext-rew` — reverted under measure-don't-seed.
- **A `std::time::Instant` deadline cannot be threaded into `axeyum-ir`.** The
  hot inner computations live in the foundational, **wasm-buildable** `axeyum-ir`
  `poly` primitives, which deliberately have no clock access. The only cross-crate
  options are (a) a cancellation-**callback** param on each hot primitive
  (mechanically invasive across the poly API, and the one probe above showed no
  benefit at the tried site), or (b) a hard degree/coefficient cap (which would
  **regress completeness** — declining large-degree cases that decide in-budget).

So the clean, soundness-neutral, non-regressing ceiling is the entry-poll set
above. Closing the last residual means *profiling to the exact inner loop* (in
`axeyum-ir` polynomial arithmetic or the NIA relaxation for `rewriting-sums`) and
threading a callback there — a cross-crate change to a foundational crate,
ADR-worthy.

**Measured ROI (2026-07-08, post-#88, re-measured over all four curated arith
corpora — corrects the earlier "~1–2 rows" estimate).** The initial re-measure
showed **7** "preprocessed dispatch timeout after reduced solve" rows at a 5 s
budget, but they are NOT one class — classifying each by shape split them into
distinct causes, and **4 of the 7 were a fixable dispatch bug, now closed**:

- **FIXED — bounded nonlinear SAT (4 rows, `synthetic/QF_NIA/nia-pythagorean-m05..08`,
  `x²+y²=z², 1≤·≤25`).** These are fully *bounded* boxes the exact int-blast owns,
  but the nonlinear-multiplier blast (step 8 of `decide_bounded_int_blast`) burned
  the whole budget and starved the trusted exhaustive-enum fallback (step 9), and
  even when a verdict was reached `dispatch_reduced` discarded it at its
  `past_deadline` gates. Fix (`auto.rs`): give the blast HALF the budget when the
  box is exhaustively enumerable (reserving the rest for the exact enum), and stop
  `dispatch_reduced` discarding an *already-decided, replay-checked* verdict (the
  deadline bounds SEARCH, not the bounded O(term-size) reconstruct+replay). Result:
  synthetic QF_NIA 32/32, sat 12→16, unknown 4→0, DISAGREE = 0, PAR-2 1.256→0.709;
  `frontier_nia_unsat` held (the 10⁴ pre-blast cap — which the fix deliberately
  does NOT touch — still guards the `nia_unsat` family). This was a dispatch bug,
  NOT the poly hot-loop below.
- **STILL OPEN — genuine poly hot-loop (1 row): `ext-rew-aggr-test`** (12.2 s, sat,
  105-line nonlinear conjunction, no disjunctions) — the true #85 residual: cost in
  the `axeyum-ir` poly primitives, needs the profile-to-inner-loop + callback above.
- **STILL OPEN — finite-domain disjunction (1 row): `rewriting-sums`** (10.7 s,
  unsat) — a #87 target, not a poly issue: `(or (= x c)…)` chains pin a finite set
  but the conditional equalities are not propagated into `z²>10⁹`; needs the
  *finite-domain* disjunction split (see #87).
- **STILL OPEN — div/mod-by-zero SAT (1 row): `mod.03`** (5.0 s) — `mod x n < 0`
  is sat only at `n = 0` (SMT-LIB `mod` is ≥ 0 for `n ≠ 0`); the `n = 0` witness
  (unconstrained div/mod-by-0, ADR-0040) is not found in budget. Distinct decider.

The remaining one-offs each need distinct machinery: `learned-rewrite-int-mod-range`
(unsat, bounded int-blast overflows at width 32; needs mod-range / `|n|<|d|`
reasoning), two QF_NRA transcendentals (`sin-cos-*`, `metitarski-1025`),
`nt-lemmas-bad` (QF_NRA unsat), and `issue3003` (QF_NRA — verdict-correct sat whose
algebraic model fails the *public* `eval` replay, task #89). So the "dominant
timeout class" was mostly a dispatch bug; the true poly-hot-loop residual is now a
single row (`ext-rew`), and #87's `rewriting-sums` is a separate finite-domain
lever.

## Consequence for #87 (disjunction case-split)

The disjunction case-split is **sound and implemented** (partition top-level
`(or …)` conjuncts, enumerate the cartesian product ≤ 32 branches, all-unsat ⇒
unsat / any-sat ⇒ sat; `route_trace` 6/6, `--lib` green) but **reverted**: its
per-branch sub-solves inherit the same residual overrun, so `rewriting-sums` (its
target) still exceeds budget and the corpus PAR-2 roughly doubled. #87 is
**purely blocked on fully closing #85's residual** — re-apply it once a branch's
small budget is actually respected.

## Backlinks

- Tasks #84 (landed), #85 (partial landed + this residual), #87 (blocked).
- `nra_real_root.rs` (`ISOLATE_DEADLINE`, the entry polls), `auto.rs`
  (`try_disjunction_split`, reverted), `axeyum-ir/src/poly.rs`
  (`sylvester_determinant`, the ruled-out site).
