# Deadline-bounding the NRA/NIA solve: what works, and the architectural ceiling

Status: **investigation finding** (tasks #84 / #85 / #87). Records how far the
NRA/NIA arithmetic solve can be made to honor `config.timeout`, why the last
residual resists a clean fix, and what that means for the disjunction case-split
lever (#87) it blocks.

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

## The residual, and why it resists a clean fix

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
ADR-worthy, for ~1–2 corpus rows. Deferred.

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
