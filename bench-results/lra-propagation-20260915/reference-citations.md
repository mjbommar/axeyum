# ADR-2122 — reference citations for bound propagation, verified line by line

Read from the gitignored clones under `references/` (repopulate with
`scripts/fetch-references.sh`). Every line range below was re-printed with
`sed -n 'A,Bp'` before being written down.

- **z3** `e18d63bda04fcab8240eb55314d567db3e43d540`, committed 2026-09-08.
- **cvc5** `1689f13331f7543801f82d9dcbcaac2f70a26781`, committed 2026-09-03.

## Corrections to ADR-2111's own citations

ADR-2111 §4 claim 2 is the design claim this lane builds on. Three of its
citations are wrong, and the third is wrong in a way that changes what a
successor would build.

1. **`try_add_bound` does not exist in z3.** `grep -rn "try_add_bound" src/`
   returns nothing. The entry point is
   `lp_bound_propagator::add_bound`, `src/math/lp/lp_bound_propagator.h:150-190`.
2. **`bound_analyzer_on_row.h:54-80` is the wrong range** — it truncates
   `analyze()` mid-body. The correct ranges are `:55-60` for `analyze_row` and
   `:64-87` for `analyze()`.
3. **"`bound_analyzer_on_row::analyze_row` yields at most two implied bounds per
   row" is FALSE.** `analyze()` returns at most 2, but that counts propagation
   DIRECTIONS (row-max and row-min), not bounds. When every column in the row
   carries the relevant bound — the common case —
   `limit_all_monoids_from_below` (`:196-220`) and `..._from_above` (`:149-172`)
   each call `limit_j` **once per row entry**, so a row of length *n* can emit
   up to **2n** `add_bound` calls. Only the singleton-unbounded paths
   (`limit_monoid_u_from_below` `:223-249`, `limit_monoid_l_from_above`
   `:252-277`) emit exactly one each. The de-duplication to "at most one lower
   and one upper per COLUMN" happens later, in `add_bound`.

   This matters for a builder: a propagator written to the "two per row" reading
   would derive a small fraction of what z3 derives, and would then be measured
   against z3 and found wanting for a reason that is in the brief rather than in
   the code. This lane's rounds emit one candidate bound per row entry per
   direction, which is z3's actual shape.

4. **`theory_lra.cpp:2841` (`mk_bound_axioms`) and `:2963`
   (`flush_bound_axioms`) are CORRECT.**

## z3 — what the mechanism is

| claim | `file:line` |
|---|---|
| propagator state: `m_improved_lower_bounds` / `m_improved_upper_bounds` map a COLUMN to an index into `m_ibounds`, so at most one pending implied bound per column per side | `src/math/lp/lp_bound_propagator.h:16-32` |
| reset per round | `src/math/lp/lp_bound_propagator.h:117-122` |
| `add_bound` keeps a bound only if strictly tighter than the pending one, or equal-and-strict where the pending one was non-strict | `src/math/lp/lp_bound_propagator.h:150-190` |
| the "is this worth deriving" filter, and it is a question about the SAT core: keep only if some UNASSIGNED arith atom on that variable would be implied | `src/smt/theory_lra.cpp:2422-2437` |
| explanation is a CLOSURE built per derived bound, joining one bound-witness dependency per non-target row entry | `src/math/lp/bound_analyzer_on_row.h:298-321` |
| the closure is held on the `implied_bound` and invoked on demand | `src/math/lp/implied_bound.h:36-40` |
| **the explanation carries NO Farkas coefficients** — flattened to constraint ids, each given a hardcoded `mpq(1)`, with an in-tree TODO saying so | `src/math/lp/lar_solver.h:219-223` |
| per-row analysis: classify each entry, then derive in up to two directions | `src/math/lp/bound_analyzer_on_row.h:64-87` |
| all-bounded direction, one `limit_j` per row entry | `src/math/lp/bound_analyzer_on_row.h:196-220`, `:149-172` |
| strictness: count summands whose delta-rational bound has a nonzero infinitesimal part, minus your own | `src/math/lp/bound_analyzer_on_row.h:113-124`, `:166,169,212` |
| the delta component is LOST crossing into `theory_lra`, and z3 refuses to propagate at all rather than strengthen `x >= r - eps` into `x > r` | `src/smt/theory_lra.cpp:2477-2487` |
| touched-row pass: eq propagation, then implied bounds, then reset | `src/math/lp/lar_solver.h:283-304` |
| the single insertion point, gated on `bound_propagation()` | `src/math/lp/lar_solver.cpp:973-976` |
| rows marked touched on a column bound change | `src/math/lp/lar_solver.cpp:1266-1275`, `:1729-1733` |
| rows marked touched by PIVOTING, when `arith_bprop_on_pivoted_rows` is on | `src/math/lp/lp_core_solver_base_def.h:275-281`; `lar_solver.cpp:209-214,228-230` |
| replay on pop | `src/math/lp/lar_solver.cpp:584-589` |
| the two row-skipping guards, one disjunction | `src/math/lp/lar_solver.h:112-121`, the predicate at `:114` |
| `max_row_length_for_bound_propagation` default **300** | `src/math/lp/lp_settings.h:245` |
| the "big coefficient" skip, unconditional (no option turns it off) | `src/math/lp/lar_solver.cpp:379-384`; "big" = not small-int representable, `src/util/rational.h:84-86` |
| `propagate_bounds_with_lp_solver` is called from `propagate_core()` on the FEASIBLE branch, once per SMT propagation round — **not** from `final_check_eh` | `src/smt/theory_lra.cpp:2311-2328`, body at `:2400-2420`, callback at `:4611-4616` |
| implied bound to SAT literal: match against pre-existing atoms, explanation materialised ONCE for the first assigned literal and reused | `src/smt/theory_lra.cpp:2503-2542` |
| the justification object is `ext_theory_propagation_justification` — antecedent literals plus enode pairs, not a proof; the clause branch is dead (`if (false && ...)`) | `src/smt/theory_lra.cpp:2617-2642` |
| **no per-round count cap**; the throttle is a conflict-count threshold plus `m_unassigned_bounds[v] == 0` | `src/smt/theory_lra.cpp:3408-3410`, `:2387-2393`, `:2499-2502`; defaults `src/params/theory_arith_params.h:35-39,61,85` |
| bound ORDERING axioms as SAT clauses, against at most FOUR sorted neighbours | `src/smt/theory_lra.cpp:2841-2894`, emission at `:2890-2893`, the clauses at `:2897-2932`, the queue drain at `:2963-3018` |

## cvc5 — the same structure, tighter caps, real Farkas coefficients

| claim | `file:line` |
|---|---|
| `propagate()`, and the fact that `propagateCandidates` is the LEGACY path (`--new-prop` defaults true) | `src/theory/arith/linear/theory_arith_private.cpp:4397-4415` |
| `propagateCandidatesNew` | `:5107-5145` |
| `propagateCandidateRow` dispatches on the row's BOUND COUNT: all bounded → `attemptFull`, one short → `attemptSingleton` | `:5456-5491` |
| `attemptFull` emits one candidate per row entry — the same shape as z3's all-bounded direction | `:5240-5263` |
| `attemptSingleton` | `:5183-5216` |
| the "would this propagation succeed" filter (cvc5's `bound_is_interesting`) | `:5147-5181` |
| candidate set: `d_updatedBounds`, populated at the three `Assert*` tails | `theory_arith_private.h:639-647`; `theory_arith_private.cpp:636`, `:805`, `:916` |
| converted to rows once per round and drained destructively | `:5493-5518`, `:5124-5144` |
| **explanations DO carry Farkas coefficients**: index 0 is the implied constraint's, *i+1* is `explain[i]`'s | `src/theory/arith/linear/linear_equality.cpp:593-607,647-674`; collected only under `produceProofs`, `theory_arith_private.cpp:5351-5362` |
| the coefficients become a real proof rule | `ProofRule::MACRO_ARITH_SCALE_SUM_UB`, `theory_arith_private.cpp:5409` |
| two delivery routes by row length: short rows become a CLAUSE, long rows a queued propagation | `:5363-5442` |
| the literal reaches the SAT core through `outputPropagate` | `:4421-4450`, `:2195-2200` |
| `arithPropagationMode` default `BOTH_PROP` | `src/options/arith_options.toml:25-43` |
| `arithPropagateMaxLength` default **16** | `src/options/arith_options.toml:113-119` |
| `arithPropAsLemmaLength` default **8** | `src/options/arith_options.toml:253-259` |
| the length cap is PROBABILISTIC in the new path: a row of length *L > 16* is still attempted with probability *16/L* | `theory_arith_private.cpp:5466-5471` |

## The one axis where the two references are 19x apart

z3 refuses a row above **300** coefficients, hard and unconditionally. cvc5
refuses above **16**, and only probabilistically. That is not a rounding
difference — it is two different bets about whether wide-row propagation pays.
This lane took z3's number, and it is registered in `config_registry` as a
CHOICE with both values beside it rather than as a fact.
