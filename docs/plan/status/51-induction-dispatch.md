# Lane: induction-dispatch — ℕ-induction from a built route to a shipped verdict

<!-- plan-section: lane-status -->

**ℕ-induction is in dispatch; the front door now decides 4 of the 12 corpus
instances where it decided 1** (`WIP`, induction-dispatch, 2026-08-17).
`prove_by_nat_induction` had been built, exported, and deliberately kept out of
`solve` because it applied ℕ-induction to goals quantified over all of `Int` and
answered `unsat` for satisfiable sets. `a32280b6a` made a recognised `n >= 0`
guard mandatory; this lane re-measured that fix, attacked it, and wired the route
in as the last rung of the quantified ladder.

Re-measurement of `corpus/regression/uflia_induction` (12 instances): the three
`unguarded_*` rows are declines and the four unique `unsat` decisions survive —
**0 status contradictions, down from 3**. The route decides `guarded_linear_
closed_form`, `guarded_linear_nonneg`, `guarded_monotone_step` and
`guarded_parity_range`; the two nonlinear-step instances (`guarded_sum_gauss`,
`guarded_product_factorial_bound`) still overrun.

**No wrong `unsat` was found, and one crash was.** The new
`tests/nat_induction_adversarial.rs` carries 22 shapes chosen because a plausible
recogniser gets them wrong, each with a hand-derived truth and its witness — a
`<= n 0` guard, `>= 0 n`, `>= n (- 5)`, `>= (+ n 1) 0`, a guard on a *different*
variable, a vacuous `true` guard, a disjunctive guard admitting `-1`, nested
binders, a conclusion carrying its own quantifier, binders shadowing free
symbols, nested and n-ary implications, three multi-goal orderings. Every one
declines, on the route alone and through the front door. The defect that surfaced
was arity, not soundness: `is_nonneg_guard` bound `(args[0], args[1])` before
matching the operator, so a one-argument guard (`(=> (not (= n 5)) …)`, legal
SMT-LIB) panicked — unreachable while the route sat outside dispatch, a
front-door crash the moment it did not.

Both suites are mutation-verified, not assumed live. Restoring the
pre-`a32280b6a` fall-through turns 8 of 22 probes into wrong `unsat` and kills
exactly one test; disabling the dispatch rung kills exactly one test in each of
the two suites that assert it fires, and nothing else.

One thing worth carrying forward: **`corpus_regression` could not have caught
this either way.** That gate calls `check_auto` — the quantifier-*free* dispatch
— while the rung lives in `solve`, so its 152 files / 0 DISAGREE is unchanged and
structurally blind to this change. The `nat_induction_corpus` gate now checks the
front-door column as well as the route's own, because a wrong `unsat` from a
wired rung is a shipped verdict.

**Next.** Two things the measurement names. (1) The nonlinear step obligations:
`2·s(n) = n(n+1)` and `fact(n) ≥ 1` both time out in the step, so the rung stops
exactly where NIA does — that is a NIA task, not an induction task. (2) The
recogniser declines any goal whose *other* assertions include a quantifier it
cannot instantiate, which is why all three multi-goal probes decline; widening
`hypotheses` to carry a universal it cannot instantiate as an assumption rather
than dropping the goal would reach them. Neither is a soundness item.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `8f8c12dce` | ℕ-induction wired into `solve` as the last rung of the quantified ladder (`unknown` → `unsat` only, on `original_assertions` because normalization + skolemization have erased the negated universal by that point). New `tests/nat_induction_adversarial.rs`: 22 adversarial shapes, hand-derived truths, measured on the route and through the front door, 0 violations. Fixed an index-out-of-bounds panic in `is_nonneg_guard` on one-argument guards. `nat_induction_corpus` re-measured (3 contradictions → 0) and its gate widened to the front-door column. Both suites mutation-verified. Blast radius: `--lib` 1159 unchanged, `corpus_regression` 152/0 DISAGREE unchanged, whole crate 285 suites / 3861 tests green, clippy and fmt clean. |
