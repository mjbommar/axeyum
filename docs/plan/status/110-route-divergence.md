# Lane: decision/evidence route divergence

<!-- plan-section: lane-status -->

**The decision route and the evidence route agreed again on
`QF_NRA/.../cli__regress0__nl__issue3003.smt2` (`DONE`, agent-route-divergence,
2026-08-20).** `check_auto_explained` said `sat` in 0.9 ms; `produce_evidence`
said `unknown certified=false checked=false`. Both run the same exact real-root
decider, so the decider was never the difference — the evidence route replays
its candidate model through the ground evaluator first (the Hard Rule), and the
replay was failing on a CORRECT model.

`poly_big::combine` reaches an operand's interval only by bisection, and
bisecting toward a *rational* root lands the midpoint exactly on it: the
interval collapses and the code declined. Every rational lifted by
`from_rational` hits that on its first refinement, so `c + α` — here
`1 + (−3/4)`, from the witness `y = −√3/2` — never computed. A collapsed
interval is more information, not less: the operand is exactly that rational, so
`α + c` is a root of `p(x − c)` and `α · c` of `p(x / c)`, isolation carried
over by bijection instead of re-derived inside a resultant's interval. Accepted
under `combine`'s own criterion (opposite endpoint signs, exact Sturm count 1),
so a decline stays a decline.

The instance now reports `sat-model certified=true checked=true`. Worth noting
for the next lane on this axis: nothing else in the tree compares the two routes
on the same query, so a divergence is only visible when someone points
`diagnose_evidence` at a file by hand.

<!-- plan-section: landed-changes -->

| 2026-08-20 | `0797719a7` | Rational operands no longer defeat algebraic field arithmetic; the NRA `sat` witness replays and the evidence route matches the decision route |
