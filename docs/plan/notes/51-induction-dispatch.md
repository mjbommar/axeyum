# Notes: 51-induction-dispatch

Detail moved out of [`../status/51-induction-dispatch.md`](../status/51-induction-dispatch.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
