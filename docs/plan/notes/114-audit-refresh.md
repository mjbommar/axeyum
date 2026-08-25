# Notes: 114-audit-refresh

Detail moved out of [`../status/114-audit-refresh.md`](../status/114-audit-refresh.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**A directory-backed audit row silently drops an instance it fails to decide.**
That is how those two went missing while the row reported `timeouts 0`: the
directory branch `continue`s past an undecided instance and leaves no record, so
numerator and denominator shrink together. Only the two synthetic rows take that
branch; the instances-array branch records the row instead. Not fixed here.

**The audit's `lean_error` is the fallback route's message, not the fragment's
reason.** All six QF_NRA gap rows classify as `Lra`, so the facade falls through
to the generic LRA route and records *its* complaint (`QF_LRA: nonlinear real
multiplication`). Calling the fragment entry points directly gives the real
answer, and the three that matter split two ways: `simple-mono-unsat` and
`subs0-unsat-confirm` are **principled declines** — their bound / zeroing case is
only *entailed*, by `(or …)`, and minting it would put a proposition in the Lean
module no assertion states; closing them needs kernel case analysis, not a
looser mint. `mult.01` is **unimplemented and scoped**: the `Exactly` bound
refuting `M != k` needs the upper bounds and an equality transport. The three
`real-handelman-unsat` rows have no reconstruction at all and are the largest
single QF_NRA item left. Per-instance table is in the gap analysis.

Next on this axis: the three Handelman reconstructions; the `Or.rec` case
analysis that would close the two principled declines; and the dir-branch drop,
which makes a synthetic row's denominator depend on what the audit could decide
that day.
