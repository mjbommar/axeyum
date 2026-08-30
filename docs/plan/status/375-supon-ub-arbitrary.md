# Lane 375 — `CReal.supOn_ub` at an arbitrary point

<!-- plan-section: lane-status -->

**Status: IN PROGRESS (stub — work not yet started).**

Target: `CReal.supOn_ub` — `∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) x,
le a x → le x b → le (F x) (supOn F a b hab u)` — the one declaration ADR-0710
names as remaining between `CReal.supOn` and comparability with Mathlib's
`IsCompact.exists_isMaxOn`.

Route under test: ADR-0710's four steps. Findings to follow.
