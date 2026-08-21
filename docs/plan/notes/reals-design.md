# Notes: reals-design

Detail moved out of [`../status/reals-design.md`](../status/reals-design.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Next:** R1 is **unblocked**. The ADR's first draft said ℚ had no order — true
of `int_prelude/rat.rs`, false of `rat_prelude.rs`, which `agent-rationals`
landed in the worktree mid-draft with `le`/`lt`/`inv`/`sub`/`div` and all 22
ordered-ring laws. The correction is recorded in the ADR rather than quietly
fixed. The only gap left is `1/(n+1)` (one definition), and writing `|a| ≤ b` as
`−b ≤ a ∧ a ≤ b` removes the `Rat.abs` dependency entirely. So: R1 carrier
(~10 decls), R2 ordered
ring + congruences (~35), R3 the one thing outside the kernel — ADR-0457's
telescope gains an equality slot (`RING_BINDER_NAMES` 30 → 39), R4 the model
witness. ℂ is scoped and **deferred with a finding**: nothing in the solver needs
it, and the only shipped complex arithmetic is exact ℚ(i) in
`axeyum-cas/src/geometry_certify.rs`, which wants a ring over ℚ and not ℝ
underneath — so ℚ(i) before ℂ, if either.
