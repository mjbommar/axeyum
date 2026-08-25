# Notes: 115-fp-misc-hang

Detail moved out of [`../status/115-fp-misc-hang.md`](../status/115-fp-misc-hang.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Every cap in that module was on the walk's RESULT.** `MAX_ABSTRACTED_TERMS`,
`MAX_ABSTRACTED_NODES` and the 1 s solve timeout all run after
`build_bv_abstraction` returns, so nothing bounded the walk itself. Memoizing
took `fp_misc` from 4,194,309 visits to 4,365 over 5,762 reachable nodes; the new
visit budget is what makes the memo's guard fail in 0.23 s instead of hanging.
Sixth instance of this bug in this repository, and the second this week — the
2026-08-20 pair (`contains_quantifier`, `lower_derived_bv`) were latent behind
routes nothing reached until `887b52e64` made FP rows decline `BvDefinedEnum`,
which is the same commit that exposed this one.

**Not dominant, and that is the honest answer.** The 2026-07-21 row was dominant
through `bv_defined_enum`, which `887b52e64` deliberately withdrew for FP
arithmetic pending a certified `Fpa2Bv` reduction — pinned by that commit's own
`declines_qf_fp_misc_without_certified_fpa2bv`. `fp_misc` now decides through
bit-blast with an explicit `bit-blast` trust hole. `trust_holes: ["timeout"]`
becoming `["bit-blast"]` is the whole improvement, and restoring dominance means
certifying `Fpa2Bv`, not raising a budget.

**`QF_BVFP/Float-no-simp3-main` is a budget, but not the one that was recorded.**
The standing note said "decision is 4.6 ms but its evidence still exceeds 120 s".
Measured at HEAD, `produce_evidence` returns in 19 ms and nothing times out. The
same `887b52e64` decline removes its certifying route, and what it falls back to
is a bare `unsat` only because `produce_evidence` skips
`reduction_unsat_certificate` **outright** whenever `config.timeout` is set —
which `audit_dominance` and `diagnose_evidence` both always do. Run the same
export unbudgeted and it is `proved` in **28.3 ms**.

I did not loosen that guard, and the measurement says why not: the `deadline` it
would rely on reaches only `solve_with_drat_proof_within`. `lower_terms`,
`tseitin_encode`, `check_drat` and the LRAT elaboration are all unbounded, and
the guard covers 42 bare-`unsat` rows across the committed audits. Landed
instead as a two-test pair asserting opposite outcomes on the same instance, so
neither can pass vacuously and either direction of change breaks one.

Next on this axis, in cost order: thread the deadline through
`export_qf_bv_unsat_proof_impl`'s unbounded phases and then narrow the blanket
budget guard to a real remaining-time attempt (this alone would move
`Float-no-simp3-main` and any other BV-reducible bare `unsat` to certified);
then `Fpa2Bv` certification, which is what both FP rows actually need for
dominance.
