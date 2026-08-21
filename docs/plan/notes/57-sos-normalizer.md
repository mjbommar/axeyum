# Notes: 57-sos-normalizer

Detail moved out of [`../status/57-sos-normalizer.md`](../status/57-sos-normalizer.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The measurement the brief handed this lane was right, and its opposite was
also worth checking.** Exactly one corpus file (`nra-neg-square-d01.smt2`,
`x·x < 0`) reached the real reconstructor before this change — confirmed by
dumping all ten. It was *declined* rather than attested, because its module
carries `Real.mul` and the transcription checker's parser was linear. So the
Rust fix alone would have moved nine instances from "verified content-free" to
"not checked at all", which is worse: `attested` is a published honesty number,
not a coverage number.

**So the checker learned degree 2, on both sides, separately.** Atoms are now
keyed by a *monomial* — a sorted tuple of variable names, `MAX_DEGREE = 2` — and
the two normalizers get their own product routines (`_smt_poly_mul`,
`_lean_poly_mul`) rather than sharing one, for the same reason they never shared
a parser: they agree only because both are right. `_bind_monomial` renames
factor by factor over both pairings, so a rendered **square** binds only a query
square (the second factor finds itself already bound elsewhere) and a rendered
**cross term** binds only a query cross term (injectivity refuses two carriers
on one symbol) — the same rule as everywhere else, not a special case. The
fail-closed boundary moved up one degree and did not disappear: degree 3 raises,
so its assertion contributes no atoms.

**Six guard deletions, six kills.** `signature` forgetting monomial shape → 1
test; `_bind_monomial` dropping injectivity → 1; dropping factor consistency
→ 2 (over-determined: it is the linear path's rule too); the `.smt2` normalizer
squaring every product → 4, including the end-to-end square-vs-cross control;
the rendered normalizer dropping a product's constant → 2. The `_rename`
re-sort was the interesting one — it survived the first fixture, because that
fixture's φ happened to be order-preserving, so the control was rewritten until
it forced `x._0 ↦ zz, x._1 ↦ aa` and now dies.

**Nothing moved in the Lean ratchets, and that is itself the finding.**
`lean_crosscheck` reports `theory_families=37 structural_families=40` before and
after: the `prop._0` wrapper carries no structural-attestation banner, so
`LeanModuleContent::of_module_source` already classified it as
*theory-reconstruction* and `gate_module_content` already accepted it. Family 30
read `theory=2` while both its modules said nothing about their queries. The Lean
split cannot see this class of shim; the binding gate is what does.

**Next.** The two remaining SOS-shaped declines are outside the degree-2
certificate entirely (`NraEvenPower`, `x⁴ < 0`), so they are a different
reconstructor, not a wider normalizer. Within this route the next real question
is proof size: `nra-sos-strict-unsat-d01` renders a 2.4 MB module (Lean: 5.0 s,
1.3 GB) because `cert_poly_to_rexpr` expands the coefficient 6 into six copies of
`one` and the additive normalizer is superlinear in generator count. It is inside
the envelope this repository already has (`schedule-deadline` is 5 MB) but it is
the thing that will stop the route scaling.
