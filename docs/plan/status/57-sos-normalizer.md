# Lane: agent-sos-normalizer — the SOS route's affine row

<!-- plan-section: lane-status -->

**The `Sos` route stopped attesting and started reconstructing: nine
content-free skeletons and one declined module became ten *bound* ones
(`WIP`, agent-sos-normalizer, 2026-08-18).** Gate line
`python3 scripts/check-lra-hypothesis-binding.py`:

    before  instances=125 | structural=95 | attested=28 | failures=0
    after   instances=135 | structural=95 | attested=19 | failures=0

with `hypotheses` 288 → 298, `mutants_caught` 1210 → 1259, `mutants_accepted`
unchanged at 427, `represented_assertions` 286 → 296.

**The whole gap was one predicate, and it was never mathematical.** A degree-2
SOS certificate's Gram matrix is `(n+1)×(n+1)` over the *homogenized*
`v = [x₀ … x_{n−1}; 1]`, so `p(x) = vᵀMv` and `M = LDLᵀ` gives
`p = Σₖ dₖ·(Σᵢ L[i][k]·vᵢ)²` — in which the last coordinate is the constant `1`.
`SosCertificate::rational_squares` nevertheless declined any column with
`L[n][k] ≠ 0`, and the comment said why: the reconstructor's linear-form builder
could emit variables and nothing else. Every corpus row that needs a constant
term — `Σ xᵢ² + 1 < 0` (k01…k08) and `(x−1)² + (y−2)² + 1 < 0` — fell through to
a `prop._0` wrapper that renders `axiom P; axiom Not P` and says nothing about
the query. `rational_affine_squares` returns the affine entry under the index
`n_vars`; `int_affine_lin_to_rexpr` maps that index to the ring's `one`; the
degree-2 ring normalizer has had `Mono::Const` all along. The kernel still
re-proves `M·p = Σ (M·wₖ)(ℓₖ⁺)²` and declines on a canonical-generator mismatch,
so a wrong index convention would decline rather than fabricate.

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

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | `Sos` reconstruction accepts a **nonzero affine row** in the `LDLᵀ` linear forms (`rational_affine_squares`, `int_affine_lin_to_rexpr`), so `Σ xᵢ² + 1 < 0` and `(x−1)² + (y−2)² + 1 < 0` reconstruct instead of emitting `axiom P; axiom Not P`. The transcription checker's two normalizers learned degree-2 monomials to match, with square/cross discrimination driven to failure six ways. Binding gate `instances=125 → 135`, `attested=28 → 19`, `failures=0`. |
