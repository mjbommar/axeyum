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

Detail moved to [`../notes/57-sos-normalizer.md`](../notes/57-sos-normalizer.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | `Sos` reconstruction accepts a **nonzero affine row** in the `LDLᵀ` linear forms (`rational_affine_squares`, `int_affine_lin_to_rexpr`), so `Σ xᵢ² + 1 < 0` and `(x−1)² + (y−2)² + 1 < 0` reconstruct instead of emitting `axiom P; axiom Not P`. The transcription checker's two normalizers learned degree-2 monomials to match, with square/cross discrimination driven to failure six ways. Binding gate `instances=125 → 135`, `attested=28 → 19`, `failures=0`. |
