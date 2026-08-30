# Notes: 141-cas-mvt

Detail moved out of [`../status/141-cas-mvt.md`](../status/141-cas-mvt.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The interesting mutation case** (per the task brief): `p = x^3 - 4x^2` on
`[0,4]` has `p(0) = p(4) = 0` so `m = 0`, and `p'(x) = x(3x-8)` has roots at
`x = 0` (the LEFT ENDPOINT itself) **and** `x = 8/3` (genuinely interior).
Both satisfy `p'(x) = m` exactly — so a checker that only tested the slope
equation would wrongly accept `c = 0` as an MVT witness.
`verify_rejects_an_endpoint_witness` confirms the coincidence holds (the
slope-equation check alone would pass) and confirms the strict-interiority
check is what actually rejects it.

18 tests (all passing): 3 correctness spot-checks (`x^2` on `[0,2]` → `m=2,
c=1` exact; `x^3` on `[0,3]` → `m=9, c=√3` — irrational, named exactly, not
approximated; `x` on `[0,1]` → the `g'≡0` degenerate branch), 4 more
degenerate cases (constant `p`, zero polynomial, `a==b` declines, `a>b`
declines), 1 high-degree probe that must not panic, 8 mutation tests
(corrupted poly coefficient / slope / `g` / `deriv_g`, swapped witness,
corrupted bracket, the endpoint-witness case above, plus the unmutated
control), and 2 cost-curve tests.

**Cost, measured (debug build):** degree 2 ~2ms, degree 3 (irrational
witness) ~5ms, degree 5 with a degree-4 algebraic witness ~27ms —
`cost_curve_by_degree`. **Cost is NOT simply inherited from `extremum.rs`
unchanged**, and an earlier draft of the module doc claimed it was before
measuring: subtracting a nonzero secant slope from `p'` generally destroys
whatever factorization made the *original* polynomial's derivative cheap to
isolate. `cost_curve_where_it_hurts_thick_degree_5_declines_soundly` reuses
`crate::extremum::tests::cost_curve_by_degree`'s own cheap all-rational
degree-5 case verbatim; on `[-2,2]` (nonzero secant slope) MVT instead needs
a root of an irreducible quartic with none of the original's structure, and
declines soundly (never a wrong witness or a panic) in 2-4s hitting the
resultant dimension cap.

No panics found in anything called from this module under adversarial/
mutated input. `crate::algebraic::test_support::make_unchecked` (already
`cfg(test)`-gated for `extremum.rs`'s own mutation tests) is reused for the
swapped-witness and corrupted-bracket fixtures.

`docs/research/10-cas/decidability-map.md` updated: a new MVT
polynomial-fragment row in the per-capability contract table (right after
EVT's), and the "Algebraic numbers" zero-testing row's witness list now
names `mvt::polynomial_mvt`/`verify_mvt_certificate` alongside
`polynomial_ivt` and `polynomial_extremum`.

Full crate gate: `cargo test -p axeyum-cas --lib` — 770 passed, 0 failed, 5
ignored (752 baseline + 18 new); `cargo test -p axeyum-cas` doctests — 152
passed. `cargo clippy -p axeyum-cas --all-targets --all-features -- -D
warnings` — clean (one `clippy::option_option` finding fixed by naming a
3-variant `WitnessSearch` enum instead of `Option<Option<AlgebraicReal>>`).

Next for this row-3 family: a kernel-reconstruction slice (ADR-0601 §2)
turning `MvtCertificate` into a checked Lean-kernel term, coordinated by
certificate SHAPE with whichever lane lands `polynomial_extremum`'s and
`polynomial_ivt`'s reconstructions — not by editing
`axeyum-lean-kernel/` from this lane. Also: `docs/curriculum/
graded-statement-families.md`'s MVT row 3 text ("Reachable, not built")
is now stale and should be updated by whoever owns that file next.
