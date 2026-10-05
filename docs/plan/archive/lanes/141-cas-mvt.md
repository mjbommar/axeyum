# Lane: cas-mvt — exact polynomial MEAN VALUE THEOREM (ADR-0603 row 3, MVT)

<!-- plan-section: lane-status -->

**Landed (`WIP`, cas-mvt, 2026-08-27).** Added `crates/axeyum-cas/src/mvt.rs`:
`polynomial_mvt` / `verify_mvt_certificate`, the exact polynomial-fragment
Mean Value Theorem — ADR-0603 row 3, the "cheapest remaining closure" named
in `docs/curriculum/graded-statement-families.md`'s MVT family (row 3 there
still reads "reachable, not built" as of this writing; out of this lane's
declared scope to edit, flagged for whoever owns that file next).

**Existence argument (the mathematical content, not hand-waved):** form the
Rolle reduction `g(x) := p(x) − p(a) − m(x−a)` where `m` is the exact secant
slope. `g(a) = g(b) = 0` by construction (checked, not assumed, by the
verifier). For `deg(p) >= 2`, `g` cannot be identically zero on `[a,b]`
(that would force `p` to be affine), so either `max(g) > 0` or `min(g) < 0`
— and since both endpoints are always `0`, whichever extremum is nonzero
must sit at an **interior** critical point by Fermat's theorem. The producer
calls `crate::extremum::polynomial_extremum` on `g` (and, if that ties at
the endpoints, on `−g`) to locate it — reusing EVT's own certified
completeness argument rather than re-deriving root isolation from scratch.
`deg(p) <= 1` (`p` constant or linear) makes `g' ≡ 0` identically; every
point of `(a,b)` is a witness and the midpoint is named via
`crate::algebraic::real_roots` on its own degree-1 defining polynomial (no
hand-built unchecked bracket).

**Certificate** mirrors `IvtCertificate`/`ExtremumCertificate`: `poly`, `a`,
`b`, `slope`, `g` and `deriv_g` (both carried explicitly as exact-identity
witnesses), and the named witness `c: AlgebraicReal`. `verify_mvt_certificate`
independently re-derives every part — recomputes the secant slope, recomputes
`g`/`g'` from `poly`/`a`/`slope` alone and compares, re-checks `c`'s bracket
isolates exactly one root of its own minimal polynomial (Sturm recount, never
trusting the stored bracket), re-checks strict interiority, re-checks `c` is
a genuine root of the recomputed `g'` by exact evaluation
(`eval_poly_at_algebraic`), and re-checks the stated conclusion `p'(c) = m`
directly from `poly` alone.

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

<!-- plan-section: landed-changes -->

| 2026-08-27 | `4724bc38a` | feat(cas): polynomial_mvt -- exact Mean Value Theorem on the decidable fragment |
| 2026-08-27 | `85b0af141` | fix(cas): mvt fixes -- clippy option_option, two failing tests, measured cost curve |
