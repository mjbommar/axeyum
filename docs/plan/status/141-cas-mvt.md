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

Detail moved to [`../notes/141-cas-mvt.md`](../notes/141-cas-mvt.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `4724bc38a` | feat(cas): polynomial_mvt -- exact Mean Value Theorem on the decidable fragment |
| 2026-08-27 | `85b0af141` | fix(cas): mvt fixes -- clippy option_option, two failing tests, measured cost curve |
