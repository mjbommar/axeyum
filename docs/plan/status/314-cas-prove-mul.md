# Lane: cas-prove-mul — polynomial × polynomial cofactors for the CAS→kernel geometry bridge

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (prove_mul landed with one reconstructed
certificate; kernel-reconstructed 8 → 9; the "8 more geometry certificates"
sizing is CORRECTED to 3 — five of the eight also need the fractional literal
cast, including the one lane 277 named as cheapest)`, cas-prove-mul,
2026-08-29).**

## Step 0: re-measured before building on it

`python3 scripts/validate-facts.py` at lane start:

    2154 facts checked, 0 errors
    cas-certificate: 36 total -- kernel-reconstructed 8, cas-internal 28

Unchanged from `docs/plan/status/277-cas-multivariate.md`. That lane's arity
survey re-verified against `artifacts/geometry-certificates/` and reproduces
exactly (arities 6–19; `varignon` and `thales` vacuous).

`scripts/brief-step0.py` was not run against a kernel-declaration target: this
lane declares no library lemma. Its subject is one `Check.*` theorem built
inside a `#[cfg(test)]` module, which no environment projection carries, and the
Rust helpers it needed (`prove_merge`, `poly_expr`, `int_poly`) were located by
reading the sibling module directly rather than by name search. The
retrieval-hazard rule still applied and paid: **nine helpers were reused from
`cas_geometry_bridge_tests.rs` by widening them to `pub(super)`, not
re-derived** — including `prove_merge`, which `prove_mul` calls at every
insertion point and which would have been the single largest piece of
duplicated work.

## The correction: `prove_mul` unblocks THREE certificates, not eight

Lane 277 sized "geometry, non-constant cofactors" at **8**, and separately
listed `medians-concurrent` as the one blocked on a fractional-literal cast.
Measured per certificate — counting terms whose serialised `coefficient`
denominator is not `1` — the two blockers **overlap on three of the eight**:

Detail moved to [`../notes/314-cas-prove-mul.md`](../notes/314-cas-prove-mul.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `203712454` | step 0 re-measurement: the "8 more geometry certificates" sizing corrected to 3; `parallelogram-diagonals-bisect` needs the fractional cast too |
| 2026-08-29 | `e253e79cd` | `rat_prelude/cas_geometry_mul_bridge_tests.rs` — `prove_mul`: monomials as sorted factor lists, three layers, `one_mul`/`zero_mul` derived |
| 2026-08-29 | `f24f87fa9` | `Check.geometry_rhombus_cofactor_identity` admitted — 9 variables, 4 polynomial cofactors, axiom-free; rewrite directions recovered from the parent module's call sites |
| 2026-08-29 | `4b9d63e9e` | `F:geometry-rhombus-cofactor-identity-kernel-checked` registered; cas-certificate kernel-reconstructed 8 → 9; mutation-verified both halves |
