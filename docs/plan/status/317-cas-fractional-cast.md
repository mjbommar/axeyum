# Lane: cas-fractional-cast — the general `Rat.ofRat`-style fractional-literal cast, plus medians-concurrent

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (fractional cast landed; kernel-reconstructed 9 →
10; medians-concurrent reconstructed; centroid-divides-medians and
parallelogram-diagonals-bisect still need prove_mul ON TOP of this cast;
F:cas-partial-fractions-mixed-general-case untouched -- cast-only, next
lane's cheapest target)`, cas-fractional-cast, 2026-08-30).**

## Step 0: re-verified before building

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 37 total -- kernel-reconstructed 9, cas-internal 28

Matches `docs/plan/status/314-cas-prove-mul.md` exactly. Re-verified that
lane's specific correction before starting: `parallelogram-diagonals-bisect`
(lane 277's originally-named "cheapest next target") is genuinely NOT
reachable by the fractional cast alone — every one of its cofactors and both
of its conclusions carry `±1/2`, which is a NON-CONSTANT-cofactor shape
needing `prove_mul` as well. `medians-concurrent` is the one certificate
whose cofactors are constant (`-1`, `-1`) and whose generators are the ones
needing the cast, so it is reachable by the cast alone — confirmed by reading
`artifacts/geometry-certificates/medians-concurrent.json` directly before
writing any Rust.

`scripts/brief-step0.py` was not run against a kernel-declaration target, for
the same reason lane cas-prove-mul's did not: this lane declares no library
lemma, only a `Check.*` theorem inside a `#[cfg(test)]` module.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_frac_bridge_tests.rs`
(new, 3 tests). Two existing helpers widened to `pub(super)` for reuse
(`nat_le_lit` in `cas_ivt_bridge_tests.rs`, `add_left_comm` in
`cas_geometry_bridge_tests.rs`); no existing logic changed.

### The cast

`Rat.normalize n d h` (`rat_prelude/ops.rs`) already existed — it takes an
`Int` numerator, a `Nat` denominator, and a proof `1 <= d`, and reduces to
lowest terms internally. That IS a `Rat.ofRat`-style cast; nothing needed
declaring in the kernel. `rat_lit(d, r: Rational) -> ExprId` is the one-line
builder this bridge lacked:

Detail moved to [`../notes/317-cas-fractional-cast.md`](../notes/317-cas-fractional-cast.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `370a51a64` | draft: `rat_prelude/cas_geometry_frac_bridge_tests.rs` -- `rat_lit` cast, `prove_scale_rat`/`prove_merge_rat`/`prove_const_combination_rat`, medians-concurrent reconstruction (compiles, not yet test-run in that commit) |
| 2026-08-30 | (pending) | tests green (11/11 sweep), mutation-verified both halves through different guards; `F:geometry-medians-cofactor-identity-kernel-checked` registered, `cas-certificate` kernel-reconstructed 9 -> 10 |
