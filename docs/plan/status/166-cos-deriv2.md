# Lane: cos-deriv2 — the derivative of cosine's partial sums

<!-- plan-section: lane-status -->

**Status: LANDED — the target is admitted.**
`CReal.cosFnWideHasDerivative : HasDerivativeOn cosFnWide (fun x => neg (sinFn
x)) zero (ofRat (Rat.natDivSucc 8 4))` is through
`Kernel::add_declaration`, axiom-free, and **cosine differentiates to minus
sine on `[0, 8/5]`** in this kernel. 2026-08-27.

Detail moved to [`../notes/166-cos-deriv2.md`](../notes/166-cos-deriv2.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | cos-deriv2 | `CReal.cosFnPartialHasDerivative` -- lane 159 step 1: every `n+1`-term partial sum of cosine's series differentiates to minus the `n`-term partial sum of sine's; kernel-accepted, `creal_prelude_builds` 93.18 s green |
| 2026-08-27 | cos-deriv2 | `CReal.expTermSuccScale` + `CReal.cosFnTermDerivCoeff` -- the index-shifted coefficient identity priced at ~70 lines: an `Eq` between two `Rat.normalize`s is ONE `normalize_congr`, where the `<=` between the same two terms (`exp_term_antitone_rat`) is ~130 lines of `Int` cross-multiplication |
| 2026-08-27 | cos-deriv2 | measured: `hasDerivative_pow`'s two Skolem `BoundedOn` functions cost one `d.lam_fv` each -- `trig_fn.rs` already had `pow` uniform continuity at a symbolic exponent, inline and duplicated; `bounded_of_uniformly_continuous` computes the index |
| 2026-08-27 | cos-deriv2 | measured: the `succ n`/`n` index shift does NOT reach `hasDerivative_congr` (`sumRange`'s ι-reduction makes both function sides defeq); it bites at `hasDerivative_uniform_limit`, and the missing fact is one-step antitonicity of `Rat.natDivSucc` in its INDEX at a symbolic numerator -- `natDivSucc_antitone` is numerator-1, `natDivSucc_le_scaled` wants a `(c+1)n+c` index |
| 2026-08-27 | cos-deriv2 | `trig_fn.rs`'s inline `pow_uc` induction extracted to `pow_uc_fn` from two byte-identical copies; 4 more `derivative.rs` helpers promoted to `pub(super)` rather than reproduced |
| 2026-08-27 | cos-deriv2 | `CReal.cosFnWideHasDerivative` -- **the target**: `HasDerivativeOn cosFnWide (fun x => neg (sinFn x)) zero (8/5)`, axiom-free, accepted on the first `add_declaration`; `creal_prelude_builds` 98.76 s green, `every_creal_declaration_is_checked_and_axiom_free` (`--release`) 15.22 s green |
| 2026-08-27 | cos-deriv2 | `CReal.natDivSuccStepLe` -- one-step antitonicity of `Rat.natDivSucc` in its INDEX at a symbolic numerator, the fact `rat_prelude` lacks and every `UniformConvergesOn` re-indexing needs; via `natDivSucc_mul` factoring the index into the numerator-1 factor, no new cross-multiplication. Belongs in `rat_prelude`; parked in `CReal` because that file is another lane's |
| 2026-08-27 | cos-deriv2 | `CReal.uniformConvergesShift` + `CReal.uniformConvergesNeg` -- re-index a uniform-convergence witness by one, and negate one; both leave the rate unchanged |
