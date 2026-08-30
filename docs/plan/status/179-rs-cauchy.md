# Lane: rs-cauchy — `riemannSum_cauchy` audit, task already subsumed

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, rs-cauchy, 2026-08-28).** No code changes: the
whole task was already landed on `main` before this lane started, 35 commits
back at `590925680` (`feat(creal): CReal.integral_by_parts`).

Task brief: build `riemannSum_cauchy`, predicted to be the literal
`CReal.Cauchy (fun m => riemannSum F a b m)` member of the family, supplied
by `CReal.cauchy_of_abs_diff_le` (landed today in `creal/ivt.rs` for the IVT
root). That prediction did not hold, but the underlying goal — closing the
`riemannSum` roadmap through `CReal.integral` — is done, by a different,
already-integrated route:

- `CReal.riemannSum_cauchy` (`integral.rs`, `declare_riemann_sum_cauchy`) is
  the **`Within`-bound**, shared-index closeness statement (roadmap step 5),
  explicitly documented as NOT the literal `CReal.Cauchy` shape.
- The literal-Cauchy-*rate* shape needed to build `CReal.integral` is instead
  `CReal.riemannSumDeepCauchyFolded` (`declare_riemann_sum_deep_cauchy_folded`),
  reached via re-indexing (`deep`) rather than via `cauchy_of_abs_diff_le` —
  `cauchy_of_abs_diff_le` is used only in `creal/ivt.rs` (its own consumer),
  never in `integral.rs` (confirmed by grep).
- `CReal.integral` itself (`declare_creal_integral`) is built from
  `regular_of_scaled_cauchy` fed that folded witness, and the whole chapter
  continues past it — `integral_converges`, `integral_const`,
  `integral_witness_independent`, `integral_add`, `integral_le`,
  `integral_scale`, `integral_split` (+ split_arbitrary/split_exact/
  split_scale_invariant/congr_of_uniformly_continuous), `integral_abs_le`,
  `ftc_estimates`, `integral_eq_antideriv_diff`, and
  `integral_by_parts` — all present in `EXPECTED_STEP_ORDER`
  (`creal_tests.rs`) and all axiom-free.

So: **the note that prompted this lane's brief was accurate about the
`cauchy_of_abs_diff_le` lemma existing, but the roadmap it named a gap in had
already been closed by the time this lane read it — by a different technique,
not the one predicted.** This is a precisely-sized negative: nothing was
missing to build, only stale to re-verify.

Detail moved to [`../notes/179-rs-cauchy.md`](../notes/179-rs-cauchy.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | rs-cauchy | no code change — `riemannSum_cauchy`/`CReal.integral` roadmap through `integral_by_parts` confirmed already landed and axiom-free; re-verified `creal_prelude_builds` (96.79s) and environment-derived coverage check (14.92s, `--release`) |
