# Lane: creal-build-bisect — where the `creal_prelude_builds` time entered

<!-- plan-section: lane-status -->

**Your lane's block (`done`, creal-build-bisect, 2026-08-28).** The regression
in
[`docs/research/11-design-review/2026-08-28-the-band-is-the-regression.md`](../../research/11-design-review/2026-08-28-the-band-is-the-regression.md)
is real and it is **not cumulative**. Three files that landed on 2026-08-27
carry **78% of the whole build**, and the mechanism is **not** the
`CReal.integral` `Definition`-unfold one that `CLAUDE.md` names as the first
suspect.

## 1. Both endpoints, measured by this lane

Prebuilt debug test binary run directly (no cargo flock in the number), the
harness's own `finished in`, `RUST_MIN_STACK` confirmed absent from the
environment, `--exact` filter, **1 test** confirmed each time.

| commit | `creal_prelude_builds` | `rat_prelude_builds` | ratio |
|---|---|---|---|
| `77b71bf10` (2026-08-26) | **12.60 s** | 4.85 s | **2.60** |
| HEAD (`1ec0fcec9` + merge) | **105.51 s** | 5.22 s | **20.21** |

8.4x, corroborating the 12.19 → 108.40 s in the write-up. The *reference*
prelude moved 4.85 → 5.22 s (+7.6%) over the same 370 commits, which is what
ordinary growth looks like.

## 2. Where the time is: three files, eight declarations

Detail moved to [`../notes/218-creal-build-bisect.md`](../notes/218-creal-build-bisect.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | creal-build-bisect | measured both endpoints (12.60 s at `77b71bf10`, 105.51 s at HEAD) and located the regression: `trig_fn` + `cos_sign` + `uniform_convergence`, all added 2026-08-27, are **79.0 s of 101.25 s**; the other 165 `STEPS` entries are 22.2 s combined |
| 2026-08-28 | creal-build-bisect | diagnosed the mechanism as unary-`Nat` reduction, **not** the `Definition` unfold: the hot declarations run 40–120 `unfold_def` attempts per successful δ-unfold (healthy is 1.6–3), 98% of them on `Nat.succ`/`Nat` towers, and cost is uncorrelated with term size (864 nodes / 9.74 s vs 8,174 nodes / 1.49 s) |
| 2026-08-28 | creal-build-bisect | A/B'd ADR-0614's literal numerals: **`CReal.cosWideNonpositive` 9.74 s → 0.12 s (81x)** and the whole build −11%, so the ADR's "measured at zero" (taken before these files landed) no longer describes this tree; the `trig_fn` family is unaffected and needs a proof change instead |
| 2026-08-28 | creal-build-bisect | `scripts/check-creal-prelude-build-ratio.sh` + `artifacts/creal-prelude-build-budget.tsv` + controls: replaces the ungated 94–123 s band with a **load-invariant ratio** against `rat_prelude_builds` (2.02x change in absolute time moves it 0.2%; the regression moves it 7.8x), pinned at 21, self-demonstrating on every run |
