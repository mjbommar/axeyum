# Lane: creal-build-bisect — where the `creal_prelude_builds` time entered

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, creal-build-bisect, 2026-08-28).** The regression in
`docs/research/11-design-review/2026-08-28-the-band-is-the-regression.md` is
real, and it is **not** cumulative. Three files that landed on 2026-08-27 carry
**78% of the whole build**.

**Endpoint at HEAD, measured by this lane** (`1ec0fcec9` + merge), prebuilt
debug binary run directly so no cargo flock is in the number, harness's own
`finished in`, `RUST_MIN_STACK` confirmed absent from the environment, filter
`--exact creal::creal_tests::creal_prelude_builds`, **1 test** run:

    105.51 s   (load 2.35 -> 1.40)
    107.12 s   (re-run with per-step timing compiled in; +1.5% instrumentation)

That corroborates the 108.40 s in the write-up.

**Distribution, per `STEPS` entry.** `creal.rs`'s `STEPS` table (194 entries)
is run as a loop by `build_creal_prelude_uncached`, so a temporary
`Instant::now()` around `(step.run)` gives the whole distribution in ONE run —
no 370-commit bisect needed. Sum of steps 101.25 s of the 107.12 s (the
remainder is `build_rat_prelude` plus interning, outside the loop).

| step | s | % |
|---|---|---|
| `trig_fn::declare_sin_fn` | 25.73 | 25.4 |
| `trig_fn::declare_cos_fn_wide` | 10.89 | 10.8 |
| `trig_fn::declare_sin_fn_dominant` | 10.60 | 10.5 |
| `cos_sign::declare_cos_wide_nonpositive` | 10.32 | 10.2 |
| `uniform_convergence::declare_weierstrass_m_test` | 7.92 | 7.8 |
| `trig_fn::declare_cos_fn_wide_progress` | 5.91 | 5.8 |
| `trig_fn::declare_sin_fn_lower_bound` | 4.40 | 4.4 |

Seven steps = **75.8 s (74.8%)**. By module: `trig_fn` 59.24 s / 14 steps,
`cos_sign` 11.46 s / 6, `uniform_convergence` 8.32 s / 9 — **79.0 s, 78%**.
The other **165 steps together are 22.2 s**, and `integral` (46 steps, the
largest family by count) is 4.82 s.

All three files were **added on 2026-08-27**: `uniform_convergence.rs`
(`edb2feb7b`, 05:06), `trig_fn.rs` (`7e0ccc952`, 12:40), `cos_sign.rs`
(`f69c51f3a`, 23:15).

So the framing "plausibly cumulative and ordinary over 370 commits" is
**refuted**. Ordinary growth accounts for 12.19 s -> ~22 s; three files
account for the other ~79 s.

Still open in this commit: whether the `Definition`-unfold mechanism is
implicated in `declare_sin_fn`, the 77b71bf10 endpoint re-measured by this
lane, and the gating proposal.

<!-- plan-section: landed-changes -->

| 2026-08-28 | creal-build-bisect | measured: `creal_prelude_builds` 105.51 s at HEAD; per-`STEPS` distribution shows `trig_fn` + `cos_sign` + `uniform_convergence` (all added 2026-08-27) are 79.0 s of 101.25 s — the regression is three files, not 370 commits |
