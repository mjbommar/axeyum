# Lane: creal-build-bisect — find where `creal_prelude_builds` time entered

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, creal-build-bisect, 2026-08-28).** Investigating the
`creal_prelude_builds` regression recorded in
`docs/research/11-design-review/2026-08-28-the-band-is-the-regression.md`
(12.19 s at `77b71bf10` → 108.40 s at HEAD, 8.9x, over 378 commits).

Method, recorded before any number is: measure with the prebuilt debug test
binary under `target/debug/deps/` (no cargo lock, so the number is work and not
the flock queue), read the harness's own `finished in Xs`, run with
`env -u RUST_MIN_STACK`, and use the colon-qualified filter
`creal::creal_tests::creal_prelude_builds` with the test count confirmed as 1.

The instrumentation point is `creal.rs`'s `STEPS` table (197 `BuildStep`s, added
2026-08-27): `build_creal_prelude_uncached` runs it as a loop, so per-step timing
gives the distribution directly and is far cheaper than bisecting 378 commits.

WIP — no measurements recorded yet in this commit.

<!-- plan-section: landed-changes -->

| 2026-08-28 | creal-build-bisect | opened: method for the `creal_prelude_builds` bisect, no numbers yet |
