# Notes: 179-rs-cauchy

Detail moved out of [`../status/179-rs-cauchy.md`](../status/179-rs-cauchy.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Verification run (no source changes, so this is a confirmation, not a
regression check):
- `creal_prelude_builds`: ok, 96.79s (single test, debug).
- `every_creal_declaration_is_checked_and_axiom_free` (`--release`): ok,
  14.92s — confirms environment-derived coverage, not just the hand-written
  inventory list, so this is a real check that the whole `creal` roadmap
  including `riemannSum_cauchy` through `integral_by_parts` is axiom-free.

No `expect(dead_code)` annotations touched (nothing new consumed). No files
in scope (`creal/integral.rs`, `creal/inventory/integral.rs`, `creal.rs`,
`creal/creal_tests.rs`) were edited.
