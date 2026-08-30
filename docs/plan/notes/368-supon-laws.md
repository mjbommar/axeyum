# Notes: 368-supon-laws

Detail moved out of [`../status/368-supon-laws.md`](../status/368-supon-laws.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**EVT remains ineligible**, and this lane does not change ADR-0692/0699's
verdict. Trusted base: `creal` stays at 0. Computational content: improved,
not sufficient — Mathlib's `IsCompact.exists_isMaxOn` bounds `F` at every
point of the interval, and so must we before the statements are comparable.

## Measurements

| | before | after |
| --- | --- | --- |
| `creal_prelude_builds` | 109.88 s | 110.80 s |
| `cargo test -p axeyum-lean-kernel --lib creal::` | 199 passed / 399.23 s | 200 passed / 425.32 s |
| `shape_search --const CReal.supOn --kind theorem` | — | 6 (control: `CReal.integral` 18) |

**The canary did not move**: eight declarations cost about a second, inside
the noise. Intermediate readings of 118-127 s were taken under lane
contention and are not the cost of this work -- the harness's own
`finished in` is CPU-contended even though `cargo-serialized.sh` serializes
the cargo jobs themselves. Read the number on a quiet box before attributing
a regression to a declaration.

Five of those six theorem types are new in this lane; `supSeq_converges_supOn`
predates it. ADR-0691's "zero against 45" was a different instrument and the
two are not on the same scale.

## Checks run

- `cargo test -p axeyum-lean-kernel --lib creal_prelude_builds` — 1 passed,
  after every increment.
- `cargo test -p axeyum-lean-kernel --lib every_creal_declaration_is_checked_and_axiom_free`
  — 1 passed. This is the discriminating one: it reads
  `kernel.environment()` rather than a list, so a build step that never ran
  would fail it through the shard entry.
- `cargo test -p axeyum-lean-kernel --lib sup_laws_concrete_and_negative_controls`
  — 1 passed, both negative controls rejected by the kernel.
- `cargo fmt --all --check`, `clippy -D warnings` on this crate — clean.
