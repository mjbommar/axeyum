# Lane: prelude-spike — prelude-build refactor prototype on `complex.rs`

<!-- plan-section: lane-status -->

**Prototype landed and green** (`WIP`, prelude-spike, 2026-08-27). Built the
level-1 phase-order fix and the level-2 topological-order validation from
[2026-08-27-architecture-review.md](../../research/11-design-review/2026-08-27-architecture-review.md)
§1 on `crates/axeyum-lean-kernel/src/complex.rs`, plus a real (not simulated)
Part B module-registry split for `complex/poly.rs`. Full writeup:
[2026-08-27-prelude-build-spike.md](../../research/11-design-review/2026-08-27-prelude-build-spike.md).

Headline: the existing hand-written build order is already a valid
topological order (0 violations across 1,279 extracted dependency edges, now
enforced by a structural preflight + two pinned tests), and splitting one
already-modularized group (`poly`, 21 of 148 fields) out of the shared struct
eliminates its hub footprint entirely — 0 lines touched in `complex.rs` for a
new declaration inside `poly.rs`, down from up to 3. Recommend applying level 1
(dependency table + structural preflight) to `creal.rs` without reservation;
recommend piloting the module-split (level Part B) on ONE already-separate
`creal/*.rs` file before generalizing, given the estimated ~9,000 call-site
churn across the full 441-field struct.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `00797f01d` | Level-1 fix: `STEPS` build-order table + `validate_step_order` structural preflight, replacing the 89-call hand-written sequence in `build_complex_prelude`. `cargo check` clean. |
| 2026-08-27 | `e0984768a` | Part B: real (not simulated) module split for `poly.rs` (21 fields into `poly::PolyNames`, 144 call sites rewritten). Full suite: 48 passed / 0 failed in 441.92s (contended host, load ~11). Write-up with all Part C numbers: `docs/research/11-design-review/2026-08-27-prelude-build-spike.md`. |
