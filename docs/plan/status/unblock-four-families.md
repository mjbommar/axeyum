# unblock-four-families

<!-- plan-section: lane-status -->

**Status: COMPLETE (2026-08-31). Four families are available for draw 14; two
independent 4-family layouts clear R5, R9, R11's hard signals and R12 against
the real `guard()`, leaving only R11's authorable disclosure review.**
Authority: [ADR-1100](../../research/09-decisions/adr-1100-four-families-for-draw-14-the-free-supply-all-sorts-early.md).

## What this lane was for

ADR-1095 measured why three draws in a row declined: `_with_cycle` assigns
`held-out` at cycle index `0, 3, 6, …`, so `n` fresh families give
`ceil(n/3)` held-out ones and R5 needs 2 — hence `n >= 4`. It searched the
supply side, found at most 3 constructible, and declined.

## The correction this lane measured

The blocker is **positional**, not a count. Cycle indices 0 and 3 are the
held-out slots, and every family constructible with no new work sorts EARLY
by its first Mathlib module name — `Batteries.Data.Nat.Bisect`,
`Init.Data.Nat.MinMax`, `Mathlib.Data.Int.Fib.Basic`. The free supply fills
index 0 and can never fill index 3. A fourth family with no new work does
exist (`natural-factorization`, an 11-row combination over four number-theory
modules the hygiene screen cannot surface) and R11 refuses it at index 3 on
vocabulary, 9 of 10 rows. So the fourth family had to be BUILT, and had to be
both late-sorting and topically fresh.

## Landed

| change | detail |
| --- | --- |
| `Nat.Abundant` / `Nat.Deficient` | `nat_prelude/abundant_deficient.rs`; opens `Mathlib.NumberTheory.FactorisationProperties`, 15 screened rows, held-out viable at index 3 |
| `Nat.stirlingFirst` / `Nat.stirlingSecond` | `nat_prelude/stirling.rs`; opens `Mathlib.Combinatorics.Enumerative.Stirling`, 16 rows, `train`/`development` only (R12 refuses `stirlingFirst_zero` for held-out) |
| evaluation tests | `abundant_deficient_tests.rs` (5), `stirling_tests.rs` (3); every value hand-computed, every negative control naming the wrong formula it rules out |
| inventory registration | both pairs added to `nat_prelude_tests::definition_names`; the environment-derived coverage assertion failed naming them first, as designed |
| environment snapshot | `kernel-environment-snapshot-v1.json` 2583 -> 2593, from a rebuilt `shape_search --release` |
| ADR-1100 | the measurement, the two verified layouts, and the positional rule the next lane needs |

No theorem about any of the four is declared (ADR-0653). No
`FAMILY_MODULES`/`FAMILY_ROUTES` edit and no `artifacts/autogenesis/` manifest
edit: this lane enables a draw, it does not author one.

## Measured

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **276 passed, 0
  failed** (273 before).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- `check-autogenesis-holdout-isolation.py` — `held_out=146` before and after,
  verdict PASS.
- Real `select()`/`guard()`, post-declaration, unsimulated: both layouts reach
  R11's disclosure step and nothing else. Control (three free families) still
  reproduces ADR-1095's `R5 the refill adds 1 held-out families`.

## Next

A draw lane authors `FAMILY_MODULES`/`FAMILY_ROUTES` for one of the two
layouts, records the two disclosure reviews in
`holdout-adjacency-review-v1.json`, and regenerates
`nursery-v2-extension.json`. Two warnings from ADR-1100 that will otherwise
cost that lane time: adding a FIFTH family pushes the contaminated
`Fib`/`Bitwise` combination into held-out index 3 and is refused; and
`Mathlib.Data.Nat.Count` screens held-out-viable but is not — `Nat.countRange`
already proves five of its rows under other names.
