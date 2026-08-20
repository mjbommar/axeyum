# Lane: autogenesis-program

<!-- plan-section: lane-status -->

**Status:** ADR-0529 permits only the declaration-exact canonical native `Acc` package through atomic target-kernel reconstruction. Receipt V5 regenerates `Acc`, `Acc.intro`, and `Acc.rec` with equal source/target identities and admits axiom-free `Acc.inv`; incomplete, lookalike, and mutual packages still decline. The unchanged Mathlib 4.30.0 r082 `Nat.dvd_gcd` control now reaches target admission of `Nat.div_mod_exec` and fails with `TypeMismatch`, leaving the caller environment unchanged.

**Next:** render and compare the expected and inferred target types at the `Nat.div_mod_exec` admission failure; isolate the first reusable representation/proof mismatch; correct it without weakening the target gate; then retry `Nat.dvd_gcd` unchanged. Keep raw arena IDs diagnostic-only.

<!-- plan-section: landed-changes -->

| 2026-08-19 | `1afe65473` | Native/imported Nat prelude composition probe |
| 2026-08-19 | `d1eb38a13` | Alpha-stable cross-kernel expression identity |
| 2026-08-20 | `b5c4bb48b` | Binder-info-insensitive kernel type-shape identity with adversarial controls |
| 2026-08-20 | `24b16642e` | r082 overlap probe classifies kernel-compatible and structurally different types |
| 2026-08-20 | `8dbd18c82` | Required Nat theorem closure census isolates a structurally unblocked first replay slice |
| 2026-08-20 | `9caac0bf5` | First probe-local checked native Nat theorem slice composes over the imported r082 kernel |
| 2026-08-20 | `b7573a525` | ADR-0523 fixes theorem-only identity-gated completed-clone composition as the public V1 boundary |
| 2026-08-20 | `bdc9bf1c9` | Public checked theorem-slice composition API publishes only a fully admitted owned clone and replayable receipt |
| 2026-08-20 | `75aa21d1a` | Composition boundary controls cover unsupported kinds, type mismatch, binder metadata, free variables, partial staging, and receipt mutation |
| 2026-08-20 | `0bcbe935d` | The r082 public-API probe exposes the exact source closure and canonical composition receipt identity |
| 2026-08-20 | `c17b7e65b` | Receipt V2 records translated definitional equality as attempt-only reuse authority and moves the r082 blocker to missing `Exists` |
| 2026-08-20 | `fced2b166` | Receipt V3 atomically reconstructs a demanded singleton inductive and advances the r082 root to missing definition `Nat.mul` |
| 2026-08-20 | `acade2a45` | Receipt V4 target-checks exact demanded definitions and advances the r082 root to the `Bool.rec` branch-order seam |
| 2026-08-20 | `502184d3f` | Native Bool adopts official Lean constructor order with kernel-prelude consumers migrated |
| 2026-08-20 | `012c6b4f6` | Solver reconstruction preserves semantic false/true branches under the official order |
| 2026-08-20 | `866add778` | Official-order fixtures and golden reconstruction bodies pass the authoritative pre-push gate |
| 2026-08-20 | `a5a111498` | Native `Nat.mod_lt` proves Lean's general positive-denominator contract and migrates GCD/Bezout consumers |
| 2026-08-20 | `ac33a0a2d` | Named compatibility diagnostics bind `Nat.mod_lt` translated definitional equality and expose `Acc` next |
| 2026-08-20 | `3d466b45c` | Receipt V5 reconstructs only canonical native `Acc` exactly and exposes `Nat.div_mod_exec` target type mismatch |
