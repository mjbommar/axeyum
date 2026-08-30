# Notes: 352-nat-fermat-number

Detail moved out of [`../status/352-nat-fermat-number.md`](../status/352-nat-fermat-number.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

— matching Mathlib's own `fermatNumber_zero`/`_one`/`_two` (each `:= rfl`
there). Test `fermat_number_evaluates_correctly`
(`nat_prelude_tests.rs`) checks all three by `def_eq`, with negative
controls against a dropped `+ 1` (values 2/4/16) and against computing
`2^n + 1` instead of the nested `2^(2^n) + 1` (value 5 at `n=2`, distinct
from the true 17). Stopped at `n = 2` deliberately — every numeral here is
unary, `fermatNumber` grows doubly exponentially, and `n = 3` (formed
magnitude `2^8 = 256`) was not attempted or measured; `n = 4` (`65537`)
would be catastrophic per this repo's measured unary-numeral cost curve.
Full `nat_prelude::` sweep (197 tests, was 196) ran in 4.74s uncontended —
no measurable cost from this declaration.

### Contamination check

Every `Nat.fermatNumber*` name now in the kernel environment (via
`shape_search --include-constructed`, grepped for `fermatNumber`):

```
Nat.fermatNumber   definition   Nat -> Nat
```

Exactly one name, the definition itself. No `Nat.fermatNumber_*` theorem
exists.

### Re-screen (after declaring, before reporting)

The committed `artifacts/autogenesis/kernel-environment-snapshot-v1.json`
predated this declaration (still 2374 declarations, ADR-0653's own
snapshot), so `propose-nursery-refill.py` initially showed
`Mathlib.NumberTheory.Fermat` ABSENT from the ready-family list — a stale
read, not a real result. Regenerated the snapshot via the committed path
(`gen-autogenesis-nursery-refill.py --snapshot-from <shape_search dump>`,
2383 declarations now), then `gen-autogenesis-statable-vocabulary.py
--write` and `propose-nursery-refill.py --remeasure`:

```
READY FAMILIES     18 (was 17)
  ...
  13  Mathlib.NumberTheory.Fermat
```

13/13 rows survive the screen unused, 0 held-out-contaminated (no theorem
name to collide) — matching ADR-0653's `0/10` prediction exactly.
**Did NOT run `gen-autogenesis-nursery-refill.py`'s draw path** —
`FAMILY_MODULES`/`FAMILY_ROUTES` are untouched; the next lane authors the
draw.

## Checks run

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib nat_prelude::`
  — 197 passed, 0 failed (was 196; +1 for `fermat_number_evaluates_correctly`,
  confirmed by name: `1 passed`).
- `cargo fmt --all --check` — clean.
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets
  --all-features -- -D warnings` — clean.
- `python3 scripts/validate-facts.py` — 2222 facts, 0 errors (no fact files
  touched by this lane).
- `bash scripts/check-merge-hygiene.sh` — see report below.

## Commits

- `0065c83b1` — `Nat.fermatNumber` declaration + evaluation test.
- `2d7d77502` — regenerated env snapshot / statable vocabulary / refill
  headroom artifacts to reflect the new declaration.

## Handoff

The next lane authors draw 7: two new held-out-safe families from the
`ready_families` list in `artifacts/autogenesis/refill-headroom-v1.json`
(18 available, `Mathlib.NumberTheory.Fermat` now included at 13 rows) into
`gen-autogenesis-nursery-refill.py`'s `FAMILY_MODULES`/`FAMILY_ROUTES`, then
regenerate. Per ADR-0653: whichever module is drawn alongside Fermat,
confirm it independently — do not trust this handoff's snapshot forever,
re-run `propose-nursery-refill.py` first, since a family's readiness can
change the moment ordinary development proves one of its mirror names.
