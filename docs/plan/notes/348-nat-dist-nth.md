# Notes: 348-nat-dist-nth

Detail moved out of [`../status/348-nat-dist-nth.md`](../status/348-nat-dist-nth.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Both are Definitions, so the kernel's type-check proves nothing about
correctness** (CLAUDE.md's standing warning). Evaluation tests added in
`nat_prelude_tests.rs`: `dist_evaluates_correctly` (concrete values on both
sides of `Nat.sub`'s truncation asymmetry — `dist 3 5 = dist 5 3 = 2`,
discriminating against a dropped-reverse-subtraction bug), plus zero/self
boundaries; `dist_theorems_apply_at_free_variables_and_concrete_instances`
(comm/self/succ_succ at a genuinely free pair via `LocalContext`/`infer_in`;
the two `sub`-orientation lemmas at concrete numerals with a hand-built
`Le 2 5` witness, confirming they were not transposed — CLAUDE.md's most
common bug family here; the zero-boundary pair checked at BOTH a concrete
instance and the free `n`, since `dist n 0`/`dist 0 n` collapse to the same
numeral once concrete, which made the first version of that negative
control vacuous); `nth_evaluates_correctly` (an infinite predicate `k >= 3`
checked at three successive indices against an "always return the first
match" bug and an off-by-one; a single-witness predicate `k = 5` checked
for both the found case and the fuel-exhaustion sentinel `0`, matching
Mathlib's own "not enough witnesses" convention).

**Screen confirmed admitting both, at exactly the predicted counts.**
Regenerated `kernel-environment-snapshot-v1.json` from a fresh
`shape_search --include-constructed` run (also picked up unrelated
definition/theorem-count drift from other lanes merged since 2026-08-29:
`328->331` defs, `1770->1934` theorems — not this lane's content, just
staleness), then `propose-nursery-refill.py --remeasure` (needs /nas3,
mounted here) to rebind `refill-headroom-v1.json`. Its READY FAMILIES list
now shows:

    18  Mathlib.Data.Nat.Dist
    11  Mathlib.Data.Nat.Nth

— matching ADR-0645's prediction exactly, and pushing ready-family count
15 -> 17 ("enough for a draw of 2 that clears the floor of 10").
`gen-autogenesis-statable-vocabulary.py` (run per the brief) reports
UNCHANGED — expected, since no SETTLED fact yet uses either constant; that
script's "bridge" metric is orthogonal to the R9 name-screen/readiness
question this task was about.

**Did NOT run `gen-autogenesis-nursery-refill.py`** (the actual draw) — out
of scope per the brief; its `--check` gate is red on `main` for a
pre-existing, separately-owned reason (two writers of
`mathlib-statable-vocabulary-v1.json`, per 345's notes) and remains so,
unchanged by this lane. `check-autogenesis-nursery.py` is likewise still
red on `main` for draw 5's pre-existing finding, unchanged here.

**Checks run:** `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 192
passed, 0 failed (full sweep, nonzero count, includes all three new tests
by name). `cargo fmt --all --check` clean. `cargo clippy -p
axeyum-lean-kernel --all-targets --all-features -- -D warnings` clean.
`python3 scripts/validate-facts.py` — 2220 facts, 0 errors (untouched by
this lane). `check-autogenesis-holdout-isolation.py` PASS, unchanged.
`scripts/check-merge-hygiene.sh` PASS.

**Next lane:** author the draw itself (2 families:
`Mathlib.Data.Nat.Dist`/`Mathlib.Data.Nat.Nth`, or others from the 17
ready) in `gen-autogenesis-nursery-refill.py`'s `FAMILY_MODULES`/
`FAMILY_ROUTES` — but first resolve the pre-existing two-writer conflict
on `mathlib-statable-vocabulary-v1.json` that keeps that generator's
`--check` red, or the draw will look clean and immediately fail the gate.
