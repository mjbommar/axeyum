# Notes: 225-nat-factorial-dvd

Detail moved out of [`../status/225-nat-factorial-dvd.md`](../status/225-nat-factorial-dvd.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`Nat.ascFactorial_succ_eq_factorial_mul_choose : (succ m).ascFactorial k = k! *
(m+k).choose k` is the rising-factorial analogue, reindexed by `n := succ m`
specifically so no `Nat.sub` is ever needed (`ascFactorial`'s natural bridge
would otherwise be `k! * (n+k-1).choose k`, needing an `n ≥ 1` truncation
guard `descFactorial` does need and this reindexing sidesteps). Proved by a
SINGLE induction on `k` (`m` fixed throughout — no `n=0` boundary to handle
inside this lemma, since `n := succ m` is never `0`), chaining eight
identities: `asc_factorial_succ`, the IH, `mul_left_comm`, `Nat.succ_add`
(aligning `succ m + j` with `succ_mul_choose_eq`'s `succ n'` shape),
`Nat.succ_mul_choose_eq`, `Nat.add_succ` (aligning back to `m + succ j`),
`mul_assoc` (reversed), `factorial_succ` (reversed). `factorial_dvd_ascFactorial`
case-splits `n`: `n = 0` needs a small separate lemma
`Nat.zero_ascFactorial_succ : (0).ascFactorial (succ k) = 0` (induction on
`k`, base is literally `ascFactorial_one` at `n:=0`) + `dvd_zero` (`k = 0` via
`dvd_refl`); `n = succ m` uses the bridge + `dvd_mul`, identical shape to the
descending case.

**What the kernel rejected, and why:** the asc bridge's `k = succ j` step
initially failed with `TypeMismatch` across the ENTIRE `nat_prelude::` suite
(all 113 tests, the "one bad declaration poisons the shared build" pattern) —
diagnosed by a temporary debug test rendering both sides of the mismatch via
`Kernel::render_lean` (removed before the final commit), which showed step 4's
`congr` rewrote `succ_add`'s substitution under `mul(x, choose_mj)` only,
while the surrounding `chain` call used it as a proof of the FULLY
`mul(fact_j, ..)`-wrapped statement — missing one layer of congruence
context. Bisected which of the three new `asc_factorial.rs` declarations was
at fault by disabling each `declare_*` call one at a time against a single
fast test, per the standing rule: `declare_zero_asc_factorial_succ` and the
three new `desc_factorial.rs` declarations were fine alone;
`declare_asc_factorial_succ_eq_factorial_mul_choose` was the culprit. Fixed
by wrapping the congr context in `mul(fact_j, ..)` directly, matching the
already-correct sibling step (step 6, same function).

Measured: `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`
(`nat_axiom_inventory --require-axiom-free nat`) — all six new theorems
(`descFactorial_succ_eq_succ_mul`, `descFactorial_eq_factorial_mul_choose`,
`factorial_dvd_descFactorial`, `zero_ascFactorial_succ`,
`ascFactorial_succ_eq_factorial_mul_choose`, `factorial_dvd_ascFactorial`)
add zero axioms; `nat_prelude::` suite: **113 passed, 0 failed** (was 107
before this lane's merge base — 112 with these six theorems admitted but not
yet in `theorem_names`/`definition_names`, since
`every_nat_declaration_is_checked_and_axiom_free` derives its coverage from
the ENVIRONMENT and fails naming exactly what's missing, per the standing
rule against hand-maintained "every X" lists). `the_build_is_deterministic`'s
`D + T` pin recounted by reading the test's own panic message (never by
hand-incrementing): `81 + 411` → `81 + 417` = 498. `cargo fmt --check` and
`clippy --all-targets -D warnings` both clean.

No target in this lane's scope (both `F:ml430-nat-factorial-dvd-*` facts, and
`F:ml430-nat-factorial-dvd-factorial-e9d14845`, already `proved`, out of
scope) carried a `⛔ HELD-OUT` or `⛔ MUTATION` marker.

`python3 scripts/validate-facts.py`: 0 errors. Both facts' `checker_command`s
verified to run and exit 0 against the landed kernel.

Next lane: the falling/rising-factorial ↔ `choose` bridges are now general
building blocks (`Nat.descFactorial_eq_factorial_mul_choose`,
`Nat.ascFactorial_succ_eq_factorial_mul_choose`) — reusable for e.g. a
`multichoose`-to-`descFactorial` bridge or a `choose`-symmetric identity that
needs the factorial relationship in the other direction.
