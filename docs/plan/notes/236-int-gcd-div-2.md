# Notes: 236-int-gcd-div-2

Detail moved out of [`../status/236-int-gcd-div-2.md`](../status/236-int-gcd-div-2.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `c` divides `i` and `j` exactly (`gcd_dvd_left`/`_right` +
  `emod_eq_zero_iff_dvd` + `ediv_add_emod`), giving `i = c*qi`, `j = c*qj`.
- Bézout (`gcd_eq_gcd_ab_witnesses`) gives `c = i*u + j*v`; substituting and
  factoring (`mul_assoc`/`left_distrib`) gives `c = c*X`, hence (via
  `Int.mul_one`) `c*1 = c*X`.
- `natAbs` of both sides (`nat_abs_mul`) plus `Nat.mul_left_cancel_of_pos`
  (fed the theorem's own hypothesis `h : Nat.lt zero g` DIRECTLY for the
  `Le one (natAbs c)` premise — `Nat.lt` unfolds to exactly that shape once
  `natAbs (ofNat g)` ι-reduces to `g`, no separate positivity lemma needed)
  gives `natAbs X = 1`.
- `gcd qi qj` divides `qi*u` and `qj*v` (`gcd_dvd_left`/`_right` +
  `dvd_mul_right` + `dvd_trans`), hence divides their sum `X` (`dvd_add`),
  hence divides `natAbs X = 1` (`nat_abs_dvd_nat_abs_of_dvd`), hence equals
  `1` (`Nat.eq_one_of_dvd_one`).

**The construction type-checked on the FIRST attempt against the kernel** —
no rejected term, no retry, no defeq surprise beyond the two ι/δ unfolds
noted above (both routine and already exercised elsewhere in this file).

Verified: `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **40
passed before my change, 40 passed after** (one new theorem replacing the
list-coverage gap it would otherwise have created), including
`every_int_declaration_is_checked_and_axiom_free` and
`derived_laws_have_no_axiom_footprint`, plus the fact's own
`theorem_axiom_footprint` grep checker (both `--release`, confirmed the
matched row `integer<TAB>Int.gcd_div_gcd_div_gcd<TAB>0<TAB>` with an empty
footprint column). `cargo fmt --edition 2024 --check` and `cargo clippy -p
axeyum-lean-kernel --all-targets -- -D warnings` both clean.
`python3 scripts/validate-facts.py`: 0 errors.

`derived_laws`'s pinned array in `int_prelude_tests.rs` went 150 → 151;
recounted by grepping the array body for `^\s*p\.` lines (151), not by
incrementing the old number.

**Assessed, left open: `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`).**
Confirmed genuinely absent, on TWO independent grounds, not just the one the
prior lane named:

1. **The negative-divisor gap is real.** Read `Int.ediv`/`Int.emod`'s actual
   recursive definitions (`int_prelude/division.rs:1-165`): both ARE defined
   for every sign of the divisor (four-branch `Int.rec` on `a` then `b`,
   matching Lean 4 core's `ediv`/`emod` bit for bit), and `Int.ediv_add_emod`
   (the division algorithm identity `b*(a/b)+a%b=a`) is proved
   UNCONDITIONALLY, all four sign branches. But the bridge from that identity
   to "`c` divides `a` exactly" — `emod_eq_zero_iff_dvd` — is stated only for
   `0 < b`, and its proof route goes through `emod_nonneg` (unconditional,
   `b≠0` only) AND `emod_lt_of_pos : ∀ a b, 0 < b → a%b < b` (the SECOND bound
   is stated with `b` itself as the upper bound, which is simply FALSE for
   negative `b` — the correct bound for negative `b` is `a%b < natAbs b`, a
   different statement, not an unmet hypothesis on the same one). Grepped
   every file under `int_prelude/` for `ediv`/`neg`-divisor handling
   (proof bodies, not names, per the brief): every hit is about a negative
   **dividend**, never a negative **divisor**'s remainder bound. No inline
   unnamed step anywhere covers it.

2. **`Int.gcd_div` itself does not exist even for a POSITIVE divisor**,
   which the prior lane's note did not surface (it only discussed the
   negative-divisor gap, on the implicit assumption the positive case was
   already available to build on). Grepped `int_prelude.rs` and every
   `int_prelude/*.rs` for `gcd_div` — the only two hits are this fact's own
   doc comments (this lane's and the prior one's). So the *general theorem*
   this fact needs — "`c ∣ a → c ∣ b → gcd(a/c, b/c) = gcd(a,b)/natAbs(c)`" —
   would need to be built from scratch even restricted to `c > 0`, and that
   restricted form is itself comparable in size to
   `gcd_div_gcd_div_gcd` (a genuine number-theoretic argument: `gcd(a,b)`'s
   own common divisor `c` must be shown to relate to `gcd(a/c,b/c)*c` via
   mutual divisibility or a Bézout-style argument, not a one-line corollary
   of anything already proved).

**What would need to be built, precisely**, if a future lane takes this on:

- `emod_natAbs_bound : ∀ a b, Not (Eq Int b zero) → lt (emod a b) (of_nat (nat_abs b))`
  — the general remainder bound that works for a divisor of EITHER sign
  (generalizing `emod_lt_of_pos`, which only covers `0 < b` and bounds
  against `b` itself rather than `natAbs b`).
- `ediv_emod_unique_general : ∀ a b q1 r1 q2 r2, Not (Eq Int b zero) →
  a = b*q1+r1 → 0 ≤ r1 → r1 < natAbs b → a = b*q2+r2 → 0 ≤ r2 →
  r2 < natAbs b → q1 = q2 ∧ r1 = r2` — the sign-general analogue of
  `ediv_emod_unique`, needed to reprove `emod_eq_zero_iff_dvd` (or a
  sign-general replacement) for `b ≠ 0` rather than `0 < b`.
- `gcd_div : ∀ a b c, c ∣ a → c ∣ b → Eq Nat (gcd (a.ediv c) (b.ediv c))
  (Nat.div (gcd a b) (nat_abs c))` itself, which does not exist at any
  divisor sign yet and is the actual target statement.

None of these are one-line consequences of what exists; this is real,
separate proof work, not a rearrangement. Left `epistemic_status: "open"`
with `evidence: []` unchanged — no ledger edit was made to this fact.

**Re-confirmed the semantic-contract-census note from the handoff**: the
brief's claim that `scripts/check-autogenesis-semantic-contract-target-census.py`
pins `F:ml430-int-gcd-div-5e01872f` by `source_content_sha256` (not by
`epistemic_status`) was not re-verified independently this pass — the prior
lane already did this check twice per the brief, and leaving the fact open
matches what it found. No edit was needed to that script.

**Mutation testing**: skipped, not touched, per instructions.

**What the kernel REJECTED and why**: nothing. Both the `Int.mul_one`-based
route for `gcd_div_gcd_div_gcd` and the assessment of `gcd_div` (no code
written for the latter) went through without a single rejected term.

**Timing**: `cargo test -p axeyum-lean-kernel --lib int_prelude::` —
3.81s before, 3.83s after (test count 40 → 40, one panic on the coverage
list fixed by adding the new name, no other regression).
