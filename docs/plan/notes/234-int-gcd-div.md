# Notes: 234-int-gcd-div

Detail moved out of [`../status/234-int-gcd-div.md`](../status/234-int-gcd-div.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) — the fully general
  statement (`c` an arbitrary, possibly negative or zero, `Int`) needs an
  exact-quotient uniqueness argument for a NEGATIVE divisor. This kernel's
  `Int.ediv_emod_unique` (`division.rs`) is stated only for `0 < b`; there is
  no proved analogue for `b < 0` (checked: no `ediv_neg`/`mul_ediv_cancel`-style
  lemma exists for a negative or zero divisor anywhere in `int_prelude`).
  Building that generality is a real, separate piece of work, not a
  rearrangement of what exists.
- `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc` (`Int.gcd_div_gcd_div_gcd`) —
  the divisor here (`↑(i.gcd j)`) is always `≥ 0`, so the negative-divisor gap
  above does NOT block it; Mathlib itself derives this fact as a one-line
  corollary of `Int.gcd_div`, which we do not have. I worked out an
  independent Bézout-based route that avoids needing `Int.gcd_div` at all
  (reduce `qi := i/c`, `qj := j/c`'s common Bézout combination `X` mod `c`,
  show `natAbs(X) = 1` via `Nat.mul_left_cancel_of_pos` on `c*1 = c*X`, then
  `gcd(qi,qj) ∣ natAbs(X) = 1`). Every lemma the route needs exists
  (`gcd_dvd_left/right`, `dvd_mul_right`, `dvd_add`, `dvd_trans`,
  `nat_abs_mul`, `nat.mul_left_cancel_of_pos`, `nat.eq_one_of_dvd_one`,
  `nat_abs_dvd_nat_abs_of_dvd`, `gcd_eq_gcd_ab_witnesses`, `mul_assoc`,
  `left_distrib`, `mul_one`) — but I stopped short of implementing it because
  the last algebraic step (`natAbs(c*1)` reducing to a bare `g`) does **not**
  reduce by computation for a SYMBOLIC `g := Nat.gcd i j` — `Nat.mul g 1`
  gets stuck at `Nat.add Nat.zero g` (`Nat.add` recurses on its RIGHT
  argument, per this repo's own standing gotcha), so the step needs an
  explicit `Nat.mul_one`/`Nat.zero_add`-style lemma rather than raw defeq,
  and I ran out of budget to nail that down and verify it against the kernel
  in this pass rather than leave a plausible-but-unverified term. Left open
  rather than landing something unchecked.

**Re-confirmed myself (not just trusted the brief):**
`scripts/check-autogenesis-semantic-contract-target-census.py` references
`F:ml430-int-gcd-div-5e01872f` only inside a static, pinned manifest row
(`EXPECTED_NARROWEST["fact_id"]`) compared against
`artifacts/autogenesis/mathlib-semantic-contract-target-census-v1.json`'s own
content by `source_content_sha256` and a handful of structural counts. Grepped
the whole script for `epistemic_status`: zero hits. It never reads the fact's
live status, so leaving `5e01872f` open does not disturb it.

**Mutation marker:** `F:ml430-mutation-48fe130e2b8eadb6f626b66f` is in this
family per the brief; skipped, not touched.

**What the kernel REJECTED and why:** nothing — `cargo check`,
`cargo test --lib int_prelude::`, `cargo fmt --check`, and `cargo clippy`
all passed on the first constructed term for `Nat.exists_mul_mod_eq_gcd`
(the term construction was planned in full, including every intermediate
lemma's exact signature, before writing any Rust).

**Timing:** `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 40
passed, 0 failed, finished in 3.79s before the rustfmt fixup and 3.97s after
(unchanged test count both times).
