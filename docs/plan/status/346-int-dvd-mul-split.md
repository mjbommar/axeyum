# Lane: int-dvd-mul-split — closing `Int.dvd_mul` where the Nat sibling's handoff left off

<!-- plan-section: lane-status -->

**Done, 2026-08-30.** `F:ml430-int-dvd-mul-3a7b94cd` (`Int.dvd_mul`) closed.
`docs/plan/status/343-dvd-mul-split.md` (lane `dvd-mul-split`) had closed the
`Nat` sibling `F:ml430-nat-dvd-mul-ebd102e2` the same day and left a precise
three-item blocker list for the `Int` side. **All three were verified against
the tree rather than inherited, and two of the three turned out to be
unnecessary once the real content is routed through `natAbs` instead of a
signed `Int.gcd` scaling.**

## The three named prerequisites, checked

1. **"A general `Int.gcd_mul_right`."** Not built, and not needed. The
   handoff's own sketch scaled `Int.gcd` by a *signed* factor
   (`Int.gcd (x*z) (y*z) = Int.gcd x y * natAbs z`), which is exactly where
   the sign of the scaling factor has to be tracked. The proof here never
   does that: it converts the hypothesis and every intermediate fact to
   `natAbs` values up front (`nat_abs_dvd_nat_abs_of_dvd`, `nat_abs_mul`) and
   runs the whole real-content argument as a `Nat.gcd_mul_right` application
   over `natAbs c, natAbs a, natAbs b` — a genuinely `Nat`-level fact that
   already existed (lane `gcd-mul-right`, same day as `343`). Bridging back
   to `Int` divisibility happens exactly once, via `dvd_of_nat_abs_dvd`, at
   the very end.
2. **"An Int-level cancellation lemma for a nonzero common factor."** Also
   not built, also not needed, for the same reason: the one cancellation in
   the proof is `g1_nat*(natAbs w) ∣ g1_nat*nb ⟹ natAbs w ∣ nb`, a `Nat`-level
   fact, and `Nat.mul_left_cancel_of_pos` already applies once `g1_nat` is
   shown positive. A local Nat-level `dvd_cancel_left_of_ne_zero` — a
   straight copy of `nat_prelude/dvd_mul_split.rs`'s own
   `dvd_cancel_left_of_pos`, built from only `NatOps` default methods so it
   works verbatim from an `IntDev` context — is all that was needed.
3. **"Establishing `g1 ≠ 0` from `c ≠ 0`."** This one WAS a genuine gap, and
   it was cheap: `Nat.eq_zero_of_gcd_eq_zero_left` (already proved) plus a
   local copy of `ring.rs`'s private `nat_abs_zero_implies_int_zero`
   (`natAbs x = 0 → x = 0`, by `Int.rec`) compose directly into a fully
   constructive proof — no case split on `c`'s sign, no excluded middle
   beyond the single `c = 0 ∨ c ≠ 0` split the statement itself needs
   (`Int.eq_em`).

## The degenerate and negative cases

Detail moved to [`../notes/346-int-dvd-mul-split.md`](../notes/346-int-dvd-mul-split.md).

