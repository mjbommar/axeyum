# Lane: int-emod-negative — two of the three named lemmas for `Int.gcd_div`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, int-emod-negative, 2026-08-29).**
Landed **two of the three** lemmas `docs/plan/status/236-int-gcd-div-2.md`
named as the missing pieces for `F:ml430-int-gcd-div-5e01872f`
(`Int.gcd_div`): `Int.emod_natAbs_bound` (the keystone) and
`Int.ediv_emod_unique_general`. `Int.gcd_div` itself stays open, precisely
scoped below. No ledger edit was made — the fact is still `open`.

**Verified before starting**: no inline negative-divisor `emod` bound exists
anywhere in `wilson.rs`, `crt.rs`, or `modinv.rs` (grepped proof bodies, not
names, per the brief). `crt.rs`'s own module doc already states the gap
directly — "this development has no bound on emod's magnitude for a
negative modulus" — confirming the prior handoff's assessment rather than
finding a shortcut around it.

**1. `Int.emod_natAbs_bound`** (`int_prelude/division.rs`):
`∀ a b, Not (Eq Int b zero) → Int.lt (emod a b) (ofNat (natAbs b))`.
Every one of the four `Int.rec` branches reuses existing machinery rather
than re-deriving it: `natAbs` is an unconditional ι-reduction (`ofNat n ↦
n`, `negSucc n ↦ succ n`), so the divisor's magnitude collapses to exactly
the shapes `emod_lt_of_pos`'s two row builders (`row_emod_lt_of_pos_of`,
`row_emod_lt_of_pos_neg`) and the `sub_nat_nat_lt_ofnat` combinator already
handle — reused directly. The `b ≠ 0` hypothesis is load-bearing in exactly
one of the four branches (`ofNat m, ofNat n`, where `n` could be `0`),
derived via the contrapositive of `nat_eq_to_int` plus
`Nat.zero_lt_of_ne_zero` and the general `Nat.mod_lt : 0 < n → m % n < n`
(no `succ`-shape pinning needed, unlike `emod_lt_of_pos`, which cannot state
this bound for a negative divisor at all).

Detail moved to [`../notes/242-int-emod-negative.md`](../notes/242-int-emod-negative.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-emod-negative | landed `Int.emod_natAbs_bound` (`declare_emod_natabs_bound`, `int_prelude/division.rs`) — the sign-general remainder bound `emod_lt_of_pos` cannot state; `int_prelude::` 40 -> 41 |
| 2026-08-29 | int-emod-negative | landed `Int.ediv_emod_unique_general` (`declare_ediv_emod_unique_general`, same file) — sign-general division-algorithm uniqueness via a negate-and-reduce-to-the-positive-case argument; `int_prelude::` 41 -> 42; `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) left open, precisely scoped to a fourth not-yet-built bridge lemma plus its own mutual-divisibility argument |
