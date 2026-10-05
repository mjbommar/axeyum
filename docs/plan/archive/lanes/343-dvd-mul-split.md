# Lane: dvd-mul-split — the divisor-splitting iff (Mathlib's `Nat.dvd_mul`/`Int.dvd_mul`)

<!-- plan-section: lane-status -->

**Done (`dvd-mul-split`, 2026-08-30).** `F:ml430-nat-dvd-mul-ebd102e2` closed.
`F:ml430-int-dvd-mul-3a7b94cd` stays open — precise blocker below, not a
re-derivation of the "no short route" verdict two prior lanes already gave it.

## `Nat.dvd_mul_split` — closed

Two prior lanes called `k ∣ m*n ↔ ∃ k1 k2, k1∣m ∧ k2∣n ∧ k1*k2=k` a
factorization-existence statement with no short route. Both sized it before
`Nat.gcd_mul_right` existed (landed the same day, lane `gcd-mul-right`) and
neither reports having tried the gcd construction. With `gcd_mul_right` in
hand it is not a factorization problem at all:

- **Forward.** `k1 := gcd(k,m)`, `k2 := k/gcd(k,m)`. `k1 ∣ m` is
  `gcd_dvd_right` directly. `k1*k2=k` comes from eliminating `gcd_dvd_left`'s
  witness. The one piece of real content, `k2 ∣ n`: `k ∣ k*n` (`dvd_mul`) and
  `k ∣ m*n` (hypothesis) combine via `dvd_gcd` into `k ∣ gcd(k*n,m*n)`;
  `gcd_mul_right` rewrites the gcd to `k1*n`, giving `k ∣ k1*n`; substituting
  `k = k1*k2` gives `k1*k2 ∣ k1*n`; cancelling the positive common factor
  `k1` (`one_le_of_dvd_pos` + `mul_left_cancel_of_pos`, no case split on `k1`
  needed since `k1 ∣ k` and `k > 0` already force it) gives `k2 ∣ n`.
- **Reverse.** Fully uniform: `m*n = (k1*q1)*(k2*q2) = (k1*k2)*(q1*q2) =
  k*(q1*q2)` (a four-factor regroup, `mul_assoc` + `mul_left_comm`), no case
  split, works even when `k1` or `k2` is `0`.
- **`k=0` degenerate case: handled by DIRECT case split, not the general
  formula.** `h : dvd 0 (m*n)` gives `m*n=0` (`mul_eq_zero`), splitting into
  `m=0` (witnesses `(0,n)`) or `n=0` (witnesses `(m,0)`). This is exactly the
  corner the dispatching brief warned "a slick argument silently breaks" on:
  the general formula's `k2 := k/gcd(k,m)` does NOT reproduce a valid witness
  pair when `n ≠ 0 = m` — `gcd(0,m)=m`, `0/m=0`, forcing `k2=0` and needing
  `0 ∣ n`, false in general.

New file `crates/axeyum-lean-kernel/src/nat_prelude/dvd_mul_split.rs`, wired
in via one `declare_dvd_mul_split` call after `declare_gcd_mul_right_mirrors`/
`declare_dvd_add_iff_left`. **Not named `Nat.dvd_mul`**: that kernel name is
already taken by the unrelated trivial lemma `∀ a q, dvd a (a*q)`
(`nat_prelude.rs`'s pre-existing `dvd_mul` field) — declaring under Mathlib's
literal name would hit `DeclarationExists`, the `Nat.inverseIndex` collision
class. Named `dvd_mul_split` (checked free in both preludes before writing).

Verified: 184 `nat_prelude::` tests pass (up from 183; the new theorem needed
adding to `theorem_names`' coverage inventory, caught immediately by
`every_nat_declaration_is_checked_and_axiom_free`). New test
`dvd_mul_split_applies_at_a_concrete_discriminating_instance_and_a_free_degenerate_one`
exercises `Iff.mpr` at a concrete discriminating instance
(`k=6,m=4,n=9`, algorithm's own witnesses `k1=2,k2=3`, producing a real proof
of `dvd 6 36`) and `Iff.mp` at the `k=0` degenerate branch with a genuinely
free `n` (pushed into an explicit `LocalContext`, since a bare unregistered
`FVar` is `UnboundFVar` to the checker, not merely "unknown"). `axiom_footprint`
empty; `nat` trusted surface measured 0 both ways
(`nat_axiom_inventory --require-axiom-free nat`).

`F:ml430-nat-dvd-mul-ebd102e2` flipped to `proved`, `depends_on` expanded by
`scripts/check-fact-depends-derived.py --fix` (11 edges added — every base
algebra lemma the proof term actually calls), `validate-facts.py` clean
(0 errors, `missing_edges=0`).

`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean (one
`doc_lazy_continuation` fixed with a blank line in the module doc's nested
list). `rustfmt --edition 2024 --check` clean on all three touched files.

## `Int.dvd_mul` — stays open, precise blocker

**The Int-native route is the same shape as the Nat proof and is NOT blocked
in principle — it needs meaningfully more new infrastructure than the Nat
side did, and I did not build it this session.** Do not re-derive the "needs
more work" verdict without reading this section; it names exactly what.

What already exists and is directly usable (checked in-tree before writing
this, not assumed):

- `Int.gcd_dvd_left : ∀ a b, ofNat (gcd a b) ∣ a`,
  `Int.gcd_dvd_right : ∀ a b, ofNat (gcd a b) ∣ b`,
  `Int.dvd_gcd : ∀ c a b, c∣a → c∣b → c∣ofNat(gcd a b)` (`int_prelude.rs`
  fields, all pre-existing) — the exact Int-level analogs of the Nat lemmas
  the forward direction uses.
- `nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd` (`int_prelude/gcd.rs`) —
  composing both directions bridges `q ∣ ofNat(natAbs b)` (Int) to `q ∣ b`
  (Int) via the Nat magnitude, WITHOUT needing a sign-guessing step. This is
  the piece that makes an Int-NATIVE construction (deriving `k2` directly
  from an Int-level `dvd_elim`, never guessing `ofNat k2` and checking its
  sign against `c` after the fact) strictly easier than bridging through
  `Nat.dvd_mul_split`'s existential and reconstructing Int witnesses from Nat
  ones afterward — the latter needs an `eq_or_eq_neg_of_nat_abs_eq`-style
  lemma (`x,y:Int, natAbs x = natAbs y → x=y ∨ x=-y`) that does NOT exist and
  would need a 4-branch `Int.rec` case split to build. **Route via the
  Int-native construction, not via the Nat existential + sign fixup.**
- `nat_abs_mul` (`int_prelude/gcd.rs`) — multiplicativity of `natAbs`, the
  bridge `gcd_scaled_mirrors.rs` already used for the three sibling mirrors.
- `Nat.gcd_mul_right` (`nat_prelude/gcd_mul_right.rs`, lane `gcd-mul-right`,
  same day) — the Nat-level distributive law everything below transports.

What is MISSING and would need to be built, in the order the proof needs them:

1. **A general `Int.gcd_mul_right`**, NOT the scaled specialization
   `gcd_scaled_mirrors.rs` already has. Statement:
   `∀ x y z : Int, Eq Nat (Int.gcd (x*z) (y*z)) (Nat.mul (Int.gcd x y) (natAbs z))`.
   Route (no new induction — pure composition of already-proved facts,
   exactly `gcd_scaled_mirrors.rs`'s own technique one level more general):
   `Int.gcd (x*z) (y*z) = Nat.gcd (natAbs(x*z)) (natAbs(y*z))` [defeq] `=
   Nat.gcd (natAbs x * natAbs z) (natAbs y * natAbs z)` [`nat_abs_mul` twice,
   congr] `= Nat.gcd (natAbs x) (natAbs y) * natAbs z` [`Nat.gcd_mul_right`]
   `= Int.gcd x y * natAbs z` [defeq]. Moderate, bounded — same shape as
   `idvd_mul_iff_nat_dvd_mul` in `gcd_scaled_mirrors.rs`.
2. **An Int-level cancellation lemma for a common NONZERO (not necessarily
   positive) left factor.** Grepped and confirmed absent:
   `grep -n 'mul_left_cancel\|cancel_of_ne_zero\|mul_cancel' int_prelude.rs`
   is empty. The Nat proof's `dvd_cancel_left_of_pos` needs `Le 1 k`; the
   Int analog needs `Not (Eq g1 zero)` instead, since `g1 := ofNat(Int.gcd
   c a)` is never negative but CAN be structurally a "positive" or "zero"
   `Int` with no ordering argument available the way `Lt 0 K` was free from
   `k = succ pred` on the Nat side. Likely built the same way as the Nat
   `dvd_cancel_left_of_pos` (local `dvd_elim` + `mul_assoc` + a cancellation
   lemma), but needs whatever the Int prelude's actual `c ≠ 0 → (c*a=c*b →
   a=b)` primitive is (or building one) — not located this session.
3. **Establishing `g1 ≠ 0` when `c ≠ 0`.** On the Nat side this was free:
   `k = succ pred` gives `Lt 0 k` definitionally via `NatOps::zero_lt_succ`,
   with no separate case split. `Int` has no such shortcut — `c ≠ 0` is not
   "not the zero constructor" the way `succ _` is on Nat (Int's two
   constructors are `ofNat`/`negSucc`, and `ofNat 0` is one case among four
   in a naive case split). Grepped and confirmed absent:
   `grep -n 'eq_zero_of_gcd\|gcd_eq_zero' int_prelude.rs` is empty — there is
   no existing `Int.eq_zero_of_gcd_eq_zero_left`-style lemma to use by
   contrapositive. This is the single most expensive-looking piece; it may
   be cheaper to case-split on `c` via `Int.rec` directly (two cases:
   `ofNat j` — reduces to the Nat-side argument on `j` — and `negSucc j`,
   always nonzero) rather than hunting for a pre-existing zero-gcd lemma.
4. **The `c=0` degenerate branch itself**, mirroring the Nat proof's direct
   case split on `m=0 ∨ n=0` (needs an Int-level `mul_eq_zero`; not checked
   for existence this session, but Int has no zero divisors either, so it is
   very likely present or cheap under some name — check before building).

None of this is a soundness or foundations problem — every piece above is
either already-proved arithmetic being transported, or a small new lemma of
a kind this file (`crates/axeyum-lean-kernel/src/int_prelude/gcd.rs` and
neighbors) already builds many of. It is a genuinely separate, moderate-to-
larger proof task from `Nat.dvd_mul_split`, not a continuation of it — size
it as its own lane rather than appending it to a "quick Int transport"
brief, which is what made the `int-gcd-mul-transport` lane's three targets
(all pure transports of an existing shape) cheap and would NOT make this one
cheap.

`F:ml430-int-dvd-mul-3a7b94cd` unchanged (`open`), partition `development`
(not held-out — safe for a future lane to pick up).
