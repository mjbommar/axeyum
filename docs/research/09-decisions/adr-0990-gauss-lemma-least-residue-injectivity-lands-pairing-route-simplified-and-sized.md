# ADR-0990: Gauss's lemma's least-residue injectivity lands axiom-free; the pairing lemma's route is simplified and precisely sized

Status: accepted
Date: 2026-08-31
Index-summary: `Nat.least_residue_injective_of_coprime : ∀ pp a k k', 0 < pp
-> gcd a pp = 1 -> k < pp -> k' < pp -> leastResidue pp a k = leastResidue pp
a k' -> k = k'` lands axiom-free in `nat_prelude/gauss_lemma.rs` (piece 1 of
ADR-0970/ADR-0985's connecting-theorem sizing). Piece 2 (the pairing lemma)
is NOT built this session, but its route is simplified from ADR-0970's
original framing and checked signature-by-signature against the tree: it
reduces to `InjectiveOn`/`MapsInto` of a signed-fold self-map on `[0,m)`,
which is exactly the hypothesis shape `Int.prodRange_permute` already
consumes — no separate bijection witness or partner-index construction is
needed.
Index-status: accepted

## Context

ADR-0970 and ADR-0985 landed Gauss's lemma's counting primitive
(`Nat.leastResidue`/`gaussSignNeg`/`gaussNegCount`) and its `a := 2` closed
form, and sized the remaining "connecting theorem" (`a^m ≡ (-1)^count [p]`,
Gauss's lemma's actual content) as three pieces, unattempted:

1. Injectivity of the least-residue map on `{1,…,m}`.
2. A pairing lemma: whenever `leastResidue p a k` exceeds `p/2`, its
   "negative" partner `p - leastResidue p a k` is itself a least residue of
   some other `k'` in `{1,…,m}`, and the resulting map is a bijection onto
   `{1,…,m}`.
3. A product-cancellation argument over `Int.prodRange` (built for Wilson's
   theorem), cancelling the shared `m!` factor.

This session verified all three citations (`Nat.gaussNegCountTwoClosedForm`,
`Nat.restrict_injective`, `Int.prodRange_permute`, `int_prelude/wilson.rs`,
ADR-0970) against `origin/main` before starting, per the standing rule that a
handoff's "what remains" is a hypothesis to check, not inherit.

## Decision

**Build piece 1 in full; do not attempt piece 2 this session, but simplify
and precisely re-size its route before stopping.**

### Piece 1: landed

`Nat.least_residue_injective_of_coprime` needs only positivity and
coprimality — not primality — which is a strictly more general and more
directly reusable statement than ADR-0970's "`{1,…,m}`, `a` coprime to `p`"
framing suggested. A caller in the classical Gauss's-lemma setting supplies
`gcd a pp = 1` via the already-landed `Nat.coprime_of_lt_prime`
(`primes.rs`).

Route (no case split — a genuine simplification over what ADR-0970's
sizing implied a "restricted to `{1,…,m}`" proof might need):
`leastResidue pp a k` unfolds definitionally to `mod (mul a k) pp`.
`mod_self_congr` (`group.rs`, exposed `pub(super)` for this file, previously
module-private) gives `modEq pp (a*k) (mod (a*k) pp)`, symmetrically for
`k'`. The hypothesis `heq` (defeq to `Eq (mod (a*k) pp) (mod (a*k') pp)`,
since `leastResidue` unfolds — matching `gauss_residue_two_eq_double_of_lt`'s
own no-congruence-step idiom, ADR-0970) transports the second `modEq` via a
custom `Eq.rec` motive into `modEq pp (mod (a*k) pp) (a*k')`; `mod_eq_trans`
chains that with the first into `modEq pp (a*k) (a*k')`; `Nat.mod_eq_cancel`
(`euler.rs`) cancels the shared coprime factor `a`, giving `modEq pp k k'`;
`mod_eq_of_mod_eq_rel` (`group.rs`, also exposed `pub(super)`) turns that
back into `mod k pp = mod k' pp`; `Nat.mod_eq_self_of_lt` collapses each side
to `k`/`k'` using the bound hypotheses; a three-step `d.chain` closes
`k = k'`.

**Axiom footprint, read from the kernel**
(`theorem_axiom_footprint -- least_residue_injective_of_coprime`): `0`.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::`: 252 passed, 0 failed
(up from 250 before this session).

### Piece 2: NOT built, route simplified and re-sized

ADR-0970's framing suggested constructing an explicit partner index `k'`
for each "negative" `k` and assembling a bijection. **That is more than
`Int.prodRange_permute` actually needs.** Its exact signature, checked
against `int_prelude/prod.rs`:

```
prodRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
  Eq Int (prodRange f n) (prodRange (fun k => f (σ k)) n)
```

`InjectiveOn σ n := ∀ i j, i<n → j<n → σ i = σ j → i = j` and
`MapsInto σ n := ∀ i, i<n → σ i < n` (`finite.rs`) — a **self-map** of
`[0,n)`, no inverse function or explicit witness required. So piece 2's
actual deliverable is: **the "signed fold"
`gaussFold pp a k := if gaussSignNeg pp a k then sub pp (leastResidue pp a
k) else leastResidue pp a k` is `InjectiveOn`/`MapsInto` on the shifted
0-indexed range `[0,m)`.** Once that lands, piece 3 can feed it to
`prodRange_permute` directly — no separate pairing/bijection lemma is a
distinct proof obligation from injectivity + boundedness.

**Injectivity of `gaussFold`, by cases on the two inputs' signs** (checked
signature-by-signature against the tree, not merely sketched):

- **Same sign** (`gaussFold k = gaussFold k'` both via the identity branch,
  or both via the `sub pp (·)` branch): in the identity case,
  `leastResidue pp a k = leastResidue pp a k'` directly, closed by
  `Nat.least_residue_injective_of_coprime` (piece 1, already landed). In the
  `sub`-branch case, `sub pp r_k = sub pp r_k'` with both `r_k, r_k' < pp`
  gives `r_k = r_k'`. **No `sub_left_cancel`-named lemma was found in the
  tree** (checked, genuinely absent, unlike every other name cited in this
  route) — it does not need to be built as subtraction cancellation:
  `add_sub_cancel_of_le : Le i k → add i (sub k i) = k` (confirmed present)
  applied at `i := r_k`/`i := r_k'`, `k := pp` reconstructs `add r_k (sub pp
  r_k) = pp` and its twin; substituting the branch hypothesis `sub pp r_k =
  sub pp r_k'` into one and equating both reconstructions to `pp` gives an
  equation `add r_k (sub pp r_k) = add r_k' (sub pp r_k)`, whose two addends
  cancel to `r_k = r_k'` (`Nat.add_right_cancel`-style, or by symmetric
  application of the same reconstruction) without a new primitive.
- **Opposite sign** (`r_k = pp - r_k'`, i.e. `r_k + r_k' = pp`): this branch
  is **vacuous**, and the argument is fully checked against existing lemma
  signatures:
  - `mod_self_congr(pp, pos_pp, a*k)` and the `k'` twin give
    `modEq pp (a*k) r_k` and `modEq pp (a*k') r_k'`.
  - `Nat.mod_eq_add : modEq d a b → modEq d c e → modEq d (a+c) (b+e)`
    (`nat_prelude.rs`, confirmed present) combines these into
    `modEq pp (a*k + a*k') (r_k + r_k')`.
  - `Nat.mod_eq_zero_of_dvd : dvd d n → modEq d n zero` (confirmed present)
    applied at `dvd pp pp` (`Nat.dvd_refl`, confirmed present) gives
    `modEq pp pp 0`; transport along the branch hypothesis `r_k + r_k' = pp`
    (symm) gives `modEq pp (r_k + r_k') 0` — cleaner than reaching for
    `group.rs`'s private `mod_self` helper, and uses only already-`pub`
    names.
  - `mod_eq_trans` chains to `modEq pp (a*k + a*k') 0`; `Nat.left_distrib`
    (`nat_prelude.rs`, confirmed present) rewrites `a*k + a*k'` to
    `a*(k+k')`; `Nat.mod_eq_cancel` (coprimality of `a`, `c*0 = 0` via
    `mul_zero`) cancels `a`, giving `modEq pp (k+k') 0`.
  - `k + k' < pp` (from `1 ≤ k, k' ≤ m` and `pp = 2m+1`, so `k+k' ≤ 2m =
    pp-1`) plus `mod_eq_of_mod_eq_rel` and `Nat.mod_eq_self_of_lt` at both
    `k+k'` and `0` (trivial: `mod 0 pp = 0`) gives `k + k' = 0` — contradicting
    `k ≥ 1` (`Nat.add` positivity: `0 < k → 0 < k + k'`, then `Nat.lt_irrefl`
    against the derived `k+k' = 0`). `False.rec` closes the branch.
  - This is a genuine simplification over ADR-0970's "the partner lands
    among `{1,…,m}`'s residues" framing: no partner witness is
    **constructed** — the branch is simply shown impossible, which is all
    injectivity needs.

**`MapsInto` of the shifted fold**: needs `leastResidue pp a k ≠ 0` (so
`sub pp (leastResidue pp a k)` and the identity branch both land in `[1,
pp)`, hence `[1,m]` after the sign split) — this is itself a small new
lemma, NOT yet in the tree: `leastResidue pp a k = 0 → p ∣ a*k` (unfold
`mod`), `Nat.euclid_lemma`/`Nat.coprime_dvd_mul_left` (both confirmed
present) plus `gcd a pp = 1` gives `p ∣ k`, contradicting `0 < k < pp` via
`Nat.le_of_dvd` (same shape `Nat.coprime_of_lt_prime`'s own proof already
uses, `primes.rs`). Then the two branch bounds (`r ≤ m` when not negative,
via `Nat.ble_eq_false_of_lt`'s converse on `gaussSignNeg`'s threshold; `pp -
r ≤ m` when negative, via `pp = 2m+1` arithmetic) close `MapsInto` at
`m` for the 1-indexed value, and a `pred`/`succ` shift lemma (careful:
`Nat.sub`/`Nat.pred` truncate silently, per this repository's standing
warning — build the shift as a SEPARATE composition step, not inline
subtraction) closes it for the 0-indexed self-map `prodRange_permute` needs.

**Estimated size**: comparable to or somewhat larger than piece 1's ~150
lines of term construction, plus the new `leastResidue`-nonzero lemma
(~40-60 lines, structurally similar to `coprime_of_lt_prime`'s own proof).
Every lemma name this route depends on was confirmed present with the
stated signature before writing this ADR, including the `sub`-branch
same-sign case (routed through `add_sub_cancel_of_le` above rather than a
dedicated cancellation lemma, since none was found under any plausible
name).

## What remains — piece 3, unchanged from ADR-0970/ADR-0985

Once piece 2's `InjectiveOn`/`MapsInto` land, piece 3 still needs, NOT sized
further this session:

- `∏_{k=1}^m (a·k) = a^m · m!` as an `Int.prodRange` identity (a
  `prodRange`-vs-`pow`/`prodRange`-vs-constant-multiple lemma; check
  `int_prelude/prod.rs` for an existing `prodRange_const_mul` or build one).
- A `modEq`-multiplicativity-over-a-product lemma (`Nat.ModEq` values
  multiply the way `mod_eq_add` says they add) — NOT confirmed present;
  likely needs a `prodRange`-indexed induction of its own.
- A "product of the per-term signs equals `(-1)^gaussNegCount`" lemma,
  connecting `countRange`'s counting predicate to a literal `(-1)` product —
  genuinely new, no existing analogue found.
- `gcd (m!) pp = 1` (from `pp` prime, `m < pp`) to cancel `m!` — likely
  reachable via `coprime_of_lt_prime` applied inductively over the factors
  of `m!`, or a dedicated `Nat`-factorial-coprimality lemma; not checked
  this session.
- A Nat/Int carrier bridge: `leastResidue`/`gaussNegCount`/`gaussFold` are
  `Nat`-typed; `Int.prodRange`/`Int.prodRange_permute` are `Int`-typed. The
  bridge itself (`Nat`-to-`Int` casts, and the fact that `Int` congruence at
  a nonnegative value agrees with the `Nat` `modEq`) is real work, not
  bookkeeping — `int_prelude/nat_abs.rs` is the likely home for the
  supporting lemmas, not yet checked against this specific need.

This remains a materially larger, multi-lemma construction than piece 2,
genuinely deserving its own session, exactly as ADR-0970 judged.

## Verification

- `cargo check -p axeyum-lean-kernel --lib` — clean.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 252 passed, 0
  failed (nonzero count confirmed; up from 250 before this session).
- `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.
- `cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint
  -- least_residue_injective_of_coprime` — footprint `0`.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — PASS,
  `held_out=146`, `artifacts/autogenesis/` untouched this session.
- No fact-ledger entries added this session (kernel declarations only). No
  collision with `F:nat-gauss-lemma` (a distinct, pre-existing divisibility
  cancellation theorem in `lcm.rs`) — the new name
  `Nat.least_residue_injective_of_coprime` is unambiguous and was checked
  against the full source tree and `artifacts/facts/` before landing.
