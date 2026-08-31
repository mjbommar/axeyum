# ADR-1015: Gauss's lemma pairing injectivity lands axiom-free; `MapsInto` and the 0-indexed shift wrapper are precisely sized

Status: accepted
Date: 2026-08-31
Index-summary: `Nat.gauss_fold_injective_of_coprime : ∀ m a k k', gcd a
(succ (mul 2 m)) = 1 -> 0 < k -> Le k m -> 0 < k' -> Le k' m -> gaussFold
(succ (mul 2 m)) a k = gaussFold (succ (mul 2 m)) a k' -> k = k'` lands
axiom-free in `nat_prelude/gauss_lemma.rs` — the mathematically hard half of
ADR-0990's piece 2 (same-sign + opposite-sign-vacuous case split). The
nonzero-residue lemma ADR-0990 flagged as the one missing piece
(`Nat.least_residue_ne_zero_of_coprime`) also lands. `MapsInto` (the range
bound `gaussFold` stays in `[1, m]`) and the 0-indexed shift wrapper
`Int.prodRange_permute` actually needs are NOT built this session; both are
precisely sized below, including the one new arithmetic fact
(`div (succ (mul 2 m)) 2 = m`) the range bound needs and does not yet have
in the tree.

Index-status: accepted

## Context

ADR-0990 re-sized Gauss's lemma's connecting-theorem piece 2 (the pairing
lemma) to: build the signed-fold self-map `gaussFold` and show it is
`InjectiveOn`/`MapsInto` on the 0-indexed range `[0, m)`, which
`Int.prodRange_permute` consumes directly — no separate bijection or
partner-index construction needed. It flagged one lemma as genuinely absent
from the tree (`leastResidue pp a k ≠ 0` for `0 < k < pp` under
coprimality) and estimated the rest as checkable against existing
signatures.

This session verified ADR-0990's citations against `origin/main` before
starting (`Nat.least_residue_injective_of_coprime`,
`Nat.gaussNegCountTwoClosedForm`, `Int.prodRange_permute`), then built the
nonzero-residue lemma and the UNSHIFTED injectivity theorem in full. What
remains — the range bound and the 0-indexed shift — is sized here rather
than attempted, per the standing rule that a precise handoff beats a rushed
or half-committed final piece.

## Decision

**Land the nonzero-residue lemma and unshifted injectivity in full; size
the range bound and shift wrapper precisely, do not attempt them this
session.**

### Landed: `Nat.least_residue_ne_zero_of_coprime`

`∀ pp a k, gcd a pp = 1 → 0 < k → k < pp → 0 < leastResidue pp a k`. Route:
assume `leastResidue pp a k = 0` (defeq `mod (a*k) pp = 0`);
`Nat.dvd_iff_mod_eq_zero`'s reverse direction gives `pp ∣ a*k`;
`Nat.gauss_lemma` (the pre-existing, unrelated Euclid-cancellation theorem,
**not** `F:nat-gauss-lemma` and **not** this file's own target — see
`nat_prelude/lcm.rs`) cancels the coprime factor `a` (after flipping
`gcd a pp = 1` to `gcd pp a = 1` via `gcd_comm`) to `pp ∣ k`;
`Nat.le_of_dvd`/`Nat.lt_of_le_of_lt`/`Nat.lt_irrefl` (the identical
contradiction shape `bezout.rs` already uses) close it against `k < pp`.

**Axiom footprint** (`theorem_axiom_footprint`):
`Nat.least_residue_ne_zero_of_coprime` = 0.

### Landed: `Nat.gaussFold` and `Nat.gauss_fold_injective_of_coprime`

`Nat.gaussFold pp a k := if gaussSignNeg pp a k then sub pp (leastResidue
pp a k) else leastResidue pp a k` — a plain non-recursive triple-lambda
over `bool_select_nat`, the same shape `Nat.leastResidue` uses.

`Nat.gauss_fold_injective_of_coprime : ∀ m a k k', gcd a (succ (mul 2 m)) =
1 → 0 < k → Le k m → 0 < k' → Le k' m → gaussFold (succ (mul 2 m)) a k =
gaussFold (succ (mul 2 m)) a k' → k = k'`.

**The domain restriction to `Le · m` is load-bearing, checked by hand
before writing any proof term**: unrestricted to the full range `[1, pp)`,
`gaussFold` is exactly 2-to-1 — at `a := 1`, `gaussFold pp 1 k = gaussFold
pp 1 (pp - k)` for every `k ∈ [1, m]`, since `leastResidue pp 1 k = k`
directly and the two residues `k`, `pp - k` fold to the same value from
opposite sides of the sign threshold. So the "opposite-sign is impossible"
half of the case split is a real fact about the restricted domain, not a
convenience.

Route, by cases on `gaussSignNeg pp a k`/`gaussSignNeg pp a k'`
(`bool_true_or_false`, nested `Or.rec`):

- **Same-sign, identity branch** (`test_k = test_k' = false`): `heq`
  transports directly (via a `Bool.rec` congruence, `bool_congr_nat`) to
  `leastResidue pp a k = leastResidue pp a k'`, closed by
  `Nat.least_residue_injective_of_coprime` (piece 1, ADR-0990).
- **Same-sign, negative branch** (`test_k = test_k' = true`): `heq`
  transports to `sub pp lr_k = sub pp lr_k'`. `add_sub_cancel_of_le` at
  each side (needing `Le lr_k pp`/`Le lr_k' pp`, from `Nat.mod_lt` weakened
  by a small `le_of_lt` helper) plus `Nat.add_right_cancel` recovers
  `lr_k = lr_k'` — **no dedicated subtraction-cancellation lemma exists in
  the tree** (confirmed absent, matching ADR-0990's own note), so this
  route reconstructs it from `add_sub_cancel_of_le` rather than needing a
  new primitive. Then piece 1 closes it.
- **Opposite-sign** (`test_k = true, test_k' = false` or the mirror):
  vacuous. `sub pp lr_k = lr_j` forces `lr_k + lr_j = pp`
  (`add_sub_cancel_of_le` + substitution); `Nat.mod_eq_add` combines
  `modEq pp (a*k) lr_k`/`modEq pp (a*j) lr_j` into `modEq pp (a*(k+j)) pp`;
  `Nat.mod_eq_zero_of_dvd` at `pp ∣ pp` (`Nat.dvd_refl`) plus
  `Nat.mod_eq_trans` gives `modEq pp (a*(k+j)) 0`; `Nat.mod_eq_cancel`
  cancels the coprime factor `a` (via a `mul_zero` bridge) to
  `modEq pp (k+j) 0`. Since `k + j ≤ m + m` (`add_le_add_left`/`_right` +
  `le_trans`) and `m + m = mul 2 m` (`succ_mul` + `one_mul`, a small local
  helper — `Nat.mul` recurses on its RIGHT argument so `mul 2 m` does not
  reduce for symbolic `m`) and `mul 2 m < pp` by construction
  (`Nat.lt_succ_of_le`), `k + j < pp`, so `Nat.mod_eq_self_of_lt` collapses
  `modEq pp (k+j) 0` to the literal equation `k + j = 0`
  (`Nat.zero_mod` on the other side). `Nat.add_eq_zero` gives `k = 0`,
  contradicting `0 < k` via `Nat.lt_irrefl`.

Every lemma name this route depends on was checked present with the stated
signature against the tree before use — `mod_lt`, `add_sub_cancel_of_le`,
`add_right_cancel`, `mod_eq_add`, `mod_eq_zero_of_dvd`, `dvd_refl`,
`left_distrib`, `mul_zero`, `lt_two_mul_of_pos`, `lt_succ_of_le`,
`add_le_add_left`/`add_le_add_right`, `le_trans`, `zero_mod`, `add_eq_zero`,
`lt_irrefl` — none needed to be built new; only two small local helpers
(`two_mul_eq_add`, `le_of_lt`) were routine compositions of existing
lemmas, not new primitives.

**Axiom footprint** (`theorem_axiom_footprint`):
`Nat.gauss_fold_injective_of_coprime` = 0.

**Verification**: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` —
258 passed, 0 failed (up from 256 at session start), including the
environment-derived coverage assertion
(`every_nat_declaration_is_checked_and_axiom_free`) and a new concrete
instantiation test (`gauss_fold_computes_the_signed_representative_and_is_
injective_at_pp_seven`) checking both the definitions' computed values at
`pp := 7, a := 2` (fold values `2, 3, 1`, pairwise distinct by kernel
reduction) and a fully-applied instance of the theorem itself — per this
repository's standing rule that a symbolic accept needs a concrete check
too, since numerals reduce and reduction can hide a defeq-shaped gap a
purely symbolic proof would not expose.

## What remains — precisely sized, NOT built this session

`Int.prodRange_permute`'s actual hypotheses (`InjectiveOn σ n`,
`MapsInto σ n` for a self-map `σ : Nat → Nat` of `[0, n)`) still need two
more pieces layered on top of what landed:

### 1. The range bound (`gaussFold` stays in `[1, m]`)

`Nat.gauss_fold_in_range : ∀ m a k, gcd a (succ (mul 2 m)) = 1 → 0 < k →
Le k m → And (0 < gaussFold (succ (mul 2 m)) a k) (Le (gaussFold (succ (mul
2 m)) a k) m)`.

By cases on `gaussSignNeg pp a k` again:

- **Not negative** (`false`, fold = `leastResidue pp a k`): positivity is
  `Nat.least_residue_ne_zero_of_coprime` (this session, needs `k < pp`,
  derivable from `Le k m` + `Lt m pp` exactly as
  `gauss_fold_injective_of_coprime`'s proof already does — that derivation
  is reusable verbatim). The upper bound `leastResidue pp a k ≤ m` follows
  from `gaussSignNeg pp a k = false`, i.e. `leastResidue pp a k < succ (div
  pp 2)` (`Nat.ble_eq_false_of_lt`'s converse direction — check the exact
  name; ADR-0990 named this the same way), i.e. `leastResidue pp a k ≤ div
  pp 2`. **This needs `div pp 2 = m`, which is NOT yet in the tree** (see
  below) — the one new arithmetic fact this piece requires.
- **Negative** (`true`, fold = `sub pp (leastResidue pp a k)`): positivity
  needs `leastResidue pp a k < pp` (`Nat.mod_lt`, already used above) so
  the truncated `sub` does not floor to 0. The upper bound `sub pp
  (leastResidue pp a k) ≤ m` follows from `gaussSignNeg pp a k = true`,
  i.e. `leastResidue pp a k ≥ succ (div pp 2)`, i.e. (again needing
  `div pp 2 = m`) `leastResidue pp a k ≥ succ m`, so
  `pp - leastResidue pp a k ≤ pp - succ m = 2m+1 - (m+1) = m` — a
  `Nat.sub`-monotonicity argument (`Nat.sub_le_sub_left`-shaped; check the
  exact name) once the bound on `leastResidue` is in hand.

**The one new fact needed: `Nat.div (succ (mul 2 m)) 2 = m`.** Checked
absent from the tree (grepped for `div_succ_two_mul`/`half_of_odd`/
`div_odd` and near-neighbours; `gauss_neg_count_two_closed_form`'s own
`div m 2` is a different quantity — the half of `m`, not the half of `pp`).
Route, checked against existing signatures but not built:
`Nat.add_mul_div_left : ∀ x z {y}, 0 < y → (x+y*z)/y = x/y+z` at
`x := 1, z := m, y := 2` gives `(1 + 2*m)/2 = 1/2 + m`; `1/2 = 0` closes by
`Eq.refl` (both concrete small numerals, well under the unary-numeral cost
cliff); the remaining gap is bridging `add 1 (mul 2 m)` (this lemma's LHS
shape) to `succ (mul 2 m)` (`pp`'s actual shape) — `Nat.add_comm` gives
`add 1 (mul 2 m) = add (mul 2 m) 1`, and `add (mul 2 m) 1` **is** defeq to
`succ (mul 2 m)` (literal `1` on the right, so `Nat.add`'s right-recursion
fires — the "symbolic side left, literal side right" rule from `CLAUDE.md`
applies to the BRIDGING step even though the target lemma itself puts the
literal on the left). Estimated ~20-30 lines, structurally routine once
written out.

### 2. The 0-indexed shift wrapper

`Int.prodRange_permute` needs a self-map of `[0, m)`, not `[1, m]`. Define
`σ(j) := pred (gaussFold pp a (succ j))` and derive:

- `Nat.gauss_fold_shift_maps_into : MapsInto σ m` — from
  `gauss_fold_in_range` at `k := succ j` (needs `0 < succ j` trivially,
  `Le (succ j) m` from `Lt j m`) giving `1 ≤ gaussFold(...) ≤ m`, then
  `pred` lands in `[0, m)`: `Nat.pred_lt_pred`-shaped monotonicity, or
  directly `Le (pred x) (pred m)` from `Le x m` plus `pred m = m - 1 < m`
  when `m > 0` (and `m = 0` makes the domain empty, `MapsInto` on `zero`
  vacuous — check whether the induction needs this case separately).
- `Nat.gauss_fold_shift_injective_on : InjectiveOn σ m` — from
  `gauss_fold_injective_of_coprime` at `k := succ i, k' := succ i'`, using
  `Nat.succ_pred_of_pos` (`Lt zero n → Eq n (succ (pred n))`, already in
  the tree) on both sides to recover `gaussFold(succ i) = gaussFold(succ
  i')` from `pred(gaussFold(succ i)) = pred(gaussFold(succ i'))`, then
  `Nat.succ_injective` to strip the outer `succ i = succ i' → i = i'`.

Neither piece needs new machinery beyond what is already cited; both are
routine compositions once the range bound (piece 1 above) exists, since
`succ_pred_of_pos` is the only load-bearing new citation and it is already
confirmed present. Estimated comparable to or somewhat smaller than this
session's injectivity proof, since the hard case-split content is already
built and this is bookkeeping on top of it.

## What remains — piece 3, unchanged from ADR-0970/ADR-0985/ADR-0990

Once the shift wrapper lands, piece 3 (the product-cancellation argument
connecting `gaussNegCount` to `a^m mod pp` via `Int.prodRange_permute`) is
unchanged from ADR-0990's sizing — genuinely larger than pieces 1+2
combined, and not attempted or re-sized this session.

## Verification

- `cargo check -p axeyum-lean-kernel --lib` — clean.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 258 passed, 0
  failed.
- `cargo run --release -p axeyum-lean-kernel --example
  theorem_axiom_footprint -- least_residue_ne_zero_of_coprime` — footprint
  `0`.
- `cargo run --release -p axeyum-lean-kernel --example
  theorem_axiom_footprint -- gauss_fold_injective_of_coprime` — footprint
  `0`.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — PASS,
  `held_out=146`, `artifacts/autogenesis/` untouched this session (checked
  before and after).
- No fact-ledger entries added this session (kernel declarations only).
  `Nat.gaussFold`/`Nat.gauss_fold_injective_of_coprime`/
  `Nat.least_residue_ne_zero_of_coprime` checked against the full source
  tree and `artifacts/facts/` before landing — no collision with
  `F:nat-gauss-lemma` (the distinct, pre-existing divisibility-cancellation
  theorem in `lcm.rs`) or any other existing name.
