# Lane: gauss-pairing-lemma — Gauss's-lemma connecting theorem (piece 2, injectivity half)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, gauss-pairing-lemma, 2026-08-31).** Full
details in ADR-1015. Verified ADR-0990's simplified route against
`origin/main` before starting.

Landed this session:

- `Nat.least_residue_ne_zero_of_coprime` (`nat_prelude/gauss_lemma.rs`) --
  the one lemma ADR-0990 flagged as genuinely absent. Axiom footprint 0.
- `Nat.gaussFold` (definition) + `Nat.gauss_fold_injective_of_coprime` --
  the signed-fold self-map's injectivity on `[1, m]`, by cases on the two
  indices' signs. The domain restriction to `Le · m` is load-bearing,
  checked by hand: unrestricted to `[1, pp)` the fold is exactly 2-to-1
  (`k` and `pp - k` always collide at `a := 1`). Same-sign closes via piece
  1 (`least_residue_injective_of_coprime`, `gauss-lemma-connecting-b`
  lane), directly or after cancelling a shared `sub pp (·)` via
  `add_sub_cancel_of_le` + `add_right_cancel` (no dedicated subtraction-
  cancellation lemma exists in the tree, confirmed absent). Opposite-sign
  is vacuous via a modular-arithmetic contradiction
  (`mod_eq_add`/`mod_eq_cancel`/`mod_eq_self_of_lt`). Axiom footprint 0.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::`: 258 passed, 0
  failed (up from 256 at session start).

**Not built this session, precisely sized in ADR-1015:**

1. `Nat.gauss_fold_in_range` (`MapsInto`-shaped range bound: `gaussFold`
   stays in `[1, m]`). Needs ONE new arithmetic fact not yet in the tree --
   `div (succ (mul 2 m)) 2 = m` -- route sketched (via `add_mul_div_left` +
   an `add_comm` bridge to match `succ`'s shape), ~20-30 lines, not built.
2. The 0-indexed shift wrapper `Int.prodRange_permute` actually needs
   (`σ(j) := pred (gaussFold pp a (succ j))`, `InjectiveOn`/`MapsInto` on
   `[0, m)`) -- routine composition of (1) and this session's injectivity
   theorem via `succ_pred_of_pos`/`succ_injective`, both confirmed present.
3. Piece 3 (product cancellation, Nat/Int carrier bridge) -- unchanged from
   ADR-0990, genuinely larger than pieces 1+2 combined.

Verification this session: `cargo check -p axeyum-lean-kernel --lib`
(clean); `cargo test -p axeyum-lean-kernel --lib nat_prelude::` (258
passed, 0 failed, up from 256); `cargo run --release -p axeyum-lean-kernel
--example theorem_axiom_footprint -- least_residue_ne_zero_of_coprime`
(footprint `0`); `... -- gauss_fold_injective_of_coprime` (footprint `0`);
`python3 scripts/check-autogenesis-holdout-isolation.py` (PASS,
`held_out=146`, `artifacts/autogenesis/` untouched, checked before and
after).

**Hardest step this session**: the opposite-sign vacuity argument --
proving `k + k' = 0` from a modular congruence needed bounding `k + k' <
pp` via `k, k' ≤ m` and `mul 2 m < pp`, which in turn needed `mul 2 m = add
m m` built from scratch (`Nat.mul` recurses on its RIGHT argument, so `mul
2 m` does not reduce for symbolic `m` and no existing lemma states the
identity directly) -- a small detour that was not in ADR-0990's original
sizing but cost only ~15 lines once identified.

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-pairing-lemma | `Nat.least_residue_ne_zero_of_coprime` and `Nat.gaussFold`/`Nat.gauss_fold_injective_of_coprime` land axiom-free in `nat_prelude/gauss_lemma.rs` -- the nonzero-residue lemma ADR-0990 flagged absent, and the mathematically hard half (same-sign/opposite-sign case split) of Gauss's-lemma piece 2 (the pairing lemma). `MapsInto` and the 0-indexed shift wrapper `Int.prodRange_permute` needs are precisely sized in ADR-1015 and NOT built this session -- one new arithmetic fact (`div (succ (mul 2 m)) 2 = m`) is the sole missing ingredient. |
