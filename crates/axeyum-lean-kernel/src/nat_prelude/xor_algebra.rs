//! `Nat.eq_of_testBit_eq` — the general "same bits imply the same number"
//! extensionality lemma, built toward piece 4 of the 4 pieces
//! `docs/plan/status/260-nat-lt-xor-cases.md` named as blocking
//! `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.xor_assoc`,
//! `Nat.xor_xor_cancel_left`/`_right`, `Nat.xor_ne_zero_iff`). See
//! `docs/plan/status/263-nat-testbit-xor.md` for piece 1 (`Nat.testBit_xor`,
//! landed), `docs/plan/status/264-nat-xor-algebra.md` for the lane that
//! landed `Nat.eq_of_testBit_eq`/`Nat.xor_assoc` and diagnosed the `y <= 1`
//! restriction below, `docs/plan/status/268-nat-xor-cancel.md` for the
//! lane that closed `Nat.xor_xor_cancel_left`/`_right` using it, and
//! `docs/plan/status/270-nat-xor-ne-zero.md` for the lane that closed
//! `Nat.xor_ne_zero_iff` — the last of piece 4's four sub-targets, now ALL
//! declared in this file. See "`Nat.xor_ne_zero_iff`" below for its route.
//!
//! # The intended route: `testBit_xor` + extensionality, not fuel induction
//!
//! `docs/plan/status/260-…`'s own land_assoc-transport warning is moot for
//! this route: `xor_assoc`/`xor_xor_cancel_left`/`xor_ne_zero_iff` do not
//! need any zero-propagation lemma at all if built THIS way. `Nat.testBit_xor`
//! (piece 1) reduces a statement about `xor` VALUES to a statement about
//! individual BITS, where `xor_bit` is a two-`Bool`-valued combine,
//! exhaustively case-splittable (`Bool.rec`, at most 2-3 levels deep — see
//! the handoff doc for the truth-table sizing). Once every bit of two
//! `xor`-built values is shown to agree, THIS file's
//! [`declare_eq_of_test_bit_eq`] — "same bits imply the same number" — turns
//! that back into a value-level equation. Neither `land_assoc`'s
//! zero-propagation lemma nor any fuel-level case analysis on `bitwiseAux`
//! is needed for any of the three targets, on this route.
//!
//! # `Nat.eq_of_testBit_eq` --- the extensionality lemma (LANDED)
//!
//! ```text
//! Nat.eq_of_testBit_eq : ∀ m n, (∀ i, Eq (testBit m i) (testBit n i)) → Eq m n
//! ```
//!
//! Not previously in this prelude: `binary.rs`'s `Nat.zero_of_testBit_eq_zero`
//! is the ONE-SIDED case ("all bits zero ⟹ the number is zero"), not the
//! general two-value form. Proved by an induction on a FUEL `k` bounding `m`
//! (the same "generalize over an outer bound, induct on the fuel" device
//! `rec_agreement.rs`'s fuel-irrelevance lemmas and `testbit_bitwise.rs`'s
//! own bridge use), with motive
//!
//! ```text
//! P(k) := ∀ n, ∀ m, Le m k → (∀ i, testBit m i = testBit n i) → Eq m n
//! ```
//!
//! - **Base** (`k = 0`): `Le m 0` forces `m = 0` (`le_antisymm` against
//!   `zero_le`); the bit hypothesis at `m := 0` then forces every bit of `n`
//!   to be `0` too (via `test_bit_of_zero` and `zero_of_test_bit_eq_zero`),
//!   so `n = 0 = m`. This same derivation --- [`zero_forces_eq`] --- closes
//!   BOTH the outer base case and the inner `m = 0` sub-case of the step
//!   below, parameterized over a proof `Eq x 0` rather than over `x` being
//!   literally the numeral `0`.
//! - **Step** (`k = succ pk`): case-splits on `m` (`cases_zero_succ`), folding
//!   the `Le`/bit hypotheses into the PER-CASE motive rather than
//!   pre-introducing them (`cases_zero_succ`'s own documented device for a
//!   hypothesis a caller wants specialized per branch). At `m = succ pm`:
//!   the bit-0 hypothesis gives `mod (succ pm) 2 = mod n 2` (`testBit _ 0` is
//!   `refl`-defeq to `mod _ 2`); the bit-`(succ j)` hypotheses, for every
//!   `j`, give `∀ j, testBit (half (succ pm)) j = testBit (half n) j`
//!   (`testBit _ (succ j)` is `refl`-defeq to `testBit (_ / 2) j`), which is
//!   exactly the IH's hypothesis at `(half (succ pm), half n)`, bounded via
//!   `half_le_predecessor_of_succ` (`rec_agreement.rs`). The IH gives
//!   `half (succ pm) = half n`; combined with the bit-0 equation and the
//!   `n = 2*(n/2) + n%2` reconstruction (`div_mod_exec`/`and_left`, the same
//!   identity `testbit_bitwise.rs`'s `div_two_mul_add_of_lt` is built from
//!   the OTHER half of) on both sides, this gives `succ pm = n`.
//!
//! Instantiating the fuel bound at `k := m` itself (`le_refl`) turns
//! `P(m)` directly into the public two-argument statement.
//!
//! # `xor_bit`'s two restriction regimes
//!
//! `Nat.xor_assoc`'s `xor_bit` associativity holds for ALL `x, y, z :
//! Nat` (not merely bits in `{0, 1}`), but `Nat.xor_xor_cancel_left`/
//! `_right`'s per-bit cancel identity `xor_bit x (xor_bit x y) = y` is FALSE
//! for a general `Nat` `y` (only `y in {0, 1}`), which is why closing those
//! two needed an extra `y <= 1` round-trip lemma ([`round_trip_le_one`]) that
//! `xor_assoc` never needed.
//!
//! # `Nat.xor_ne_zero_iff` — via `mt` twice, not via an `Iff` of `Eq`
//!
//! ```text
//! Nat.xor_ne_zero_iff : ∀ a b, Iff (Not (Eq (xor a b) 0)) (Not (Eq a b))
//! ```
//!
//! Matches Lean core's `Nat.xor_ne_zero_iff : x ^^^ y ≠ 0 ↔ x ≠ y`, read
//! directly from the pinned Batteries checkout
//! (`Batteries/Data/Nat/Bitwise/Lemmas.lean:68`) rather than trusted from
//! prose — `xor_ne_zero_iff`/`xor_xor_cancel_left`/`xor_xor_cancel_right`
//! all live there (cited, not defined, in Mathlib's own `Bitwise.lean`),
//! confirming the prior lane's "Lean core, not Mathlib-authored" reading.
//!
//! The natural-looking route — build `Nat.xor_eq_zero_iff : Eq (xor a b) 0
//! ↔ Eq a b` first, then negate both sides — needs an extra `Iff`
//! not-congruence combinator this prelude does not have. `mt` (modus
//! tollens, `Π a b, (a → b) → (b → False) → (a → False)`, already in the
//! logic prelude and unused until now) skips that: partially applying `mt`
//! with just the two propositions and a DIRECTION lemma gives a complete
//! `Not`-to-`Not` implication with no further wrapping needed —
//! `mt (Eq a b) (Eq (xor a b) 0) f : Not (Eq (xor a b) 0) → Not (Eq a b)`
//! for `f : Eq a b → Eq (xor a b) 0`, and symmetrically for the other
//! direction. Two small directional corollaries feed it:
//!
//! - **`Eq (xor a b) 0 → Eq a b`** (the `mpr` side) — does NOT need
//!   [`declare_xor_xor_cancel_left`]/`_right` at all, confirming
//!   `docs/plan/status/268-nat-xor-cancel.md`'s handoff: per bit,
//!   `Nat.testBit_xor` plus the hypothesis gives `Eq (xor_bit (testBit a i)
//!   (testBit b i)) 0`, and a NEW per-bit fact
//!   ([`xor_bit_eq_zero_implies_eq`]) closes it to `Eq (testBit a i)
//!   (testBit b i)` given both are `<= 1` (`Nat.testBit_le_one`) — reusing
//!   [`round_trip_le_one`] rather than re-deriving a bound lemma.
//!   `Nat.eq_of_testBit_eq` turns the per-bit result back into `Eq a b`.
//! - **`Eq a b → Eq (xor a b) 0`** (the `mp` side) — via a NEW
//!   `Nat.xor_self`-shaped argument ([`xor_self`]): `congrArg (xor a ·)` on
//!   the hypothesis gives `Eq (xor a a) (xor a b)`, and a per-bit
//!   self-cancellation-to-zero fact ([`xor_bit_self_zero`], built from a
//!   NEW `Bool`-level `xor_fn x x = false` fact, [`bool_xor_self`]) plus
//!   `Nat.eq_of_testBit_eq` gives `Eq (xor a a) 0`.
//!
//! Confirmed by a Python truth-table simulation before any Rust was written:
//! `xor_fn a b = false → a = b` holds unconditionally over all 4 `Bool`
//! pairs. The `a = false` branch closes for ANY `b` by `bool_symm` on the
//! (defeq-reduced) hypothesis; the `a = true, b = true` branch is `refl`;
//! the `a = true, b = false` branch needs no ex-falso at all, because there
//! the hypothesis (`Eq true false`, since `xor_fn true false` reduces to
//! `true`) already IS the goal (`Eq true false`) — the identity function.
//! So no `false_true_elim` is needed anywhere in this file.
//!
//! # Codomain / mirror check
//!
//! No `ml430` fact for any of `xor_assoc`/`xor_xor_cancel_left`/
//! `xor_ne_zero_iff` was found in the ledger (`artifacts/facts/` has no
//! `F-ml430-nat-xor-*` file). `Nat.xor`, `Nat.testBit`, `Le`, `Eq` all match
//! Mathlib's codomains for these specific statements (no `Bool`-valued
//! `testBit` involved, unlike the six sibling mirrors the `testBit`
//! codomain mismatch blocked), so whichever of them land will be new local
//! facts (`F:nat-xor-assoc`, `F:nat-xor-xor-cancel-left`, …), not `ml430`
//! mirrors of anything pre-registered. `Nat.eq_of_testBit_eq` ITSELF has no
//! `ml430` mirror either (no such general extensionality statement appears
//! in `Mathlib/Data/Nat/Bitwise.lean` at the pinned commit under this or a
//! related name) and is registered as its own new local fact.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use super::rec_agreement::half_le_predecessor_of_succ;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// `Nat.eq_of_testBit_eq` -- same bits imply the same number.
// ============================================================================

/// `Eq x zero ⊢ (∀ i, Eq (testBit x i) (testBit n i)) → Eq x n`. Shared by
/// the outer base case (`x := m`, `hx0` from `le_antisymm`) and the step
/// case's `m = 0` sub-case (`x := zero` literally, `hx0 := refl`).
///
/// Proof: `hx0` transports the bit hypothesis to `∀ i, testBit zero i =
/// testBit n i`; `test_bit_of_zero` gives `testBit zero i = 0`, so every bit
/// of `n` is `0`, and `zero_of_test_bit_eq_zero` closes `n = 0`; `x = 0 = n`
/// by `trans`.
fn zero_forces_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    n: ExprId,
    hx0: ExprId,
    bits_hyp: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();

    let n_bits_zero = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tb_x_i = d.const_app(p.test_bit, &[x, i]);
        let tb_n_i = d.const_app(p.test_bit, &[n, i]);
        let h_i = d.apply(bits_hyp, &[i]); // Eq tb_x_i tb_n_i
        let tb_zero_i = d.const_app(p.test_bit, &[zero, i]);
        let congr_x0 = d.congr(x, zero, hx0, &|d, y| {
            let ii = i;
            d.const_app(p.test_bit, &[y, ii])
        });
        let tb0_eq_zero = d.lemma(p.test_bit_of_zero, &[i]);
        let tb_x_eq_zero = d.trans(tb_x_i, tb_zero_i, zero, congr_x0, tb0_eq_zero);
        let tb_n_eq_tbx = d.symm(tb_x_i, tb_n_i, h_i);
        let tb_n_eq_zero = d.trans(tb_n_i, tb_x_i, zero, tb_n_eq_tbx, tb_x_eq_zero);
        d.lam_fv(i_fv, nat, tb_n_eq_zero)
    };
    let n_eq_zero = d.lemma(p.zero_of_test_bit_eq_zero, &[n, n_bits_zero]);
    let zero_eq_n = d.symm(n, zero, n_eq_zero);
    d.trans(x, zero, n, hx0, zero_eq_n)
}

/// `Eq x (add (mul two (div x two)) (mod x two))` for any `x` --- the
/// Euclidean reconstruction identity, the equation half of
/// `div_mod_exec`'s `And`. `and_left` on the same `divMod` witness
/// `testbit_bitwise.rs`'s `div_two_mul_add_of_lt` takes its bound half from.
fn reconstruct_div_mod(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let dx = d.div(x, two);
    let rx = d.modulo(x, two);
    let two_dx = d.mul(two, dx);
    let sum = d.add(two_dx, rx);
    let eq_ty = d.eq(x, sum);
    let bound_ty = d.lt(rx, two);
    let h_exec = d.lemma(p.div_mod_exec, &[one, x]);
    and_left(d, eq_ty, bound_ty, h_exec)
}

/// `Nat.eq_of_testBit_eq : ∀ n, ∀ m, (∀ i, Eq (testBit m i) (testBit n i))
/// → Eq m n` --- see the module doc for the fuel induction shape. (Argument
/// order `n` then `m` to keep the induction's own motive, built with `n`
/// captured before the `m`-split, syntactically simple; the PUBLIC-facing
/// order in the theorem's own binders is `m` then `n`, matching every other
/// use site in this file, wired at the very end.)
fn declare_eq_of_test_bit_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let bits_ty_at = |d: &mut NatDev<'_>, mm: ExprId, n: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tb_m = d.const_app(p.test_bit, &[mm, i]);
        let tb_n = d.const_app(p.test_bit, &[n, i]);
        let body = d.eq(tb_m, tb_n);
        d.pi_fv(i_fv, nat, body)
    };

    // motive(k) := ∀ n, ∀ m, Le m k → bits(m, n) → Eq m n
    let motive = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let le_ty = d.le(m, k);
        let bt = bits_ty_at(d, m, n);
        let eqmn = d.eq(m, n);
        let arrow_bt = d.arrow(bt, eqmn);
        let inner = d.arrow(le_ty, arrow_bt);
        let over_m = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(n_fv, nat, over_m)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let zero = d.zero();
        let le_ty = d.le(m, zero);
        let le_fv = d.fresh_fvar();
        let le_hyp = d.kernel().fvar(le_fv);
        let bt = bits_ty_at(d, m, n);
        let bits_fv = d.fresh_fvar();
        let bits_hyp = d.kernel().fvar(bits_fv);

        let zero_le_m = d.lemma(p.zero_le, &[m]);
        let m_eq_zero = d.lemma(p.le_antisymm, &[m, zero, le_hyp, zero_le_m]);
        let eq_final = zero_forces_eq(d, &p, m, n, m_eq_zero, bits_hyp);

        let with_bits = d.lam_fv(bits_fv, bt, eq_final);
        let with_le = d.lam_fv(le_fv, le_ty, with_bits);
        let with_m = d.lam_fv(m_fv, nat, with_le);
        d.lam_fv(n_fv, nat, with_m)
    };

    let step = |d: &mut NatDev<'_>, pk: ExprId, ih: ExprId| -> ExprId {
        // ih : ∀ n, ∀ m, Le m pk → bits(m, n) → Eq m n
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let succ_pk = d.succ(pk);

        let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
            let le_ty = d.le(mm, succ_pk);
            let bt = bits_ty_at(d, mm, n);
            let eqmn = d.eq(mm, n);
            let arrow_bt = d.arrow(bt, eqmn);
            d.arrow(le_ty, arrow_bt)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let le_ty0 = d.le(zero, succ_pk);
            let le_fv = d.fresh_fvar();
            let _le_hyp = d.kernel().fvar(le_fv);
            let bt0 = bits_ty_at(d, zero, n);
            let bits_fv = d.fresh_fvar();
            let bits_hyp = d.kernel().fvar(bits_fv);
            let hx0 = d.refl(zero);
            let eq_final = zero_forces_eq(d, &p, zero, n, hx0, bits_hyp);
            let wb = d.lam_fv(bits_fv, bt0, eq_final);
            d.lam_fv(le_fv, le_ty0, wb)
        };

        let at_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
            let m_succ = d.succ(pm);
            let le_ty_s = d.le(m_succ, succ_pk);
            let le_fv = d.fresh_fvar();
            let le_hyp = d.kernel().fvar(le_fv);
            let bt_s = bits_ty_at(d, m_succ, n);
            let bits_fv = d.fresh_fvar();
            let bits_hyp = d.kernel().fvar(bits_fv);

            let two = d.num(2);
            let half_m = d.div(m_succ, two);
            let half_n = d.div(n, two);

            let half_bits = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let succ_j = d.succ(j);
                let h = d.apply(bits_hyp, &[succ_j]);
                let nat_ty = d.nat_ty();
                d.lam_fv(j_fv, nat_ty, h)
            };

            let half_le_pk = half_le_predecessor_of_succ(d, &p, pm, pk, le_hyp);

            let ih_at = d.apply(ih, &[half_n]);
            let ih_at = d.apply(ih_at, &[half_m]);
            let ih_at = d.apply(ih_at, &[half_le_pk]);
            let half_eq = d.apply(ih_at, &[half_bits]);

            let zero_i = d.zero();
            let low_bit_eq = d.apply(bits_hyp, &[zero_i]);

            let m_mod = d.modulo(m_succ, two);
            let n_mod = d.modulo(n, two);
            let two_half_m = d.mul(two, half_m);
            let two_half_n = d.mul(two, half_n);
            let mid_m = d.add(two_half_m, m_mod);
            let mid_shared = d.add(two_half_n, m_mod);
            let mid_n = d.add(two_half_n, n_mod);

            let step1 = d.congr(half_m, half_n, half_eq, &|d, x| {
                let two = d.num(2);
                let t = d.mul(two, x);
                let mm = m_mod;
                d.add(t, mm)
            });
            let step2 = d.congr(m_mod, n_mod, low_bit_eq, &|d, x| {
                let hn = half_n;
                let two = d.num(2);
                let t = d.mul(two, hn);
                d.add(t, x)
            });
            let combined = d.trans(mid_m, mid_shared, mid_n, step1, step2);

            let recon_m = reconstruct_div_mod(d, &p, m_succ);
            let recon_n = reconstruct_div_mod(d, &p, n);
            let recon_n_symm = d.symm(n, mid_n, recon_n);
            let (_, eq_final) = d.chain(
                m_succ,
                &[(mid_m, recon_m), (mid_n, combined), (n, recon_n_symm)],
            );

            let wb = d.lam_fv(bits_fv, bt_s, eq_final);
            d.lam_fv(le_fv, le_ty_s, wb)
        };

        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let case_proof = cases_zero_succ(d, m, &motive_m, &at_zero, &at_succ);
        let with_m = d.lam_fv(m_fv, nat, case_proof);
        d.lam_fv(n_fv, nat, with_m)
    };

    // Public theorem, order (m, n): instantiate the fuel at k := m via
    // le_refl, then apply at (n' := n, m' := m).
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let bits_fv = d.fresh_fvar();
    let bits_hyp = d.kernel().fvar(bits_fv);

    let proof_fn = d.induct(&motive, &base, &step, m);
    let le_refl_m = d.lemma(p.le_refl, &[m]);
    let inst = d.apply(proof_fn, &[n]);
    let inst = d.apply(inst, &[m]);
    let inst = d.apply(inst, &[le_refl_m]);
    let final_proof = d.apply(inst, &[bits_hyp]);

    let bits_ty_outer = bits_ty_at(d, m, n);
    let eqmn = d.eq(m, n);
    let value = {
        let wb = d.lam_fv(bits_fv, bits_ty_outer, final_proof);
        let wn = d.lam_fv(n_fv, nat, wb);
        d.lam_fv(m_fv, nat, wn)
    };
    let ty = {
        let arrow1 = d.arrow(bits_ty_outer, eqmn);
        let over_n = d.pi_fv(n_fv, nat, arrow1);
        d.pi_fv(m_fv, nat, over_n)
    };
    d.declare_theorem(p.eq_of_test_bit_eq, ty, value)
}

// ============================================================================
// `xor_bit` algebra: `xor_bit`'s value depends on its arguments only through
// whether each equals `1`, so its algebraic laws hold for ALL `x, y, z :
// Nat`, verified by a Python truth-table simulation before any Rust was
// written (`xor` associates, confirmed over all 8 Boolean triples).
// ============================================================================

/// `bool_select_nat cond 1 0` --- the decode `xor_bit` builds its result
/// with, factored out so [`xor_bit_assoc`] can reason about it directly.
fn digitize(d: &mut NatDev<'_>, cond: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    d.bool_select_nat(cond, one, zero)
}

/// `Bool.rec` deciding `b`, generic over an arrow-shaped motive (the same
/// device `combined_lt_two`/`bool_select_nat_same` use inline in
/// `testbit_bitwise.rs`, promoted here since this file needs it repeatedly).
fn cases_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    b: ExprId,
    motive: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_false: &dyn Fn(&mut NatDev<'_>) -> ExprId,
    at_true: &dyn Fn(&mut NatDev<'_>) -> ExprId,
) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let motive_lam = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = motive(d, c);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let case_false = at_false(d);
    let case_true = at_true(d);
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive_lam, case_false, case_true, b])
}

/// `Eq (beq (digitize cond) 1) cond`, for any `Bool` `cond` --- the
/// round-trip recovering the decision from the `Nat`-decoded value. Two
/// cases, both `refl` (`digitize` at a literal `cond` iota-reduces, then
/// `beq` of two literals iota-reduces).
fn beq_digitize_one(d: &mut NatDev<'_>, p: &NatPrelude, cond: ExprId) -> ExprId {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, c: ExprId| -> ExprId {
        let one = d.num(1);
        let sel = digitize(d, c);
        let lhs = d.beq(sel, one);
        d.bool_eq(lhs, c)
    };
    let at_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        let one = d.num(1);
        let sel = digitize(d, false_);
        let lhs = d.beq(sel, one);
        // `lhs` (a `Bool` value, `beq (digitize false) 1`) reduces to
        // `false_` by iota+iota; the reflexivity witness needed is of
        // `lhs`, NOT of `sel` (`sel` is `Nat`-typed -- `Eq.refl Bool sel`
        // would be ill-typed).
        d.bool_refl(lhs)
    };
    let at_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        let one = d.num(1);
        let sel = digitize(d, true_);
        let lhs = d.beq(sel, one);
        d.bool_refl(lhs)
    };
    cases_bool(d, &p, cond, &motive, &at_false, &at_true)
}

/// `Eq (xor_fn (xor_fn a b) c) (xor_fn a (xor_fn b c))`, for all `Bool` `a,
/// b, c`. Splitting on `a` alone closes `a = false` for ANY `b, c` by
/// `refl` (`xor_fn false w` reduces to `w` for any `w`, since the outer
/// `Bool.rec` scrutinee is the LITERAL `false`); `a = true` needs one more
/// split on `b`, and `(a, b) = (true, true)` needs a final split on `c`.
fn bool_xor_assoc(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let p = *p;

    let motive_a = |d: &mut NatDev<'_>, aa: ExprId| -> ExprId {
        let xor_ = super::bitwise::xor_fn(d);
        let xab = d.apply(xor_, &[aa, b]);
        let lhs = d.apply(xor_, &[xab, c]);
        let xor_2 = super::bitwise::xor_fn(d);
        let xbc = d.apply(xor_2, &[b, c]);
        let rhs = d.apply(xor_2, &[aa, xbc]);
        d.bool_eq(lhs, rhs)
    };

    let at_a_false = |d: &mut NatDev<'_>| -> ExprId {
        let xor_ = super::bitwise::xor_fn(d);
        let xbc = d.apply(xor_, &[b, c]);
        d.bool_refl(xbc)
    };

    let at_a_true = |d: &mut NatDev<'_>| -> ExprId {
        let motive_b = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
            let true_ = d.bool_true();
            let xor_ = super::bitwise::xor_fn(d);
            let xab = d.apply(xor_, &[true_, bb]);
            let lhs = d.apply(xor_, &[xab, c]);
            let true_2 = d.bool_true();
            let xor_2 = super::bitwise::xor_fn(d);
            let xbc = d.apply(xor_2, &[bb, c]);
            let rhs = d.apply(xor_2, &[true_2, xbc]);
            d.bool_eq(lhs, rhs)
        };
        let at_b_false = |d: &mut NatDev<'_>| -> ExprId {
            // xor_fn true false = true (refl); both sides reduce to
            // xor_fn true c.
            let true_ = d.bool_true();
            let xor_ = super::bitwise::xor_fn(d);
            let xtc = d.apply(xor_, &[true_, c]);
            d.bool_refl(xtc)
        };
        let at_b_true = |d: &mut NatDev<'_>| -> ExprId {
            let motive_c = |d: &mut NatDev<'_>, cc: ExprId| -> ExprId {
                let true_ = d.bool_true();
                let false_ = d.bool_false();
                let xor_ = super::bitwise::xor_fn(d);
                let xab = d.apply(xor_, &[true_, true_]); // reduces to false
                let _ = false_;
                let lhs = d.apply(xor_, &[xab, cc]);
                let true_2 = d.bool_true();
                let xor_2 = super::bitwise::xor_fn(d);
                let xbc = d.apply(xor_2, &[true_2, cc]);
                let true_3 = d.bool_true();
                let rhs = d.apply(xor_2, &[true_3, xbc]);
                d.bool_eq(lhs, rhs)
            };
            let at_c_false = |d: &mut NatDev<'_>| -> ExprId {
                // LHS = xor_fn false false = false.
                // RHS = xor_fn true (xor_fn true false) = xor_fn true true = false.
                let false_ = d.bool_false();
                d.bool_refl(false_)
            };
            let at_c_true = |d: &mut NatDev<'_>| -> ExprId {
                // LHS = xor_fn false true = true.
                // RHS = xor_fn true (xor_fn true true) = xor_fn true false = true.
                let true_ = d.bool_true();
                d.bool_refl(true_)
            };
            cases_bool(d, &p, c, &motive_c, &at_c_false, &at_c_true)
        };
        cases_bool(d, &p, b, &motive_b, &at_b_false, &at_b_true)
    };

    cases_bool(d, &p, a, &motive_a, &at_a_false, &at_a_true)
}

/// `h : Eq Bool a b, f : Bool -> Nat  ⊢  Eq Nat (f a) (f b)` --- the
/// cross-type congruence [`NatOps::congr`] cannot provide: that helper's
/// `eq_motive`/`transport` hardcode `Eq Nat` for the HYPOTHESIS slot too, so
/// a `Bool`-typed `h` (as every intermediate in [`xor_bit_assoc`] is, before
/// `digitize` brings it back to `Nat`) needs `bool_eq_motive`/
/// `bool_transport` instead, with the conclusion built at `Nat`.
fn congr_bool_to_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fx = f(d, x);
        let concl = d.eq(fa, fx);
        let hyp = d.bool_eq(a, x);
        let anon = d.anon_name();
        let inner = d.kernel().lam(anon, hyp, concl, BinderInfo::Default);
        let bool_ty = d.bool_ty();
        d.lam_fv(x_fv, bool_ty, inner)
    };
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Eq (xor_bit (xor_bit x y) z) (xor_bit x (xor_bit y z))`, for all `Nat`
/// `x, y, z` --- lifts [`bool_xor_assoc`] through the round-trip
/// [`beq_digitize_one`]. `xor_bit x y := digitize (xor_fn (beq x 1) (beq y
/// 1))` (`testbit_bitwise.rs`), so `xor_bit (xor_bit x y) z` is, by
/// DEFINITION (`refl`), `digitize (xor_fn (beq (xor_bit x y) 1) (beq z 1))`;
/// the round-trip identifies `beq (xor_bit x y) 1` with `xor_fn bx by`,
/// [`bool_xor_assoc`] identifies the two associated `Bool` combines, and a
/// final `symm` + `refl` lands on `xor_bit x (xor_bit y z)`'s own
/// definitional unfold.
fn xor_bit_assoc(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let bx = d.beq(x, one);
    let by = d.beq(y, one);
    let bz = d.beq(z, one);

    let xy = super::testbit_bitwise::xor_bit(d, x, y);
    let yz = super::testbit_bitwise::xor_bit(d, y, z);
    let beq_xy_one = d.beq(xy, one);
    let beq_yz_one = d.beq(yz, one);

    let xor_ = super::bitwise::xor_fn(d);
    let cond_xy = d.apply(xor_, &[bx, by]);
    let xor_2 = super::bitwise::xor_fn(d);
    let cond_yz = d.apply(xor_2, &[by, bz]);

    let rt_xy = beq_digitize_one(d, &p, cond_xy); // Eq (beq (digitize cond_xy) 1) cond_xy
    let rt_yz = beq_digitize_one(d, &p, cond_yz);
    let assoc_bool = bool_xor_assoc(d, &p, bx, by, bz); // Eq (xor_fn cond_xy bz) (xor_fn bx cond_yz)

    // Left leg: digitize(xor_fn beq_xy_one bz) [start, refl-defeq to
    // xor_bit(xy, z)] -> digitize(xor_fn cond_xy bz) [via rt_xy] ->
    // digitize(xor_fn bx cond_yz) [via assoc_bool].
    let start_l = {
        let xor_ = super::bitwise::xor_fn(d);
        let inner = d.apply(xor_, &[beq_xy_one, bz]);
        digitize(d, inner)
    };
    let mid_l1 = {
        let xor_ = super::bitwise::xor_fn(d);
        let inner = d.apply(xor_, &[cond_xy, bz]);
        digitize(d, inner)
    };
    let mid_l2 = {
        let xor_ = super::bitwise::xor_fn(d);
        let inner = d.apply(xor_, &[bx, cond_yz]);
        digitize(d, inner)
    };
    let step_l1 = congr_bool_to_nat(d, beq_xy_one, cond_xy, rt_xy, &|d, w| {
        let xor_ = super::bitwise::xor_fn(d);
        let bzv = bz;
        let inner = d.apply(xor_, &[w, bzv]);
        digitize(d, inner)
    });
    let xor_cond_xy_bz = {
        let xor_ = super::bitwise::xor_fn(d);
        d.apply(xor_, &[cond_xy, bz])
    };
    let xor_bx_cond_yz = {
        let xor_ = super::bitwise::xor_fn(d);
        d.apply(xor_, &[bx, cond_yz])
    };
    let step_l2 = congr_bool_to_nat(d, xor_cond_xy_bz, xor_bx_cond_yz, assoc_bool, &|d, w| {
        digitize(d, w)
    });

    // Right leg: digitize(xor_fn bx beq_yz_one) [end, refl-defeq to
    // xor_bit(x, yz)] -> digitize(xor_fn bx cond_yz) [via rt_yz].
    let start_r = {
        let xor_ = super::bitwise::xor_fn(d);
        let inner = d.apply(xor_, &[bx, beq_yz_one]);
        digitize(d, inner)
    };
    let step_r1 = congr_bool_to_nat(d, beq_yz_one, cond_yz, rt_yz, &|d, w| {
        let xor_ = super::bitwise::xor_fn(d);
        let bxv = bx;
        let inner = d.apply(xor_, &[bxv, w]);
        digitize(d, inner)
    });

    let (last_l, chain_l) = d.chain(start_l, &[(mid_l1, step_l1), (mid_l2, step_l2)]);
    let step_r1_symm = d.symm(start_r, mid_l2, step_r1);
    d.trans(start_l, last_l, start_r, chain_l, step_r1_symm)
}

/// `Nat.xor_assoc : ∀ a b c, Eq (xor (xor a b) c) (xor a (xor b c))` ---
/// applies [`declare_eq_of_test_bit_eq`]'s extensionality lemma to a
/// per-bit proof built from `Nat.testBit_xor` (applied twice on each side)
/// and [`xor_bit_assoc`].
fn declare_xor_assoc(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.xor_assoc, 3, &|d, values| {
        let (a, b, c) = (values[0], values[1], values[2]);
        let xab = d.const_app(p.xor, &[a, b]);
        let lhs = d.const_app(p.xor, &[xab, c]);
        let xbc = d.const_app(p.xor, &[b, c]);
        let rhs = d.const_app(p.xor, &[a, xbc]);
        let stmt = d.eq(lhs, rhs);

        // bits_hyp : ∀ i, Eq (testBit lhs i) (testBit rhs i)
        let bits_hyp = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);

            // testBit lhs i = xor_bit (testBit xab i) (testBit c i)
            //               = xor_bit (xor_bit (testBit a i) (testBit b i)) (testBit c i)
            let tb_a = d.const_app(p.test_bit, &[a, i]);
            let tb_b = d.const_app(p.test_bit, &[b, i]);
            let tb_c = d.const_app(p.test_bit, &[c, i]);

            let tb_lhs_outer = d.lemma(p.test_bit_xor, &[xab, c, i]); // Eq (testBit lhs i) (xor_bit (testBit xab i) (testBit c i))
            let tb_xab = d.const_app(p.test_bit, &[xab, i]);
            let tb_lhs_inner = d.lemma(p.test_bit_xor, &[a, b, i]); // Eq (testBit xab i) (xor_bit tb_a tb_b)
            let xor_tb_xab_tb_c = super::testbit_bitwise::xor_bit(d, tb_xab, tb_c);
            let xab_bit = super::testbit_bitwise::xor_bit(d, tb_a, tb_b);
            let xor_xor_ab_c = super::testbit_bitwise::xor_bit(d, xab_bit, tb_c);
            let congr_lhs_inner = d.congr(tb_xab, xab_bit, tb_lhs_inner, &|d, w| {
                let tb_c2 = tb_c;
                super::testbit_bitwise::xor_bit(d, w, tb_c2)
            });
            let tb_lhs = d.const_app(p.test_bit, &[lhs, i]);
            let (_, lhs_eq) = d.chain(
                tb_lhs,
                &[
                    (xor_tb_xab_tb_c, tb_lhs_outer),
                    (xor_xor_ab_c, congr_lhs_inner),
                ],
            );

            // testBit rhs i = xor_bit (testBit a i) (testBit xbc i)
            //               = xor_bit (testBit a i) (xor_bit (testBit b i) (testBit c i))
            let tb_rhs_outer = d.lemma(p.test_bit_xor, &[a, xbc, i]); // Eq (testBit rhs i) (xor_bit tb_a (testBit xbc i))
            let tb_xbc = d.const_app(p.test_bit, &[xbc, i]);
            let tb_rhs_inner = d.lemma(p.test_bit_xor, &[b, c, i]); // Eq (testBit xbc i) (xor_bit tb_b tb_c)
            let xor_tb_a_tb_xbc = super::testbit_bitwise::xor_bit(d, tb_a, tb_xbc);
            let xbc_bit = super::testbit_bitwise::xor_bit(d, tb_b, tb_c);
            let xor_a_xor_bc = super::testbit_bitwise::xor_bit(d, tb_a, xbc_bit);
            let congr_rhs_inner = d.congr(tb_xbc, xbc_bit, tb_rhs_inner, &|d, w| {
                let tb_a2 = tb_a;
                super::testbit_bitwise::xor_bit(d, tb_a2, w)
            });
            let tb_rhs = d.const_app(p.test_bit, &[rhs, i]);
            let (_, rhs_eq) = d.chain(
                tb_rhs,
                &[
                    (xor_tb_a_tb_xbc, tb_rhs_outer),
                    (xor_a_xor_bc, congr_rhs_inner),
                ],
            );

            // xor_bit assoc: xor_xor_ab_c = xor_a_xor_bc
            let bit_assoc = xor_bit_assoc(d, &p, tb_a, tb_b, tb_c);

            let (_, bit_eq) = d.chain(tb_lhs, &[(xor_xor_ab_c, lhs_eq), (xor_a_xor_bc, bit_assoc)]);
            let rhs_eq_symm = d.symm(tb_rhs, xor_a_xor_bc, rhs_eq);
            let final_bit_eq = d.trans(tb_lhs, xor_a_xor_bc, tb_rhs, bit_eq, rhs_eq_symm);
            d.lam_fv(i_fv, nat, final_bit_eq)
        };

        let proof = d.lemma(p.eq_of_test_bit_eq, &[lhs, rhs, bits_hyp]);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.xor_xor_cancel_left` / `_right` -- the `y <= 1` round-trip lemma this
// needs is genuinely new work: the natural per-bit cancel identity
// `xor_bit x (xor_bit x y) = y` is FALSE for general `y : Nat` (only for
// `y ∈ {0, 1}`), unlike `xor_bit_assoc`'s identity above, which never needed
// that restriction. Confirmed by a Python truth-table simulation before any
// Rust was written: `xor_bit(3, xor_bit(3, 5)) = 0 != 5`.
// ============================================================================

/// `Eq (digitize (beq y 1)) y`, given `Le y 1` --- the round-trip that
/// recovers `y` ITSELF (not merely the `Bool` decision `beq y 1`) once `y`
/// is known to be a bit. Needed because [`xor_bit_cancel_left`]'s identity
/// is false for general `y`: `digitize (beq y 1)` collapses any `y >= 2` to
/// `0` or `1` (`y := 5` gives `digitize false = 0 != 5`). `Le y 1` gives
/// `Lt y 2` (`le_succ_succ(y, 1, h) : Le (succ y) (succ 1)`, and `succ (num
/// 1)` is `refl`-defeq to `num 2`, so no separate lemma is needed for the
/// bound itself), then `Nat.lt_two_cases` splits into `y = 0`/`y = 1`, each
/// closed by transporting the hypothesis along the equality and a `refl` at
/// the computed literal (the same "build refl of one side, let defeq do the
/// rest" device [`beq_digitize_one`] uses).
fn round_trip_le_one(d: &mut NatDev<'_>, p: &NatPrelude, y: ExprId, h_le: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);

    let dg_of = |d: &mut NatDev<'_>, v: ExprId| -> ExprId {
        let one = d.num(1);
        let bv = d.beq(v, one);
        digitize(d, bv)
    };
    let dg_y = dg_of(d, y);
    let target = d.eq(dg_y, y);

    let succ_y_le_succ_one = d.lemma(p.le_succ_succ, &[y, one, h_le]); // Le (succ y) (succ 1) =defeq= Lt y 2
    let dichotomy = d.lemma(p.lt_two_cases, &[y, succ_y_le_succ_one]); // Or (Eq y 0) (Eq y 1)

    let zero = d.zero();
    let eq_y0_ty = d.eq(y, zero);
    let eq_y1_ty = d.eq(y, one);

    let minor_zero = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dg0 = dg_of(d, zero);
        let step1 = d.congr(y, zero, h, &|d, x| dg_of(d, x));
        let step2 = d.refl(dg0); // Eq dg0 dg0 =defeq= Eq dg0 zero (dg0 computes to 0)
        let to_zero = d.trans(dg_y, dg0, zero, step1, step2);
        let symm_h = d.symm(y, zero, h);
        let body = d.trans(dg_y, zero, y, to_zero, symm_h);
        d.lam_fv(h_fv, eq_y0_ty, body)
    };
    let minor_one = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dg1 = dg_of(d, one);
        let step1 = d.congr(y, one, h, &|d, x| dg_of(d, x));
        let step2 = d.refl(dg1); // Eq dg1 dg1 =defeq= Eq dg1 one (dg1 computes to 1)
        let to_one = d.trans(dg_y, dg1, one, step1, step2);
        let symm_h = d.symm(y, one, h);
        let body = d.trans(dg_y, one, y, to_one, symm_h);
        d.lam_fv(h_fv, eq_y1_ty, body)
    };

    let logic = d.prelude().logic;
    d.const_app(
        logic.or_elim,
        &[eq_y0_ty, eq_y1_ty, target, dichotomy, minor_zero, minor_one],
    )
}

/// `Eq (xor_fn a (xor_fn a b)) b`, for all `Bool` `a, b` --- the self-cancel
/// identity [`xor_bit_cancel_left`] lifts through the round-trip. Splitting
/// on `a` alone closes `a = false` for ANY `b` by `refl` (`xor_fn false w`
/// reduces to `w`, applied twice); `a = true` needs one more split on `b`,
/// and BOTH leaves close by `refl` directly with no further split (unlike
/// [`bool_xor_assoc`]'s `a = b = true` leaf, which needed a third level on
/// `c`).
fn bool_xor_self_cancel_left(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;

    let motive_a = |d: &mut NatDev<'_>, aa: ExprId| -> ExprId {
        let xor_ = super::bitwise::xor_fn(d);
        let inner = d.apply(xor_, &[aa, b]);
        let xor_2 = super::bitwise::xor_fn(d);
        let lhs = d.apply(xor_2, &[aa, inner]);
        d.bool_eq(lhs, b)
    };

    let at_a_false = |d: &mut NatDev<'_>| -> ExprId { d.bool_refl(b) };

    let at_a_true = |d: &mut NatDev<'_>| -> ExprId {
        let motive_b = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
            let true_ = d.bool_true();
            let xor_ = super::bitwise::xor_fn(d);
            let inner = d.apply(xor_, &[true_, bb]);
            let true_2 = d.bool_true();
            let xor_2 = super::bitwise::xor_fn(d);
            let lhs = d.apply(xor_2, &[true_2, inner]);
            d.bool_eq(lhs, bb)
        };
        // xor_fn true false = true; xor_fn true true = false -- so LHS at
        // b = false reduces to `false`, which IS `b` at this leaf.
        let at_b_false = |d: &mut NatDev<'_>| -> ExprId {
            let false_ = d.bool_false();
            d.bool_refl(false_)
        };
        // xor_fn true true = false; xor_fn true false = true -- LHS at
        // b = true reduces to `true`, which IS `b` at this leaf.
        let at_b_true = |d: &mut NatDev<'_>| -> ExprId {
            let true_ = d.bool_true();
            d.bool_refl(true_)
        };
        cases_bool(d, &p, b, &motive_b, &at_b_false, &at_b_true)
    };

    cases_bool(d, &p, a, &motive_a, &at_a_false, &at_a_true)
}

/// `Eq (xor_bit x (xor_bit x y)) y`, given `Le y 1` --- FALSE for general
/// `y`, see the module doc above and [`round_trip_le_one`]. Lifts
/// [`bool_xor_self_cancel_left`] through the same digitize/round-trip route
/// [`xor_bit_assoc`] uses, landing on `y` itself (not merely `digitize (beq
/// y 1)`) via [`round_trip_le_one`].
fn xor_bit_cancel_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    y: ExprId,
    h_le_y: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let bx = d.beq(x, one);
    let by = d.beq(y, one);

    let cond_xy = {
        let xor_ = super::bitwise::xor_fn(d);
        d.apply(xor_, &[bx, by])
    };
    let inner = super::testbit_bitwise::xor_bit(d, x, y); // refl-defeq to digitize(cond_xy)
    let b_inner = d.beq(inner, one);

    let start = super::testbit_bitwise::xor_bit(d, x, inner); // xor_bit(x, xor_bit(x, y))

    let rt_inner = beq_digitize_one(d, &p, cond_xy); // Eq b_inner cond_xy

    let mid1 = {
        let xor_ = super::bitwise::xor_fn(d);
        let inner2 = d.apply(xor_, &[bx, cond_xy]);
        digitize(d, inner2)
    };
    let step1 = congr_bool_to_nat(d, b_inner, cond_xy, rt_inner, &|d, w| {
        let xor_ = super::bitwise::xor_fn(d);
        let bxv = bx;
        let inner3 = d.apply(xor_, &[bxv, w]);
        digitize(d, inner3)
    });

    let self_cancel_bool = bool_xor_self_cancel_left(d, &p, bx, by); // Eq (xor_fn bx cond_xy) by
    let xor_bx_cond_xy = {
        let xor_ = super::bitwise::xor_fn(d);
        d.apply(xor_, &[bx, cond_xy])
    };
    let dg_by = digitize(d, by);
    let step2 = congr_bool_to_nat(d, xor_bx_cond_xy, by, self_cancel_bool, &|d, w| {
        digitize(d, w)
    });

    let (_, chain_proof) = d.chain(start, &[(mid1, step1), (dg_by, step2)]);

    let rt_y = round_trip_le_one(d, &p, y, h_le_y); // Eq dg_by y
    d.trans(start, dg_by, y, chain_proof, rt_y)
}

/// `Nat.xor_xor_cancel_left : ∀ a b, Eq (xor a (xor a b)) b` --- applies
/// [`declare_eq_of_test_bit_eq`]'s extensionality lemma to a per-bit proof
/// built from `Nat.testBit_xor` (twice) and [`xor_bit_cancel_left`], the
/// latter needing `Nat.testBit_le_one` to supply the `y <= 1` hypothesis at
/// each bit (`Nat.testBit` is always in `{0, 1}`).
fn declare_xor_xor_cancel_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.xor_xor_cancel_left, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let xab = d.const_app(p.xor, &[a, b]); // X := xor a b
        let lhs = d.const_app(p.xor, &[a, xab]); // xor a (xor a b)
        let stmt = d.eq(lhs, b);

        let bits_hyp = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);

            let tb_a = d.const_app(p.test_bit, &[a, i]);
            let tb_b = d.const_app(p.test_bit, &[b, i]);
            let tb_xab = d.const_app(p.test_bit, &[xab, i]);
            let tb_lhs = d.const_app(p.test_bit, &[lhs, i]);

            let outer = d.lemma(p.test_bit_xor, &[a, xab, i]); // Eq (testBit lhs i) (xor_bit tb_a tb_xab)
            let inner = d.lemma(p.test_bit_xor, &[a, b, i]); // Eq tb_xab (xor_bit tb_a tb_b)

            // xab_bit := xor_bit tb_a tb_b -- the VALUE testBit(xab, i)
            // equals (`inner`'s RHS), substituted below into the outer
            // combine `xor_bit tb_a _`, landing on `xor_bit tb_a (xor_bit
            // tb_a tb_b)` -- NOT `xab_bit` alone, which is only the inner
            // substituted operand, not the cascaded outer expression.
            let xor_bit_a_tbxab = super::testbit_bitwise::xor_bit(d, tb_a, tb_xab);
            let xab_bit = super::testbit_bitwise::xor_bit(d, tb_a, tb_b);
            let cascaded = super::testbit_bitwise::xor_bit(d, tb_a, xab_bit); // xor_bit tb_a (xor_bit tb_a tb_b)
            let congr_step = d.congr(tb_xab, xab_bit, inner, &|d, w| {
                let tb_a2 = tb_a;
                super::testbit_bitwise::xor_bit(d, tb_a2, w)
            }); // Eq xor_bit_a_tbxab cascaded

            let (_, to_cascaded) =
                d.chain(tb_lhs, &[(xor_bit_a_tbxab, outer), (cascaded, congr_step)]);

            let h_le_tbb = d.lemma(p.test_bit_le_one, &[b, i]); // Le tb_b 1
            let cancel = xor_bit_cancel_left(d, &p, tb_a, tb_b, h_le_tbb); // Eq cascaded tb_b

            let final_bit_eq = d.trans(tb_lhs, cascaded, tb_b, to_cascaded, cancel);
            d.lam_fv(i_fv, nat, final_bit_eq)
        };

        let proof = d.lemma(p.eq_of_test_bit_eq, &[lhs, b, bits_hyp]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.xor_xor_cancel_right : ∀ a b, Eq (xor (xor a b) b) a` --- the
/// symmetric partner of [`declare_xor_xor_cancel_left`], transported via
/// `Nat.xor_comm` twice rather than redoing the per-bit argument:
/// `xor (xor a b) b = xor (xor b a) b` (congr on `xor_comm a b`)
/// `= xor b (xor b a)` (`xor_comm (xor b a) b`)
/// `= a` (`xor_xor_cancel_left b a`).
fn declare_xor_xor_cancel_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.xor_xor_cancel_right, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let xab = d.const_app(p.xor, &[a, b]);
        let lhs = d.const_app(p.xor, &[xab, b]);
        let stmt = d.eq(lhs, a);

        let xba = d.const_app(p.xor, &[b, a]);
        let comm_ab = d.lemma(p.xor_comm, &[a, b]); // Eq xab xba
        let step0 = d.congr(xab, xba, comm_ab, &|d, w| {
            let bb = b;
            d.const_app(p.xor, &[w, bb])
        }); // Eq lhs (xor xba b)

        let xor_xba_b = d.const_app(p.xor, &[xba, b]);
        let comm2 = d.lemma(p.xor_comm, &[xba, b]); // Eq (xor xba b) (xor b xba)
        let xor_b_xba = d.const_app(p.xor, &[b, xba]);

        let cancel = d.lemma(p.xor_xor_cancel_left, &[b, a]); // Eq (xor b (xor b a)) a

        let (_, proof) = d.chain(lhs, &[(xor_xba_b, step0), (xor_b_xba, comm2), (a, cancel)]);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.xor_ne_zero_iff` -- the last of piece 4's four sub-targets. See the
// module doc ("`Nat.xor_ne_zero_iff` — via `mt` twice") for the route.
// ============================================================================

/// `Eq (xor_fn x x) false`, for all `Bool` `x` --- confirmed by the Python
/// truth-table simulation in the module doc (`xor_fn false false = false`,
/// `xor_fn true true = false`, both `refl`).
fn bool_xor_self(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, xx: ExprId| -> ExprId {
        let xor_ = super::bitwise::xor_fn(d);
        let lhs = d.apply(xor_, &[xx, xx]);
        let false_ = d.bool_false();
        d.bool_eq(lhs, false_)
    };
    let at_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    let at_true = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    cases_bool(d, &p, x, &motive, &at_false, &at_true)
}

/// `Eq (xor_bit x x) 0`, for all `Nat` `x` --- lifts [`bool_xor_self`]
/// through `digitize` the same way [`xor_bit_assoc`]/[`xor_bit_cancel_left`]
/// lift their own `Bool`-level facts: `xor_bit x x := digitize (xor_fn (beq
/// x 1) (beq x 1))` by definition, and `digitize false` iota-reduces to `0`.
fn xor_bit_self_zero(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let bx = d.beq(x, one);
    let xor_ = super::bitwise::xor_fn(d);
    let cond = d.apply(xor_, &[bx, bx]);
    let self_bool = bool_xor_self(d, &p, bx); // Eq cond false
    let false_ = d.bool_false();
    // Eq (digitize cond) (digitize false) -- refl-defeq to Eq (xor_bit x x) 0.
    congr_bool_to_nat(d, cond, false_, self_bool, &|d, w| digitize(d, w))
}

/// `Nat.xor_self`-shaped: `Eq (xor a a) 0`, for all `Nat` `a` --- applies
/// [`declare_eq_of_test_bit_eq`]'s extensionality lemma to a per-bit proof
/// built from `Nat.testBit_xor` and [`xor_bit_self_zero`].
fn xor_self(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();
    let xaa = d.const_app(p.xor, &[a, a]);

    let bits_hyp = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);

        let tb_a = d.const_app(p.test_bit, &[a, i]);
        let tb_xaa = d.const_app(p.test_bit, &[xaa, i]);
        let outer = d.lemma(p.test_bit_xor, &[a, a, i]); // Eq tb_xaa (xor_bit tb_a tb_a)
        let xor_bit_aa = super::testbit_bitwise::xor_bit(d, tb_a, tb_a);
        let self_zero = xor_bit_self_zero(d, &p, tb_a); // Eq xor_bit_aa 0
        let a_eq_zero = d.trans(tb_xaa, xor_bit_aa, zero, outer, self_zero); // Eq tb_xaa 0

        let tb_zero = d.const_app(p.test_bit, &[zero, i]);
        let tb_zero_i = d.lemma(p.test_bit_of_zero, &[i]); // Eq tb_zero zero
        let tb_zero_i_symm = d.symm(tb_zero, zero, tb_zero_i); // Eq zero tb_zero

        let bit_eq = d.trans(tb_xaa, zero, tb_zero, a_eq_zero, tb_zero_i_symm); // Eq tb_xaa tb_zero
        d.lam_fv(i_fv, nat, bit_eq)
    };

    d.lemma(p.eq_of_test_bit_eq, &[xaa, zero, bits_hyp])
}

/// `Eq (digitize cond) 0 -> Eq cond false`, for all `Bool` `cond` --- the
/// `false` branch is `refl` (`digitize false` iota-reduces to `0`, and the
/// hypothesis at that point is the trivial `Eq 0 0`). The `true` branch DOES
/// need an ex-falso, unlike [`bool_eq_of_xor_eq_false`]'s `true, false` leaf
/// below (which is genuinely the identity): `digitize true` reduces to `1`
/// (`succ zero`), so the hypothesis is the IMPOSSIBLE `Eq (succ zero) zero`,
/// refuted by `Nat.succ_ne_zero` into whatever the goal (`Eq true false`)
/// happens to be, via `False.rec`.
fn digitize_eq_zero_implies_false(d: &mut NatDev<'_>, p: &NatPrelude, cond: ExprId) -> ExprId {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, c: ExprId| -> ExprId {
        let dg = digitize(d, c);
        let zero = d.zero();
        let hyp = d.eq(dg, zero);
        let false_b = d.bool_false();
        let concl = d.bool_eq(c, false_b);
        d.arrow(hyp, concl)
    };
    let at_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_b = d.bool_false();
        let dg0 = digitize(d, false_b); // computes to 0
        let zero = d.zero();
        let hyp_ty = d.eq(dg0, zero);
        let h_fv = d.fresh_fvar();
        let body = d.bool_refl(false_b);
        d.lam_fv(h_fv, hyp_ty, body)
    };
    let at_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        let dg1 = digitize(d, true_); // computes to 1 = succ zero
        let zero = d.zero();
        let hyp_ty = d.eq(dg1, zero); // =defeq= Eq (succ zero) zero, an impossible hypothesis
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let false_b = d.bool_false();
        let concl_ty = d.bool_eq(true_, false_b);

        // ex falso: succ_ne_zero(zero) : Not (Eq (succ zero) zero); applied
        // to h gives False, then False.rec.{0} eliminates into concl_ty.
        let neg = d.lemma(p.succ_ne_zero, &[zero]); // Eq (succ zero) zero -> False
        let impossible = d.apply(neg, &[h]); // False
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let anon = d.anon_name();
        let false_motive = d
            .kernel()
            .lam(anon, false_ty, concl_ty, crate::BinderInfo::Default);
        let level_zero = d.kernel().level_zero();
        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let body = d.apply(false_rec, &[false_motive, impossible]);
        d.lam_fv(h_fv, hyp_ty, body)
    };
    cases_bool(d, &p, cond, &motive, &at_false, &at_true)
}

/// `Eq (xor_fn a b) false -> Eq a b`, for all `Bool` `a, b` --- confirmed by
/// the module doc's Python simulation. Splitting on `a` alone closes `a =
/// false` for ANY `b` via `bool_symm` on the (defeq-reduced) hypothesis
/// (`xor_fn false b` reduces to `b`); `a = true` needs one more split on
/// `b`: `b = false` is the IDENTITY (`xor_fn true false` reduces to `true`,
/// so the hypothesis `Eq true false` already IS the goal `Eq true false`);
/// `b = true` is `refl` (`xor_fn true true` reduces to `false`, so the
/// hypothesis is the trivial `Eq false false`, and the goal `Eq true true`
/// needs no case analysis on it at all).
fn bool_eq_of_xor_eq_false(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;

    let motive_a = |d: &mut NatDev<'_>, aa: ExprId| -> ExprId {
        let xor_ = super::bitwise::xor_fn(d);
        let lhs = d.apply(xor_, &[aa, b]);
        let false_ = d.bool_false();
        let hyp = d.bool_eq(lhs, false_);
        let concl = d.bool_eq(aa, b);
        d.arrow(hyp, concl)
    };

    let at_a_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp_ty = d.bool_eq(b, false_); // =defeq= Eq (xor_fn false b) false
        let body = d.bool_symm(b, false_, h); // Eq false b
        d.lam_fv(h_fv, hyp_ty, body)
    };

    let at_a_true = |d: &mut NatDev<'_>| -> ExprId {
        let motive_b = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
            let true_ = d.bool_true();
            let xor_ = super::bitwise::xor_fn(d);
            let lhs = d.apply(xor_, &[true_, bb]);
            let false_ = d.bool_false();
            let hyp = d.bool_eq(lhs, false_);
            let true_2 = d.bool_true();
            let concl = d.bool_eq(true_2, bb);
            d.arrow(hyp, concl)
        };
        let at_b_false = |d: &mut NatDev<'_>| -> ExprId {
            // xor_fn true false = true (refl). hyp: Eq true false. concl:
            // Eq true false. The identity -- not an ex-falso.
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hyp_ty = d.bool_eq(true_, false_);
            d.lam_fv(h_fv, hyp_ty, h)
        };
        let at_b_true = |d: &mut NatDev<'_>| -> ExprId {
            // xor_fn true true = false (refl). hyp: Eq false false. concl:
            // Eq true true.
            let false_ = d.bool_false();
            let true_ = d.bool_true();
            let h_fv = d.fresh_fvar();
            let hyp_ty = d.bool_eq(false_, false_);
            let body = d.bool_refl(true_);
            d.lam_fv(h_fv, hyp_ty, body)
        };
        cases_bool(d, &p, b, &motive_b, &at_b_false, &at_b_true)
    };

    cases_bool(d, &p, a, &motive_a, &at_a_false, &at_a_true)
}

/// `Eq (xor_bit x y) 0 -> Eq x y`, given `Le x 1` and `Le y 1` --- the
/// per-bit fact [`declare_xor_ne_zero_iff`]'s `mpr`-side corollary needs.
///
/// Route: `xor_bit x y = 0` gives `xor_fn (beq x 1) (beq y 1) = false`
/// ([`digitize_eq_zero_implies_false`]), hence `beq x 1 = beq y 1`
/// ([`bool_eq_of_xor_eq_false`]). Congruence lifts that Bool equality to an
/// equality of `digitize`d values, and [`round_trip_le_one`] at each of `x`
/// and `y` (using the `<= 1` hypotheses -- the SAME restriction
/// [`xor_bit_cancel_left`] needs, and for the same reason: the round-trip
/// only recovers the raw operand when it is already a bit) closes the chain
/// back to `Eq x y`.
fn xor_bit_eq_zero_implies_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    y: ExprId,
    h_le_x: ExprId,
    h_le_y: ExprId,
    h_zero: ExprId, // Eq (xor_bit x y) 0
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let bx = d.beq(x, one);
    let by = d.beq(y, one);
    let xor_ = super::bitwise::xor_fn(d);
    let cond = d.apply(xor_, &[bx, by]);

    let cond_false_fn = digitize_eq_zero_implies_false(d, &p, cond); // Eq (digitize cond) 0 -> Eq cond false
    let cond_false = d.apply(cond_false_fn, &[h_zero]); // Eq cond false

    let bx_eq_by_fn = bool_eq_of_xor_eq_false(d, &p, bx, by); // Eq cond false -> Eq bx by
    let bx_eq_by = d.apply(bx_eq_by_fn, &[cond_false]); // Eq bx by

    let dg_bx = digitize(d, bx);
    let dg_by = digitize(d, by);
    let congr_step = congr_bool_to_nat(d, bx, by, bx_eq_by, &|d, w| digitize(d, w)); // Eq dg_bx dg_by

    let rt_x = round_trip_le_one(d, &p, x, h_le_x); // Eq dg_bx x
    let rt_y = round_trip_le_one(d, &p, y, h_le_y); // Eq dg_by y
    let rt_x_symm = d.symm(dg_bx, x, rt_x); // Eq x dg_bx

    let (_, chain_proof) = d.chain(x, &[(dg_bx, rt_x_symm), (dg_by, congr_step), (y, rt_y)]);
    chain_proof
}

/// `Nat.xor_ne_zero_iff : ∀ a b, Iff (Not (Eq (xor a b) 0)) (Not (Eq a b))`
/// --- see the module doc ("`Nat.xor_ne_zero_iff` — via `mt` twice") for the
/// route: two directional corollaries ([`xor_self`] for `mp`,
/// [`xor_bit_eq_zero_implies_eq`] plus `Nat.eq_of_testBit_eq` for `mpr`) fed
/// into `mt` (modus tollens) directly, with no `Iff`-of-`Eq` intermediate.
fn declare_xor_ne_zero_iff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.xor_ne_zero_iff, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let xab = d.const_app(p.xor, &[a, b]);
        let zero = d.zero();
        let eq_xor_zero = d.eq(xab, zero);
        let eq_ab = d.eq(a, b);
        let not_xor_zero = d.const_app(p.logic.not, &[eq_xor_zero]);
        let not_ab = d.const_app(p.logic.not, &[eq_ab]);
        let stmt = d.const_app(p.logic.iff, &[not_xor_zero, not_ab]);

        // eq_of_xor_eq_zero_fn : Eq (xor a b) 0 -> Eq a b
        let eq_of_xor_eq_zero_fn = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let bits_hyp = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);

                let tb_a = d.const_app(p.test_bit, &[a, i]);
                let tb_b = d.const_app(p.test_bit, &[b, i]);
                let tb_xab = d.const_app(p.test_bit, &[xab, i]);

                let congr_h = d.congr(xab, zero, h, &|d, w| d.const_app(p.test_bit, &[w, i])); // Eq tb_xab (testBit 0 i)
                let tb_zero = d.const_app(p.test_bit, &[zero, i]);
                let tb_zero_i = d.lemma(p.test_bit_of_zero, &[i]); // Eq tb_zero zero
                let (_, tb_xab_eq_zero) = d.chain(tb_xab, &[(tb_zero, congr_h), (zero, tb_zero_i)]); // Eq tb_xab 0

                let outer = d.lemma(p.test_bit_xor, &[a, b, i]); // Eq tb_xab (xor_bit tb_a tb_b)
                let xab_bit = super::testbit_bitwise::xor_bit(d, tb_a, tb_b);
                let outer_symm = d.symm(tb_xab, xab_bit, outer); // Eq xab_bit tb_xab
                let bit_zero = d.trans(xab_bit, tb_xab, zero, outer_symm, tb_xab_eq_zero); // Eq xab_bit 0

                let h_le_a = d.lemma(p.test_bit_le_one, &[a, i]); // Le tb_a 1
                let h_le_b = d.lemma(p.test_bit_le_one, &[b, i]); // Le tb_b 1
                let bit_eq =
                    xor_bit_eq_zero_implies_eq(d, &p, tb_a, tb_b, h_le_a, h_le_b, bit_zero);
                d.lam_fv(i_fv, nat, bit_eq)
            };

            let proof = d.lemma(p.eq_of_test_bit_eq, &[a, b, bits_hyp]);
            d.lam_fv(h_fv, eq_xor_zero, proof)
        };

        // xor_eq_zero_of_eq_fn : Eq a b -> Eq (xor a b) 0
        let xor_eq_zero_of_eq_fn = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let xaa = d.const_app(p.xor, &[a, a]);
            let congr_h = d.congr(a, b, h, &|d, w| {
                let a2 = a;
                d.const_app(p.xor, &[a2, w])
            }); // Eq xaa xab
            let congr_h_symm = d.symm(xaa, xab, congr_h); // Eq xab xaa
            let self_zero = xor_self(d, &p, a); // Eq xaa 0
            let proof = d.trans(xab, xaa, zero, congr_h_symm, self_zero); // Eq xab 0
            d.lam_fv(h_fv, eq_ab, proof)
        };

        let mt = p.logic.mt;
        let mp = d.const_app(mt, &[eq_ab, eq_xor_zero, xor_eq_zero_of_eq_fn]); // Not eq_xor_zero -> Not eq_ab
        let mpr = d.const_app(mt, &[eq_xor_zero, eq_ab, eq_of_xor_eq_zero_fn]); // Not eq_ab -> Not eq_xor_zero

        let proof = d.const_app(p.logic.iff_intro, &[not_xor_zero, not_ab, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares.
pub(super) fn declare_xor_algebra_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_eq_of_test_bit_eq(d, p)?;
    declare_xor_assoc(d, p)?;
    declare_xor_xor_cancel_left(d, p)?;
    declare_xor_xor_cancel_right(d, p)?;
    declare_xor_ne_zero_iff(d, p)?;
    Ok(())
}
