//! `Nat.eq_of_testBit_eq` — the general "same bits imply the same number"
//! extensionality lemma, built toward piece 4 of the 4 pieces
//! `docs/plan/status/260-nat-lt-xor-cases.md` named as blocking
//! `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.xor_assoc`,
//! `Nat.xor_xor_cancel_left`/`_right`, `Nat.xor_ne_zero_iff`). See
//! `docs/plan/status/263-nat-testbit-xor.md` for piece 1 (`Nat.testBit_xor`,
//! landed) and `docs/plan/status/264-nat-xor-algebra.md` for this lane's
//! handoff, including why the three `xor` algebra targets themselves are
//! NOT landed in this file (time-boxed out; the remaining shape is
//! documented there, not sketched here as unverified code).
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
//! # What this file does NOT reach (documented, not sketched)
//!
//! None of `Nat.xor_assoc`, `Nat.xor_xor_cancel_left`/`_right`,
//! `Nat.xor_ne_zero_iff` are declared in this file — see
//! `docs/plan/status/264-nat-xor-algebra.md` for the exact remaining shape
//! of each, including the `xor_bit` Boolean-algebra lemmas
//! (`xor_bit`'s value depends on its arguments ONLY through whether each
//! equals `1`, so associativity/self-cancellation hold for ALL `x, y, z :
//! Nat`, not merely bits in `{0, 1}`, via a `Bool.rec` case split at most
//! 2-3 levels deep) that would combine with [`declare_eq_of_test_bit_eq`]
//! and `Nat.testBit_xor` to close them.
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

/// Everything this module declares. See the module doc for what's NOT
/// declared here (`Nat.xor_xor_cancel_left`/`_right`, `Nat.xor_ne_zero_iff`).
pub(super) fn declare_xor_algebra_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_eq_of_test_bit_eq(d, p)?;
    declare_xor_assoc(d, p)?;
    Ok(())
}
