//! `Nat.testBit_xor` — bridging `testBitAux`'s INDEX recursion with
//! `bitwiseAux`'s VALUE recursion. Piece (1) of the 4 pieces
//! `docs/plan/status/260-nat-lt-xor-cases.md` named as blocking
//! `F:ml430-nat-lt-xor-cases-c43a1e85`; see
//! `docs/plan/status/263-nat-testbit-xor.md` for the handoff on pieces 2-4.
//!
//! # The statement
//!
//! ```text
//! Nat.testBit_xor : ∀ m n i,
//!   Eq (testBit (xor m n) i) (xor_bit (testBit m i) (testBit n i))
//! ```
//!
//! `xor_bit(x, y) := bool_select_nat (xor_fn (beq x 1) (beq y 1)) 1 0` — the
//! SAME per-bit combine `bitwiseAux`'s own `succ_minor` row builds at bit 0
//! (`bitwise.rs`), generalized here to an arbitrary bit position. Nat-valued
//! throughout (Mathlib's `testBit` returns `Bool`; ours returns `Nat` in
//! `{0, 1}`), so this is a local `F:nat-*` fact once landed, not an `ml430`
//! mirror — see this crate's closing status doc for the exact reasoning.
//!
//! `xor_bit` is duplicated (not imported) from `xor_parity.rs`'s private
//! `fn xor_bit` — that file is mid-work in a sibling lane and out of this
//! lane's scope to touch; the construction is eight lines and identical.
//!
//! # Keeping the two recursions in step
//!
//! `testBitAux` recurses on the INDEX `i` (`testBit_succ`, refl: `testBit n
//! (succ i) ≡ testBit (n/2) i`), carrying `n` through unchanged. `xor`
//! recurses on FUEL derived from the VALUE (`bitwiseAux`, fuel = the first
//! operand's magnitude). The bridge is an induction on `i`, generalizing
//! over BOTH `m` and `n` in the motive (the same "generalize the OTHER
//! variable" device `binary.rs`'s `testBit_le_one`/`sum_testBit_lt` use for
//! one variable, widened to two since `xor` genuinely mixes them), reduced
//! at each level to two per-step lemmas that do NOT mention `i` at all:
//!
//! - [`xor_low_bit`]: `Eq (mod (xor m n) 2) (xor_bit (mod m 2) (mod n 2))`
//!   — closes the induction's BASE case (`testBit _ 0` is `refl`-defeq to
//!   `mod _ 2`, so this closes `i = 0` with no explicit rewrite). This is
//!   `xor_parity.rs`'s `even_xor_hard_case` step generalized from `Iff
//!   Even` to a plain `Eq` and extended to cover the `m = 0`/`n = 0`
//!   boundary cases (which `even_xor` handles by a DIFFERENT "one side of
//!   an `Iff` is always true" device that has no `Eq`-shaped analogue) —
//!   built via `cases_mod_two` there instead.
//! - [`xor_div_two`]: `Eq (div (xor m n) 2) (xor (div m 2) (div n 2))` —
//!   closes the STEP case (`testBit _ (succ j)` is `refl`-defeq to `testBit
//!   (_/2) j`, so `d.congr` along this equation transports the IH from
//!   `(m/2, n/2)` back to `(m, n)`). This is new: nothing in the prelude
//!   related `xor`'s recursive tail to `xor` of the halved operands before
//!   this file. The `m`, `n` both-nonzero case needs
//!   `bitwise_aux_agree_of_fuel` (`bitwise.rs`, ADR-none, fuel-irrelevance)
//!   to bridge the exposed fuel `pm` (one less than `m`) to the CANONICAL
//!   fuel `m/2` that `xor (m/2) (n/2)`'s own definition uses — via
//!   `half_le_predecessor_of_succ` (`rec_agreement.rs`) for the
//!   sufficiency bound.
//!
//! Both lemmas share the same "one step of `bitwiseAux`'s recursor" case
//! analysis (`m = 0`; `n = 0` with `m` exposed `succ`-shaped; both `succ`),
//! bundled in [`xor_step`] so the recursive term, the per-bit combine, and
//! its `< 2` bound are computed once and reused by both.
//!
//! # What pieces 2-4 still need (unchanged from `docs/plan/status/260-…`)
//!
//! This file supplies exactly piece (1). `exists_most_significant_bit`,
//! `lt_of_testBit`, and `xor_assoc`/`xor_xor_cancel`/`xor_ne_zero_iff` are
//! untouched — see `docs/plan/status/263-nat-testbit-xor.md`.

use super::NatPrelude;
use super::bitwise::xor_fn;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps, cases_mod_two, cases_zero_succ};
use super::parity::mod_two_mul_add_of_lt;
use super::rec_agreement::half_le_predecessor_of_succ;
use crate::KernelError;
use crate::expr::ExprId;

/// `fun x y => bool_select_nat (xor_fn (beq x 1) (beq y 1)) 1 0` — the
/// per-bit XOR combine (duplicated from `xor_parity.rs`'s private
/// `xor_bit`, see the module doc for why).
pub(super) fn xor_bit<D: NatOps>(d: &mut D, x: ExprId, y: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let x_bool = d.beq(x, one);
    let y_bool = d.beq(y, one);
    let xor_ = xor_fn(d);
    let combined = d.apply(xor_, &[x_bool, y_bool]);
    d.bool_select_nat(combined, one, zero)
}

/// `Eq (xor k 0) k`, for ANY `k` (possibly symbolic) — `Nat.bitwise_zero_right`
/// at `f := xor_fn`: that theorem's own statement is `Eq (bitwise f k 0)
/// (bool_select_nat (f true false) k 0)`, and at the CONCRETE `f := xor_fn`,
/// `xor_fn true false` reduces to the literal `true` (both arguments are
/// already `Bool` literals, so no symbolic-scrutinee `Bool.rec` is stuck),
/// so `bool_select_nat true k 0` reduces to `k` by `refl` regardless of
/// `k`'s own shape — the same defeq-bridging technique `xor_comm`
/// (`xor_order.rs`) uses for `bitwise_comm`.
pub(super) fn xor_zero_right(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId) -> ExprId {
    let p = *p;
    let xor_ = xor_fn(d);
    d.lemma(p.bitwise_zero_right, &[xor_, k])
}

/// `Eq (div (add (mul two x) r) two) x`, given `Lt r two` — the DIV sibling
/// of `parity.rs`'s `mod_two_mul_add_of_lt` (not exposed there; duplicated
/// rather than editing that file, which a sibling lane is mid-work on).
/// Identical `divMod`-uniqueness witness, `and_left` in place of
/// `and_right`.
pub(super) fn div_two_mul_add_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    r: ExprId,
    r_lt_two: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let mul_two_x = d.mul(two, x);
    let dividend = d.add(mul_two_x, r);

    let eq_ty = d.eq(dividend, dividend);
    let bound_ty = d.lt(r, two);
    let refl_eq = d.refl(dividend);
    let h_construct = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, refl_eq, r_lt_two]);

    let h_exec = d.lemma(p.div_mod_exec, &[one, dividend]);
    let q_exec = d.div(dividend, two);
    let r_exec = d.modulo(dividend, two);

    let unique = d.lemma(
        p.div_mod_unique,
        &[two, dividend, q_exec, r_exec, x, r, h_exec, h_construct],
    );
    let eq_q_ty = d.eq(q_exec, x);
    let eq_r_ty = d.eq(r_exec, r);
    and_left(d, eq_q_ty, eq_r_ty, unique)
}

/// The pieces exposed by ONE step of `bitwiseAux`'s recursor at `f :=
/// xor_fn`, `m := succ pm`, `n := succ pn` (both operands literally
/// `succ`-shaped, so both zero-guards collapse to `false` by `refl` and the
/// "genuinely bitwise" row fires) — shared by [`xor_low_bit`] and
/// [`xor_div_two`]'s hard cases, mirroring `xor_parity.rs`'s
/// `even_xor_hard_case`.
struct XorStep {
    /// `xor_fn`, reused verbatim everywhere below so every `bitwiseAux`
    /// term built from it is the SAME closed term.
    xor_term: ExprId,
    /// `bitwiseAux xor_fn pm (m/2) (n/2)` — the recursive call one step
    /// down, at fuel `pm` (NOT yet the canonical fuel `m/2`).
    recursive: ExprId,
    /// The per-bit XOR value at bit 0 of `m`, `n`: `xor_bit (m%2) (n%2)`.
    combined: ExprId,
    /// `Lt combined two`.
    combined_lt_two: ExprId,
    /// `div m 2` (`m := succ pm`).
    half_m: ExprId,
    /// `div n 2` (`n := succ pn`).
    half_n: ExprId,
    /// `add (mul two recursive) combined` — `bitwiseAux`'s `succ_minor` row
    /// fully reduced; `refl`-defeq to `xor (succ pm) (succ pn)`.
    xn_reduced: ExprId,
}

fn xor_step(d: &mut NatDev<'_>, p: &NatPrelude, pm: ExprId, pn: ExprId) -> XorStep {
    let p = *p;
    let m_succ = d.succ(pm);
    let n_succ = d.succ(pn);
    let two = d.num(2);
    let zero = d.zero();
    let half_m = d.div(m_succ, two);
    let half_n = d.div(n_succ, two);
    let xor_term = xor_fn(d);
    let recursive = d.const_app(p.bitwise_aux, &[xor_term, pm, half_m, half_n]);
    let bit_m = d.modulo(m_succ, two);
    let bit_n = d.modulo(n_succ, two);
    let combined = xor_bit(d, bit_m, bit_n);
    let doubled = d.mul(two, recursive);
    let xn_reduced = d.add(doubled, combined);

    // `Lt combined two`: `combined` is `bool_select_nat cond 1 0` for a
    // (possibly symbolic) `Bool` `cond` -- decide it directly by `Bool.rec`,
    // exactly `xor_parity.rs::even_xor_hard_case`'s derivation.
    let combined_lt_two = {
        let one = d.num(1);
        let bit_m_bool = d.beq(bit_m, one);
        let bit_n_bool = d.beq(bit_n, one);
        let cond = d.apply(xor_term, &[bit_m_bool, bit_n_bool]);
        let bool_ty = d.bool_ty();
        let motive_lam = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let v = d.bool_select_nat(c, one, zero);
            let body = d.lt(v, two);
            d.lam_fv(c_fv, bool_ty, body)
        };
        let case_true = d.lemma(p.le_refl, &[two]);
        let case_false = d.zero_lt_succ(one);
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
        d.apply(bool_rec, &[motive_lam, case_false, case_true, cond])
    };

    XorStep {
        xor_term,
        recursive,
        combined,
        combined_lt_two,
        half_m,
        half_n,
        xn_reduced,
    }
}

/// `Eq (mod (xor m n) 2) (xor_bit (mod m 2) (mod n 2))`, for ALL `m`, `n` —
/// the low-bit correctness of `Nat.xor`, generalizing
/// `xor_parity.rs::even_xor_hard_case` (which stops at `Iff Even`) to a
/// plain `Eq` and covering its boundary cases too. Three cases via
/// `cases_zero_succ` on `m` then `n`; see the module doc.
fn xor_low_bit(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;

    let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
        let two = d.num(2);
        let xor_mn = d.const_app(p.xor, &[mm, n]);
        let lhs = d.modulo(xor_mn, two);
        let mod_m = d.modulo(mm, two);
        let mod_n = d.modulo(n, two);
        let rhs = xor_bit(d, mod_m, mod_n);
        d.eq(lhs, rhs)
    };

    let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let one = d.num(1);
        let at_zero = d.refl(zero);
        let at_one = d.refl(one);
        cases_mod_two(
            d,
            &p,
            n,
            &|d, y| {
                let zero = d.zero();
                let xb = xor_bit(d, zero, y);
                d.eq(y, xb)
            },
            at_zero,
            at_one,
        )
    };

    let at_m_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
        let m_succ = d.succ(pm);

        let motive_n = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let two = d.num(2);
            let xor_mn = d.const_app(p.xor, &[m_succ, nn]);
            let lhs = d.modulo(xor_mn, two);
            let mod_m = d.modulo(m_succ, two);
            let mod_n = d.modulo(nn, two);
            let rhs = xor_bit(d, mod_m, mod_n);
            d.eq(lhs, rhs)
        };

        let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let one = d.num(1);
            let at_zero = d.refl(zero);
            let at_one = d.refl(one);
            cases_mod_two(
                d,
                &p,
                m_succ,
                &|d, x| {
                    let zero = d.zero();
                    let xb = xor_bit(d, x, zero);
                    d.eq(x, xb)
                },
                at_zero,
                at_one,
            )
        };

        let at_n_succ = |d: &mut NatDev<'_>, pn: ExprId| -> ExprId {
            let step = xor_step(d, &p, pm, pn);
            mod_two_mul_add_of_lt(d, &p, step.recursive, step.combined, step.combined_lt_two)
        };

        cases_zero_succ(d, n, &motive_n, &at_n_zero, &at_n_succ)
    };

    cases_zero_succ(d, m, &motive_m, &at_m_zero, &at_m_succ)
}

/// `Eq (div (xor m n) 2) (xor (div m 2) (div n 2))`, for ALL `m`, `n` —
/// relates `xor`'s recursive tail to `xor` of the halved operands. Three
/// cases via `cases_zero_succ`, mirroring [`xor_low_bit`]; see the module
/// doc for the both-`succ` case's fuel-irrelevance step.
fn xor_div_two(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;

    let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
        // Both sides reduce to `div n 2` by `refl` alone: `xor 0 k` reduces
        // to `k` for literal fuel `0` regardless of `k`'s shape, on EITHER
        // side of the equation (`k := n` on the left, `k := div n 2` on the
        // right, once `div 0 2` reduces to `0`).
        let two = d.num(2);
        let half_n = d.div(n, two);
        d.refl(half_n)
    };

    let at_m_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
        let m_succ = d.succ(pm);

        let motive_n = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let two = d.num(2);
            let xor_mn = d.const_app(p.xor, &[m_succ, nn]);
            let lhs = d.div(xor_mn, two);
            let half_m = d.div(m_succ, two);
            let half_n = d.div(nn, two);
            let rhs = d.const_app(p.xor, &[half_m, half_n]);
            d.eq(lhs, rhs)
        };

        let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
            // LHS reduces to `div m_succ 2` by `refl` (one step: `m_succ`'s
            // outer `succ` shape is enough). RHS needs `xor_zero_right` at
            // the truly SYMBOLIC `div m_succ 2` -- `div 0 2` reduces to `0`
            // by `refl`, but `xor (div m_succ 2) 0` does not reduce by
            // `refl` for a non-literal fuel.
            let two = d.num(2);
            let zero = d.zero();
            let half_m = d.div(m_succ, two);
            let xor_half_m_zero = xor_zero_right(d, &p, half_m);
            let lhs_of_xzr = d.const_app(p.xor, &[half_m, zero]);
            d.symm(lhs_of_xzr, half_m, xor_half_m_zero)
        };

        let at_n_succ = |d: &mut NatDev<'_>, pn: ExprId| -> ExprId {
            let step = xor_step(d, &p, pm, pn);
            let two = d.num(2);

            // `div (xor m_succ n_succ) 2` reduces (`refl`) to `div
            // xn_reduced 2`; erase `combined` under `div _ 2`.
            let div_eq_recursive =
                div_two_mul_add_of_lt(d, &p, step.recursive, step.combined, step.combined_lt_two);
            let lhs = d.div(step.xn_reduced, two);

            // Bridge `bitwiseAux xor_term pm half_m half_n` (fuel `pm`) to
            // the CANONICAL `bitwiseAux xor_term half_m half_m half_n`
            // (fuel `half_m`, `refl`-defeq to `xor half_m half_n`) via
            // fuel-irrelevance.
            let le_refl_half_m = d.lemma(p.le_refl, &[step.half_m]);
            let succ_pm = d.succ(pm);
            let bound = d.lemma(p.le_refl, &[succ_pm]);
            let le_half_m_pm = half_le_predecessor_of_succ(d, &p, pm, pm, bound);
            let agree = d.lemma(
                p.bitwise_aux_agree_of_fuel,
                &[step.xor_term, pm, step.half_m, step.half_n, step.half_m],
            );
            let agree = d.apply(agree, &[le_half_m_pm, le_refl_half_m]);
            let agree_rhs = d.const_app(
                p.bitwise_aux,
                &[step.xor_term, step.half_m, step.half_m, step.half_n],
            );

            d.trans(lhs, step.recursive, agree_rhs, div_eq_recursive, agree)
        };

        cases_zero_succ(d, n, &motive_n, &at_n_zero, &at_n_succ)
    };

    let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
        let two = d.num(2);
        let xor_mn = d.const_app(p.xor, &[mm, n]);
        let lhs = d.div(xor_mn, two);
        let half_m = d.div(mm, two);
        let half_n = d.div(n, two);
        let rhs = d.const_app(p.xor, &[half_m, half_n]);
        d.eq(lhs, rhs)
    };

    cases_zero_succ(d, m, &motive_m, &at_m_zero, &at_m_succ)
}

/// `Nat.testBit_xor : ∀ m n i, Eq (testBit (xor m n) i) (xor_bit (testBit m
/// i) (testBit n i))` — see the module doc for the induction shape.
fn declare_test_bit_xor(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let xor_mn = d.const_app(p.xor, &[m, n]);
        let lhs = d.const_app(p.test_bit, &[xor_mn, x]);
        let tb_m = d.const_app(p.test_bit, &[m, x]);
        let tb_n = d.const_app(p.test_bit, &[n, x]);
        let rhs = xor_bit(d, tb_m, tb_n);
        let body = d.eq(lhs, rhs);
        let over_n = d.pi_fv(n_fv, nat, body);
        d.pi_fv(m_fv, nat, over_n)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let proof = xor_low_bit(d, &p, m, n);
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(m_fv, nat, with_n)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let half_m = d.div(m, two);
        let half_n = d.div(n, two);

        // ih_half : Eq (testBit (xor half_m half_n) j)
        //              (xor_bit (testBit half_m j) (testBit half_n j))
        let ih_half = d.apply(ih, &[half_m, half_n]);

        // div_eq : Eq (div (xor m n) 2) (xor half_m half_n)
        let div_eq = xor_div_two(d, &p, m, n);

        let xor_mn = d.const_app(p.xor, &[m, n]);
        let half_xor_mn = d.div(xor_mn, two);
        let xor_half = d.const_app(p.xor, &[half_m, half_n]);

        // congr_step : Eq (testBit half_xor_mn j) (testBit xor_half j)
        let congr_step = d.congr(half_xor_mn, xor_half, div_eq, &|d, x| {
            d.const_app(p.test_bit, &[x, j])
        });

        let lhs = d.const_app(p.test_bit, &[half_xor_mn, j]);
        let mid = d.const_app(p.test_bit, &[xor_half, j]);
        let tb_half_m = d.const_app(p.test_bit, &[half_m, j]);
        let tb_half_n = d.const_app(p.test_bit, &[half_n, j]);
        let rhs = xor_bit(d, tb_half_m, tb_half_n);

        let proof = d.trans(lhs, mid, rhs, congr_step, ih_half);
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(m_fv, nat, with_n)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof_fn = d.induct(&motive, &base, &step, i);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.apply(proof_fn, &[m, n]);

    let stmt = {
        let xor_mn = d.const_app(p.xor, &[m, n]);
        let lhs = d.const_app(p.test_bit, &[xor_mn, i]);
        let tb_m = d.const_app(p.test_bit, &[m, i]);
        let tb_n = d.const_app(p.test_bit, &[n, i]);
        let rhs = xor_bit(d, tb_m, tb_n);
        d.eq(lhs, rhs)
    };
    let ty = {
        let over_i = d.pi_fv(i_fv, nat, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        d.pi_fv(m_fv, nat, over_n)
    };
    let value = {
        let over_i = d.lam_fv(i_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        d.lam_fv(m_fv, nat, over_n)
    };
    d.declare_theorem(p.test_bit_xor, ty, value)
}

// =============================================================================
// `Nat.testBit_land` / `Nat.testBit_lor` -- the AND/OR analogues of
// `Nat.testBit_xor` above, transported to `Nat.landAux`/`Nat.lorAux` rather
// than `Nat.bitwiseAux`. Both mirrors (`F:ml430-nat-testbit-land-dfef7ca4`,
// `F:ml430-nat-testbit-lor-7644e067`) are Bool-vs-Nat codomain mismatches
// (see `docs/plan/status/244-nat-testbit-bitwise.md`) and stay `open`; these
// are new LOCAL `F:nat-*` facts, matching `test_bit_xor`'s own pattern.
//
// `land`/`lor` are separate fuel recursions from `bitwiseAux` (no `f`
// combinator argument), so `xor_step`/`xor_low_bit`/`xor_div_two` are not
// reused directly -- `land_step`/`land_low_bit`/`land_div_two` and their
// `lor` twins mirror the SHAPE of those functions with `land`/`lor`'s own
// names and per-bit combine substituted in.
// =============================================================================

/// `Lt (mod x 2) 2`, for ANY `x` -- straight from `Nat.mod_lt`.
fn mod_two_lt_two(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let pos = d.zero_lt_succ(one);
    d.lemma(p.mod_lt, &[x, two, pos])
}

/// `Le (mod x 2) 1`, for ANY `x` -- [`mod_two_lt_two`] then `le_of_lt_succ`
/// (`two` is literally `succ one`, so the `Lt _ 2` witness is already typed
/// as `Lt _ (succ one)`).
fn mod_two_le_one(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let lt2 = mod_two_lt_two(d, &p, x);
    let bit = d.modulo(x, two);
    d.lemma(p.le_of_lt_succ, &[bit, one, lt2])
}

/// `Lt (mul (mod m 2) (mod n 2)) 2` -- `land`'s per-bit AND is bounded by
/// `mod m 2` (the `bit_product_le_left` shape: `Le (mul a b) a` given
/// `Le b 1`), chained with `Lt (mod m 2) 2`. No case split needed --
/// symbolic in both `m` and `n`.
fn land_bit_lt_two(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let bit_m = d.modulo(m, two);
    let bit_n = d.modulo(n, two);
    let bit_n_le_one = mod_two_le_one(d, &p, n);
    let bit = d.mul(bit_m, bit_n);
    let bit_m_one = d.mul(bit_m, one);
    let mono = d.lemma(p.mul_le_mul_left, &[bit_m, bit_n, one, bit_n_le_one]);
    // mono : Le bit bit_m_one
    let mul_one_eq = d.lemma(p.mul_one, &[bit_m]); // Eq bit_m_one bit_m
    let motive = d.eq_motive(bit_m_one, &|d, x| d.le(bit, x));
    let bit_le_bit_m = d.transport(bit_m_one, motive, mono, bit_m, mul_one_eq);
    let bit_m_lt_two = mod_two_lt_two(d, &p, m);
    d.lemma(
        p.lt_of_le_of_lt,
        &[bit, bit_m, two, bit_le_bit_m, bit_m_lt_two],
    )
}

/// `Lt (bool_select_nat (ble (mod m 2) (mod n 2)) (mod n 2) (mod m 2)) 2` --
/// `lor`'s per-bit OR (`max` via `ble`/`bool_select_nat`) is bounded by
/// `Bool.rec` directly on the comparison, needing only `Lt (mod m 2) 2` and
/// `Lt (mod n 2) 2` at the two branches (mirrors `rec_agreement.rs`'s
/// private `lor_bit_lt_two`, duplicated per this file's established
/// convention -- see [`div_two_mul_add_of_lt`]'s doc).
fn lor_bit_lt_two(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let bool_ty = d.bool_ty();
    let bit_m = d.modulo(m, two);
    let bit_n = d.modulo(n, two);
    let bit_m_lt_two = mod_two_lt_two(d, &p, m);
    let bit_n_lt_two = mod_two_lt_two(d, &p, n);
    let cond = d.ble(bit_m, bit_n);
    let motive = |d: &mut NatDev<'_>, c: ExprId| -> ExprId {
        let sel = d.bool_select_nat(c, bit_n, bit_m);
        d.lt(sel, two)
    };
    let motive_lam = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = motive(d, c);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive_lam, bit_m_lt_two, bit_n_lt_two, cond])
}

/// The pieces exposed by ONE step of `landAux`'s recursor at `m := succ pm`,
/// `n := succ pn` (both operands literally `succ`-shaped, so both
/// zero-guards collapse to `false` by `refl` and the genuinely-bitwise row
/// fires) -- the `land` twin of `XorStep`/`xor_step`, minus the `f`
/// combinator argument `landAux` doesn't take.
struct LandStep {
    recursive: ExprId,
    combined: ExprId,
    combined_lt_two: ExprId,
    half_m: ExprId,
    half_n: ExprId,
    xn_reduced: ExprId,
}

fn land_step(d: &mut NatDev<'_>, p: &NatPrelude, pm: ExprId, pn: ExprId) -> LandStep {
    let p = *p;
    let m_succ = d.succ(pm);
    let n_succ = d.succ(pn);
    let two = d.num(2);
    let half_m = d.div(m_succ, two);
    let half_n = d.div(n_succ, two);
    let recursive = d.const_app(p.land_aux, &[pm, half_m, half_n]);
    let bit_m = d.modulo(m_succ, two);
    let bit_n = d.modulo(n_succ, two);
    let combined = d.mul(bit_m, bit_n);
    let combined_lt_two = land_bit_lt_two(d, &p, m_succ, n_succ);
    let doubled = d.mul(two, recursive);
    let xn_reduced = d.add(doubled, combined);
    LandStep {
        recursive,
        combined,
        combined_lt_two,
        half_m,
        half_n,
        xn_reduced,
    }
}

/// `Eq (mod (land m n) 2) (mul (mod m 2) (mod n 2))`, for ALL `m`, `n`.
/// `land`'s ABSORBING zero (`land 0 n = 0`, `land m 0 = 0`) makes both
/// boundary cases collapse straight to `0` on both sides -- simpler than
/// `xor_low_bit`'s shape, which has to carry `n`/`m` through unchanged.
fn land_low_bit(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let zero = d.zero();

    let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
        let land_mn = d.const_app(p.land, &[mm, n]);
        let lhs = d.modulo(land_mn, two);
        let mod_m = d.modulo(mm, two);
        let mod_n = d.modulo(n, two);
        let rhs = d.mul(mod_m, mod_n);
        d.eq(lhs, rhs)
    };

    let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
        let land_0n = d.const_app(p.land, &[zero, n]);
        let lhs = d.modulo(land_0n, two);
        let land_0n_eq_zero = d.lemma(p.land_zero_left, &[n]);
        let mod_zero_two = d.modulo(zero, two);
        let congr1 = d.congr(land_0n, zero, land_0n_eq_zero, &|d, x| d.modulo(x, two));
        let zero_mod_1 = d.lemma(p.zero_mod, &[two]);
        let (_, lhs_is_zero) = d.chain(lhs, &[(mod_zero_two, congr1), (zero, zero_mod_1)]);

        let mod_n = d.modulo(n, two);
        let rhs = d.mul(mod_zero_two, mod_n);
        let zero_mod_2 = d.lemma(p.zero_mod, &[two]);
        let mul_zero_n = d.mul(zero, mod_n);
        let congr2 = d.congr(mod_zero_two, zero, zero_mod_2, &|d, x| d.mul(x, mod_n));
        let zero_mul_n = d.lemma(p.zero_mul, &[mod_n]);
        let (_, rhs_is_zero) = d.chain(rhs, &[(mul_zero_n, congr2), (zero, zero_mul_n)]);

        let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
        d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
    };

    let at_m_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
        let m_succ = d.succ(pm);

        let motive_n = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let land_mn = d.const_app(p.land, &[m_succ, nn]);
            let lhs = d.modulo(land_mn, two);
            let mod_m = d.modulo(m_succ, two);
            let mod_n = d.modulo(nn, two);
            let rhs = d.mul(mod_m, mod_n);
            d.eq(lhs, rhs)
        };

        let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
            let land_m0 = d.const_app(p.land, &[m_succ, zero]);
            let lhs = d.modulo(land_m0, two);
            let land_m0_eq_zero = d.lemma(p.land_zero_right, &[m_succ]);
            let mod_zero_two = d.modulo(zero, two);
            let congr1 = d.congr(land_m0, zero, land_m0_eq_zero, &|d, x| d.modulo(x, two));
            let zero_mod_1 = d.lemma(p.zero_mod, &[two]);
            let (_, lhs_is_zero) = d.chain(lhs, &[(mod_zero_two, congr1), (zero, zero_mod_1)]);

            let mod_m = d.modulo(m_succ, two);
            let rhs = d.mul(mod_m, mod_zero_two);
            let zero_mod_2 = d.lemma(p.zero_mod, &[two]);
            let mul_m_zero = d.mul(mod_m, zero);
            let congr2 = d.congr(mod_zero_two, zero, zero_mod_2, &|d, x| d.mul(mod_m, x));
            let mul_zero_m = d.lemma(p.mul_zero, &[mod_m]);
            let (_, rhs_is_zero) = d.chain(rhs, &[(mul_m_zero, congr2), (zero, mul_zero_m)]);

            let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
            d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
        };

        let at_n_succ = |d: &mut NatDev<'_>, pn: ExprId| -> ExprId {
            let step = land_step(d, &p, pm, pn);
            mod_two_mul_add_of_lt(d, &p, step.recursive, step.combined, step.combined_lt_two)
        };

        cases_zero_succ(d, n, &motive_n, &at_n_zero, &at_n_succ)
    };

    cases_zero_succ(d, m, &motive_m, &at_m_zero, &at_m_succ)
}

/// `Eq (div (land m n) 2) (land (div m 2) (div n 2))`, for ALL `m`, `n`.
fn land_div_two(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let zero = d.zero();

    let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
        let land_mn = d.const_app(p.land, &[mm, n]);
        let lhs = d.div(land_mn, two);
        let half_m = d.div(mm, two);
        let half_n = d.div(n, two);
        let rhs = d.const_app(p.land, &[half_m, half_n]);
        d.eq(lhs, rhs)
    };

    let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
        let land_0n = d.const_app(p.land, &[zero, n]);
        let lhs = d.div(land_0n, two);
        let land_0n_eq_zero = d.lemma(p.land_zero_left, &[n]);
        let div_zero_two = d.div(zero, two);
        let congr1 = d.congr(land_0n, zero, land_0n_eq_zero, &|d, x| d.div(x, two));
        let zero_div_1 = d.lemma(p.zero_div, &[two]);
        let (_, lhs_is_zero) = d.chain(lhs, &[(div_zero_two, congr1), (zero, zero_div_1)]);

        let half_n = d.div(n, two);
        let rhs = d.const_app(p.land, &[div_zero_two, half_n]);
        let zero_div_2 = d.lemma(p.zero_div, &[two]);
        let land_zero_half_n = d.const_app(p.land, &[zero, half_n]);
        let congr2 = d.congr(div_zero_two, zero, zero_div_2, &|d, x| {
            d.const_app(p.land, &[x, half_n])
        });
        let land_zero_left_half_n = d.lemma(p.land_zero_left, &[half_n]);
        let (_, rhs_is_zero) = d.chain(
            rhs,
            &[(land_zero_half_n, congr2), (zero, land_zero_left_half_n)],
        );

        let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
        d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
    };

    let at_m_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
        let m_succ = d.succ(pm);
        let half_m = d.div(m_succ, two);

        let motive_n = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let land_mn = d.const_app(p.land, &[m_succ, nn]);
            let lhs = d.div(land_mn, two);
            let half_m = d.div(m_succ, two);
            let half_n = d.div(nn, two);
            let rhs = d.const_app(p.land, &[half_m, half_n]);
            d.eq(lhs, rhs)
        };

        let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
            // `land`'s absorbing zero fires on BOTH sides (unlike `lor`):
            // `land (succ pm) 0 = 0`, so both LHS and RHS reduce to `zero`,
            // exactly `land_low_bit`'s `at_n_zero` shape.
            let land_m0 = d.const_app(p.land, &[m_succ, zero]);
            let lhs = d.div(land_m0, two);
            let land_m0_eq_zero = d.lemma(p.land_zero_right, &[m_succ]);
            let div_zero_two = d.div(zero, two);
            let congr1 = d.congr(land_m0, zero, land_m0_eq_zero, &|d, x| d.div(x, two));
            let zero_div_1 = d.lemma(p.zero_div, &[two]);
            let (_, lhs_is_zero) = d.chain(lhs, &[(div_zero_two, congr1), (zero, zero_div_1)]);

            let rhs = d.const_app(p.land, &[half_m, div_zero_two]);
            let zero_div_2 = d.lemma(p.zero_div, &[two]);
            let land_half_m_zero = d.const_app(p.land, &[half_m, zero]);
            let congr2 = d.congr(div_zero_two, zero, zero_div_2, &|d, x| {
                d.const_app(p.land, &[half_m, x])
            });
            let land_zero_right_half_m = d.lemma(p.land_zero_right, &[half_m]);
            let (_, rhs_is_zero) = d.chain(
                rhs,
                &[(land_half_m_zero, congr2), (zero, land_zero_right_half_m)],
            );

            let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
            d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
        };

        let at_n_succ = |d: &mut NatDev<'_>, pn: ExprId| -> ExprId {
            let step = land_step(d, &p, pm, pn);
            let two = d.num(2);

            let div_eq_recursive =
                div_two_mul_add_of_lt(d, &p, step.recursive, step.combined, step.combined_lt_two);
            let lhs = d.div(step.xn_reduced, two);

            let le_refl_half_m = d.lemma(p.le_refl, &[step.half_m]);
            let succ_pm = d.succ(pm);
            let bound = d.lemma(p.le_refl, &[succ_pm]);
            let le_half_m_pm = half_le_predecessor_of_succ(d, &p, pm, pm, bound);
            let agree = d.lemma(
                p.land_aux_agree_of_fuel,
                &[pm, step.half_m, step.half_n, step.half_m],
            );
            let agree = d.apply(agree, &[le_half_m_pm, le_refl_half_m]);
            let agree_rhs = d.const_app(p.land_aux, &[step.half_m, step.half_m, step.half_n]);

            d.trans(lhs, step.recursive, agree_rhs, div_eq_recursive, agree)
        };

        cases_zero_succ(d, n, &motive_n, &at_n_zero, &at_n_succ)
    };

    cases_zero_succ(d, m, &motive_m, &at_m_zero, &at_m_succ)
}

/// `fun x y => bool_select_nat (ble x y) y x` -- the per-bit OR combine
/// (`max` via `ble`/`bool_select_nat`, matching `lor.rs`'s own construction).
pub(super) fn lor_bit<D: NatOps>(d: &mut D, x: ExprId, y: ExprId) -> ExprId {
    let cond = d.ble(x, y);
    d.bool_select_nat(cond, y, x)
}

/// The pieces exposed by ONE step of `lorAux`'s recursor at `m := succ pm`,
/// `n := succ pn` -- the `lor` twin of `XorStep`/`xor_step`, minus the `f`
/// combinator argument `lorAux` doesn't take, and with `lor_bit` (`max`) in
/// place of the AND product.
struct LorStep {
    recursive: ExprId,
    combined: ExprId,
    combined_lt_two: ExprId,
    half_m: ExprId,
    half_n: ExprId,
    xn_reduced: ExprId,
}

fn lor_step(d: &mut NatDev<'_>, p: &NatPrelude, pm: ExprId, pn: ExprId) -> LorStep {
    let p = *p;
    let m_succ = d.succ(pm);
    let n_succ = d.succ(pn);
    let two = d.num(2);
    let half_m = d.div(m_succ, two);
    let half_n = d.div(n_succ, two);
    let recursive = d.const_app(p.lor_aux, &[pm, half_m, half_n]);
    let bit_m = d.modulo(m_succ, two);
    let bit_n = d.modulo(n_succ, two);
    let combined = lor_bit(d, bit_m, bit_n);
    let combined_lt_two = lor_bit_lt_two(d, &p, m_succ, n_succ);
    let doubled = d.mul(two, recursive);
    let xn_reduced = d.add(doubled, combined);
    LorStep {
        recursive,
        combined,
        combined_lt_two,
        half_m,
        half_n,
        xn_reduced,
    }
}

/// `Eq (mod (lor m n) 2) (lor_bit (mod m 2) (mod n 2))`, for ALL `m`, `n` --
/// the `lor` twin of `xor_low_bit`. `lor`'s boundary shape is IDENTICAL to
/// `xor`'s (`lor 0 n = n`, `lor m 0 = m`, both by `refl`), so this mirrors
/// `xor_low_bit`'s structure with `lor_bit`/`lor_aux`/`lor_zero_right`
/// substituted -- `lor` has its OWN direct `lor_zero_right`, so no
/// `bitwise_zero_right`-style detour is needed.
fn lor_low_bit(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;

    let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
        let two = d.num(2);
        let lor_mn = d.const_app(p.lor, &[mm, n]);
        let lhs = d.modulo(lor_mn, two);
        let mod_m = d.modulo(mm, two);
        let mod_n = d.modulo(n, two);
        let rhs = lor_bit(d, mod_m, mod_n);
        d.eq(lhs, rhs)
    };

    let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let one = d.num(1);
        let at_zero = d.refl(zero);
        let at_one = d.refl(one);
        cases_mod_two(
            d,
            &p,
            n,
            &|d, y| {
                let zero = d.zero();
                let lb = lor_bit(d, zero, y);
                d.eq(y, lb)
            },
            at_zero,
            at_one,
        )
    };

    let at_m_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
        let m_succ = d.succ(pm);

        let motive_n = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let two = d.num(2);
            let lor_mn = d.const_app(p.lor, &[m_succ, nn]);
            let lhs = d.modulo(lor_mn, two);
            let mod_m = d.modulo(m_succ, two);
            let mod_n = d.modulo(nn, two);
            let rhs = lor_bit(d, mod_m, mod_n);
            d.eq(lhs, rhs)
        };

        let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let one = d.num(1);
            let at_zero = d.refl(zero);
            let at_one = d.refl(one);
            cases_mod_two(
                d,
                &p,
                m_succ,
                &|d, x| {
                    let zero = d.zero();
                    let lb = lor_bit(d, x, zero);
                    d.eq(x, lb)
                },
                at_zero,
                at_one,
            )
        };

        let at_n_succ = |d: &mut NatDev<'_>, pn: ExprId| -> ExprId {
            let step = lor_step(d, &p, pm, pn);
            mod_two_mul_add_of_lt(d, &p, step.recursive, step.combined, step.combined_lt_two)
        };

        cases_zero_succ(d, n, &motive_n, &at_n_zero, &at_n_succ)
    };

    cases_zero_succ(d, m, &motive_m, &at_m_zero, &at_m_succ)
}

/// `Eq (div (lor m n) 2) (lor (div m 2) (div n 2))`, for ALL `m`, `n` -- the
/// `lor` twin of `xor_div_two`.
fn lor_div_two(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;

    let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
        // Both sides reduce to `div n 2` by `refl`: `lor 0 k = k` for
        // literal fuel `0` regardless of `k`'s shape, on either side.
        let two = d.num(2);
        let half_n = d.div(n, two);
        d.refl(half_n)
    };

    let at_m_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
        let m_succ = d.succ(pm);

        let motive_n = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let two = d.num(2);
            let lor_mn = d.const_app(p.lor, &[m_succ, nn]);
            let lhs = d.div(lor_mn, two);
            let half_m = d.div(m_succ, two);
            let half_n = d.div(nn, two);
            let rhs = d.const_app(p.lor, &[half_m, half_n]);
            d.eq(lhs, rhs)
        };

        let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
            // LHS reduces to `div m_succ 2` by `refl`. RHS needs
            // `lor_zero_right` at the SYMBOLIC `div m_succ 2`.
            let two = d.num(2);
            let zero = d.zero();
            let half_m = d.div(m_succ, two);
            let lor_half_m_zero = d.lemma(p.lor_zero_right, &[half_m]);
            let lhs_of_lzr = d.const_app(p.lor, &[half_m, zero]);
            d.symm(lhs_of_lzr, half_m, lor_half_m_zero)
        };

        let at_n_succ = |d: &mut NatDev<'_>, pn: ExprId| -> ExprId {
            let step = lor_step(d, &p, pm, pn);
            let two = d.num(2);

            let div_eq_recursive =
                div_two_mul_add_of_lt(d, &p, step.recursive, step.combined, step.combined_lt_two);
            let lhs = d.div(step.xn_reduced, two);

            let le_refl_half_m = d.lemma(p.le_refl, &[step.half_m]);
            let succ_pm = d.succ(pm);
            let bound = d.lemma(p.le_refl, &[succ_pm]);
            let le_half_m_pm = half_le_predecessor_of_succ(d, &p, pm, pm, bound);
            let agree = d.lemma(
                p.lor_aux_agree_of_fuel,
                &[pm, step.half_m, step.half_n, step.half_m],
            );
            let agree = d.apply(agree, &[le_half_m_pm, le_refl_half_m]);
            let agree_rhs = d.const_app(p.lor_aux, &[step.half_m, step.half_m, step.half_n]);

            d.trans(lhs, step.recursive, agree_rhs, div_eq_recursive, agree)
        };

        cases_zero_succ(d, n, &motive_n, &at_n_zero, &at_n_succ)
    };

    let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
        let two = d.num(2);
        let lor_mn = d.const_app(p.lor, &[mm, n]);
        let lhs = d.div(lor_mn, two);
        let half_m = d.div(mm, two);
        let half_n = d.div(n, two);
        let rhs = d.const_app(p.lor, &[half_m, half_n]);
        d.eq(lhs, rhs)
    };

    cases_zero_succ(d, m, &motive_m, &at_m_zero, &at_m_succ)
}

/// `Nat.testBit_lor : ∀ m n i, Eq (testBit (lor m n) i) (lor_bit (testBit m
/// i) (testBit n i))` -- the `lor` twin of `declare_test_bit_xor`/
/// `declare_test_bit_land`.
fn declare_test_bit_lor(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let lor_mn = d.const_app(p.lor, &[m, n]);
        let lhs = d.const_app(p.test_bit, &[lor_mn, x]);
        let tb_m = d.const_app(p.test_bit, &[m, x]);
        let tb_n = d.const_app(p.test_bit, &[n, x]);
        let rhs = lor_bit(d, tb_m, tb_n);
        let body = d.eq(lhs, rhs);
        let over_n = d.pi_fv(n_fv, nat, body);
        d.pi_fv(m_fv, nat, over_n)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let proof = lor_low_bit(d, &p, m, n);
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(m_fv, nat, with_n)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let half_m = d.div(m, two);
        let half_n = d.div(n, two);

        let ih_half = d.apply(ih, &[half_m, half_n]);

        let div_eq = lor_div_two(d, &p, m, n);

        let lor_mn = d.const_app(p.lor, &[m, n]);
        let half_lor_mn = d.div(lor_mn, two);
        let lor_half = d.const_app(p.lor, &[half_m, half_n]);

        let congr_step = d.congr(half_lor_mn, lor_half, div_eq, &|d, x| {
            d.const_app(p.test_bit, &[x, j])
        });

        let lhs = d.const_app(p.test_bit, &[half_lor_mn, j]);
        let mid = d.const_app(p.test_bit, &[lor_half, j]);
        let tb_half_m = d.const_app(p.test_bit, &[half_m, j]);
        let tb_half_n = d.const_app(p.test_bit, &[half_n, j]);
        let rhs = lor_bit(d, tb_half_m, tb_half_n);

        let proof = d.trans(lhs, mid, rhs, congr_step, ih_half);
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(m_fv, nat, with_n)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof_fn = d.induct(&motive, &base, &step, i);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.apply(proof_fn, &[m, n]);

    let stmt = {
        let lor_mn = d.const_app(p.lor, &[m, n]);
        let lhs = d.const_app(p.test_bit, &[lor_mn, i]);
        let tb_m = d.const_app(p.test_bit, &[m, i]);
        let tb_n = d.const_app(p.test_bit, &[n, i]);
        let rhs = lor_bit(d, tb_m, tb_n);
        d.eq(lhs, rhs)
    };
    let ty = {
        let over_i = d.pi_fv(i_fv, nat, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        d.pi_fv(m_fv, nat, over_n)
    };
    let value = {
        let over_i = d.lam_fv(i_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        d.lam_fv(m_fv, nat, over_n)
    };
    d.declare_theorem(p.test_bit_lor, ty, value)
}

/// `Nat.testBit_land : ∀ m n i, Eq (testBit (land m n) i) (mul (testBit m i)
/// (testBit n i))`. Induction on `i`; see the module doc.
fn declare_test_bit_land(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let land_mn = d.const_app(p.land, &[m, n]);
        let lhs = d.const_app(p.test_bit, &[land_mn, x]);
        let tb_m = d.const_app(p.test_bit, &[m, x]);
        let tb_n = d.const_app(p.test_bit, &[n, x]);
        let rhs = d.mul(tb_m, tb_n);
        let body = d.eq(lhs, rhs);
        let over_n = d.pi_fv(n_fv, nat, body);
        d.pi_fv(m_fv, nat, over_n)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let proof = land_low_bit(d, &p, m, n);
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(m_fv, nat, with_n)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let half_m = d.div(m, two);
        let half_n = d.div(n, two);

        let ih_half = d.apply(ih, &[half_m, half_n]);

        let div_eq = land_div_two(d, &p, m, n);

        let land_mn = d.const_app(p.land, &[m, n]);
        let half_land_mn = d.div(land_mn, two);
        let land_half = d.const_app(p.land, &[half_m, half_n]);

        let congr_step = d.congr(half_land_mn, land_half, div_eq, &|d, x| {
            d.const_app(p.test_bit, &[x, j])
        });

        let lhs = d.const_app(p.test_bit, &[half_land_mn, j]);
        let mid = d.const_app(p.test_bit, &[land_half, j]);
        let tb_half_m = d.const_app(p.test_bit, &[half_m, j]);
        let tb_half_n = d.const_app(p.test_bit, &[half_n, j]);
        let rhs = d.mul(tb_half_m, tb_half_n);

        let proof = d.trans(lhs, mid, rhs, congr_step, ih_half);
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(m_fv, nat, with_n)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof_fn = d.induct(&motive, &base, &step, i);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.apply(proof_fn, &[m, n]);

    let stmt = {
        let land_mn = d.const_app(p.land, &[m, n]);
        let lhs = d.const_app(p.test_bit, &[land_mn, i]);
        let tb_m = d.const_app(p.test_bit, &[m, i]);
        let tb_n = d.const_app(p.test_bit, &[n, i]);
        let rhs = d.mul(tb_m, tb_n);
        d.eq(lhs, rhs)
    };
    let ty = {
        let over_i = d.pi_fv(i_fv, nat, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        d.pi_fv(m_fv, nat, over_n)
    };
    let value = {
        let over_i = d.lam_fv(i_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        d.lam_fv(m_fv, nat, over_n)
    };
    d.declare_theorem(p.test_bit_land, ty, value)
}

/// Everything this module declares. `Nat.lt_xor_cases` itself is NOT
/// declared here — pieces 2-4 (see the module doc) are still needed.
pub(super) fn declare_testbit_bitwise_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_test_bit_xor(d, p)?;
    declare_test_bit_land(d, p)?;
    declare_test_bit_lor(d, p)?;
    Ok(())
}
