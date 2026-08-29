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
fn xor_bit(d: &mut NatDev<'_>, x: ExprId, y: ExprId) -> ExprId {
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

/// Everything this module declares. `Nat.lt_xor_cases` itself is NOT
/// declared here — pieces 2-4 (see the module doc) are still needed.
pub(super) fn declare_testbit_bitwise_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_test_bit_xor(d, p)?;
    Ok(())
}
