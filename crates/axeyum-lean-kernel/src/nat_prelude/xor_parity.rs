//! `Nat.even_xor : ∀ m n, Iff (Even (xor m n)) (Iff (Even m) (Even n))`
//! (`F:ml430-nat-even-xor-78a39432`) — the first consumer of `parity.rs`'s
//! parity <-> low-bit bridge (`even_iff_mod_two_eq_zero`).
//!
//! # Why the boundary cases need none of the bitwise machinery at all
//!
//! `xor 0 n` and `xor m 0` (for `m` already known `succ`-shaped) both reduce
//! to `n`/`m` by pure `refl` — `bitwise.rs`'s `zero_minor`/the `n = 0` guard
//! in `succ_minor` collapse immediately, independent of the other operand's
//! shape (see `xor.rs`'s own module doc: "XOR is `lor`-shaped,
//! `0 xor n = n`"). So at `m = 0` the whole goal is defeq to
//! `Iff (Even n) (Iff (Even 0) (Even n))`, and at `n = 0` (with `m` already
//! `succ`-shaped) it is defeq to `Iff (Even m) (Iff (Even m) (Even 0))` —
//! both closed by the generic "one side of an `Iff` is unconditionally true"
//! shape, needing only [`even_zero`], never `mod`.
//!
//! # The genuinely bitwise case
//!
//! With `m = succ pm`, `n = succ pn` both literal, `bitwise.rs`'s
//! `succ_minor` row fires (fuel `= m`, exhausting one step), and — because
//! `beq (succ _) zero` reduces to `false` regardless of the predecessor —
//! BOTH zero-guards (`n = 0`, `m = 0`) collapse to `false` by `refl`,
//! landing on the "genuinely bitwise" row:
//!
//! ```text
//! xor m n ≡ add (mul two (bitwiseAux xor_fn pm (m/2) (n/2))) combined_nat
//! combined_nat := bool_select_nat (xor_fn (beq (m%2) 1) (beq (n%2) 1)) 1 0
//! ```
//!
//! The higher-order recursive term is never inspected — only its LOW bit
//! matters, and doubling it erases it under `mod _ 2`. So the whole proof
//! needs exactly one new arithmetic fact, [`mod_two_mul_add_of_lt`]
//! (`parity.rs`), applied at `x := bitwiseAux xor_fn pm (m/2) (n/2)`,
//! `r := combined_nat`: `mod (xor m n) 2 = combined_nat`. Composing that
//! with `even_iff_mod_two_eq_zero` at `xor m n`, `m`, `n` reduces the whole
//! goal to a PURELY NUMERIC fact about `combined_nat`, `m % 2`, `n % 2` —
//! closed by [`cases_mod_two`] twice (four leaves, each a concrete
//! `Bool`/`Nat` computation), mirroring `rec_agreement.rs`'s `bit_agreement`
//! four-leaf shape but concluding an `Iff` at each leaf rather than an `Eq`.
//!
//! # `Nat.lt_xor_cases` stays open
//!
//! `F:ml430-nat-lt-xor-cases-c43a1e85` needs a highest-differing-bit
//! induction (Mathlib's own proof inducts on `testBit` disagreement) with no
//! foothold this file's per-bit-at-the-boundary technique provides — see
//! `docs/plan/status/254-nat-parity-lowbit.md`.

use super::NatPrelude;
use super::bitwise::xor_fn;
use super::ops::{NatDev, NatOps, cases_mod_two, cases_zero_succ};
use super::parity::even_predicate;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.even_zero : Even 0`, witnessed by `0` (`0 = 0 + 0`, refl). Kept
/// local (not a named theorem) since nothing else needs it — the boundary
/// cases below are its only consumers.
fn even_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();
    let pred = even_predicate(d, zero);
    let one_lvl = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
    let refl_zero = d.refl(zero);
    d.apply(intro, &[nat, pred, zero, refl_zero])
}

/// `Iff A B` when both `A` and `B` are already proved true — ignore the
/// hypothesis on each side and hand back the other side's proof.
pub(super) fn iff_of_true_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a_ty: ExprId,
    b_ty: ExprId,
    proof_a: ExprId,
    proof_b: ExprId,
) -> ExprId {
    let p = *p;
    let a_fv = d.fresh_fvar();
    let mp = d.lam_fv(a_fv, a_ty, proof_b);
    let b_fv = d.fresh_fvar();
    let mpr = d.lam_fv(b_fv, b_ty, proof_a);
    d.const_app(p.logic.iff_intro, &[a_ty, b_ty, mp, mpr])
}

/// `Iff A B` when both `A` and `B` are already refuted — from either
/// hypothesis, derive `False` via the OTHER side's refutation and eliminate.
pub(super) fn iff_of_false_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a_ty: ExprId,
    b_ty: ExprId,
    not_a: ExprId,
    not_b: ExprId,
) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let level_zero = d.kernel().level_zero();

    let mp = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let false_from_a = d.apply(not_a, &[a]);
        let motive = d.kernel().lam(anon, false_ty, b_ty, BinderInfo::Default);
        let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let b_from_false = d.apply(rec, &[motive, false_from_a]);
        d.lam_fv(a_fv, a_ty, b_from_false)
    };
    let mpr = {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let false_from_b = d.apply(not_b, &[b]);
        let motive = d.kernel().lam(anon, false_ty, a_ty, BinderInfo::Default);
        let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let a_from_false = d.apply(rec, &[motive, false_from_b]);
        d.lam_fv(b_fv, b_ty, a_from_false)
    };
    d.const_app(p.logic.iff_intro, &[a_ty, b_ty, mp, mpr])
}

/// `h1 : Iff A B, h2 : Iff B C  ⊢  Iff A C`.
pub(super) fn iff_trans(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a_ty: ExprId,
    b_ty: ExprId,
    c_ty: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = *p;
    let mp = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let h1_mp = d.const_app(p.logic.iff_mp, &[a_ty, b_ty, h1]);
        let b_from_a = d.apply(h1_mp, &[a]);
        let h2_mp = d.const_app(p.logic.iff_mp, &[b_ty, c_ty, h2]);
        let c_from_b = d.apply(h2_mp, &[b_from_a]);
        d.lam_fv(a_fv, a_ty, c_from_b)
    };
    let mpr = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let h2_mpr = d.const_app(p.logic.iff_mpr, &[b_ty, c_ty, h2]);
        let b_from_c = d.apply(h2_mpr, &[c]);
        let h1_mpr = d.const_app(p.logic.iff_mpr, &[a_ty, b_ty, h1]);
        let a_from_b = d.apply(h1_mpr, &[b_from_c]);
        d.lam_fv(c_fv, c_ty, a_from_b)
    };
    d.const_app(p.logic.iff_intro, &[a_ty, c_ty, mp, mpr])
}

/// `h : Iff A B  ⊢  Iff B A`.
pub(super) fn iff_symm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a_ty: ExprId,
    b_ty: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let mp = d.const_app(p.logic.iff_mpr, &[a_ty, b_ty, h]);
    let mpr = d.const_app(p.logic.iff_mp, &[a_ty, b_ty, h]);
    d.const_app(p.logic.iff_intro, &[b_ty, a_ty, mp, mpr])
}

/// Given `bridge_p : Iff P P2` and `bridge_q : Iff Q Q2`, produce
/// `Iff (Iff P Q) (Iff P2 Q2)` — composing through `iff_trans`/`iff_symm`
/// rather than building the four-way case analysis by hand.
#[allow(clippy::too_many_arguments)]
fn iff_congr_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_ty: ExprId,
    p2_ty: ExprId,
    q_ty: ExprId,
    q2_ty: ExprId,
    bridge_p: ExprId,
    bridge_q: ExprId,
) -> ExprId {
    let p = *p;
    let iff_pq_ty = d.const_app(p.logic.iff, &[p_ty, q_ty]);
    let iff_p2q2_ty = d.const_app(p.logic.iff, &[p2_ty, q2_ty]);

    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let bridge_p_symm = iff_symm(d, &p, p_ty, p2_ty, bridge_p);
        let step1 = iff_trans(d, &p, p2_ty, p_ty, q_ty, bridge_p_symm, h);
        let step2 = iff_trans(d, &p, p2_ty, q_ty, q2_ty, step1, bridge_q);
        d.lam_fv(h_fv, iff_pq_ty, step2)
    };
    let mpr = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let bridge_q_symm = iff_symm(d, &p, q_ty, q2_ty, bridge_q);
        let step1 = iff_trans(d, &p, p_ty, p2_ty, q2_ty, bridge_p, h);
        let step2 = iff_trans(d, &p, p_ty, q2_ty, q_ty, step1, bridge_q_symm);
        d.lam_fv(h_fv, iff_p2q2_ty, step2)
    };
    d.const_app(p.logic.iff_intro, &[iff_pq_ty, iff_p2q2_ty, mp, mpr])
}

/// `fun x y => bool_select_nat (xor_fn (beq x 1) (beq y 1)) 1 0` — the
/// per-bit XOR combine, built generically over `x`, `y` so it can be
/// evaluated both symbolically (as the goal's own `combined_nat`) and at
/// the four concrete `{0, 1}` corners `cases_mod_two` supplies.
fn xor_bit(d: &mut NatDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let x_bool = d.beq(x, one);
    let y_bool = d.beq(y, one);
    let xor_ = xor_fn(d);
    let combined = d.apply(xor_, &[x_bool, y_bool]);
    d.bool_select_nat(combined, one, zero)
}

/// `Iff (Eq (xor_bit x y) 0) (Iff (Eq x 0) (Eq y 0))` — the motive
/// `cases_mod_two` instantiates at each of the four `{0, 1}` corners.
fn xor_bit_claim(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let bit = xor_bit(d, x, y);
    let bit_eq_zero_ty = d.eq(bit, zero);
    let x_eq_zero_ty = d.eq(x, zero);
    let y_eq_zero_ty = d.eq(y, zero);
    let inner_ty = d.const_app(p.logic.iff, &[x_eq_zero_ty, y_eq_zero_ty]);
    d.const_app(p.logic.iff, &[bit_eq_zero_ty, inner_ty])
}

/// One leaf of the four-leaf case split: `x`, `y` are the LITERAL `0`/`1`
/// `cases_mod_two` substitutes, `x_is_zero`/`y_is_zero` say which. `xor_bit`
/// computes to `0` whenever the two bits AGREE (both `0` or both `1` — XOR
/// cancels) and to `1` whenever they DISAGREE, which is exactly
/// `x_is_zero == y_is_zero`; the inner `Iff (Eq x 0) (Eq y 0)` is
/// PROVABLE when the bits agree (both branches genuinely true, or both
/// genuinely false — an `Iff` of two false props is itself true) and
/// REFUTABLE when they disagree.
fn xor_bit_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    y: ExprId,
    x_is_zero: bool,
    y_is_zero: bool,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let bit = xor_bit(d, x, y);
    let bit_eq_zero_ty = d.eq(bit, zero);
    let x_eq_zero_ty = d.eq(x, zero);
    let y_eq_zero_ty = d.eq(y, zero);
    let inner_ty = d.const_app(p.logic.iff, &[x_eq_zero_ty, y_eq_zero_ty]);

    if x_is_zero == y_is_zero {
        // Bits agree: `xor_bit x y` reduces to `0` by refl either way.
        let bit_eq_zero = d.refl(bit);
        let inner_iff = if x_is_zero {
            let x_eq_zero = d.refl(zero);
            let y_eq_zero = d.refl(zero);
            iff_of_true_true(d, &p, x_eq_zero_ty, y_eq_zero_ty, x_eq_zero, y_eq_zero)
        } else {
            let not_x = d.lemma(p.succ_ne_zero, &[zero]);
            let not_y = d.lemma(p.succ_ne_zero, &[zero]);
            iff_of_false_false(d, &p, x_eq_zero_ty, y_eq_zero_ty, not_x, not_y)
        };
        iff_of_true_true(d, &p, bit_eq_zero_ty, inner_ty, bit_eq_zero, inner_iff)
    } else {
        // Bits disagree: `xor_bit x y` reduces to `1`, refuted; the inner
        // iff is refuted by transporting the TRUE side's proof across it
        // and contradicting the FALSE side's refutation.
        let not_bit_eq_zero = d.lemma(p.succ_ne_zero, &[zero]);
        let not_inner = if x_is_zero {
            let x_eq_zero = d.refl(zero);
            let not_y = d.lemma(p.succ_ne_zero, &[zero]);
            let hiff_fv = d.fresh_fvar();
            let hiff = d.kernel().fvar(hiff_fv);
            let mp_fn = d.const_app(p.logic.iff_mp, &[x_eq_zero_ty, y_eq_zero_ty, hiff]);
            let y_from_x = d.apply(mp_fn, &[x_eq_zero]);
            let false_proof = d.apply(not_y, &[y_from_x]);
            d.lam_fv(hiff_fv, inner_ty, false_proof)
        } else {
            let y_eq_zero = d.refl(zero);
            let not_x = d.lemma(p.succ_ne_zero, &[zero]);
            let hiff_fv = d.fresh_fvar();
            let hiff = d.kernel().fvar(hiff_fv);
            let mpr_fn = d.const_app(p.logic.iff_mpr, &[x_eq_zero_ty, y_eq_zero_ty, hiff]);
            let x_from_y = d.apply(mpr_fn, &[y_eq_zero]);
            let false_proof = d.apply(not_x, &[x_from_y]);
            d.lam_fv(hiff_fv, inner_ty, false_proof)
        };
        iff_of_false_false(d, &p, bit_eq_zero_ty, inner_ty, not_bit_eq_zero, not_inner)
    }
}

/// `Iff (Eq (xor_bit bit_m bit_n) 0) (Iff (Eq bit_m 0) (Eq bit_n 0))`,
/// universally over `bit_m := mod m_succ 2`, `bit_n := mod n_succ 2` — the
/// purely numeric fact the bitwise case reduces to, via [`cases_mod_two`]
/// twice (mirrors `rec_agreement.rs`'s `bit_agreement` nesting).
fn xor_bit_numeric_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m_succ: ExprId,
    n_succ: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let bit_n = d.modulo(n_succ, two);

    let inner = |d: &mut NatDev<'_>, x: ExprId, x_is_zero: bool| -> ExprId {
        let zero = d.zero();
        let one = d.num(1);
        let at_zero = xor_bit_leaf(d, &p, x, zero, x_is_zero, true);
        let at_one = xor_bit_leaf(d, &p, x, one, x_is_zero, false);
        cases_mod_two(
            d,
            &p,
            n_succ,
            &|d, y| xor_bit_claim(d, &p, x, y),
            at_zero,
            at_one,
        )
    };

    let zero = d.zero();
    let one = d.num(1);
    let outer_zero = inner(d, zero, true);
    let outer_one = inner(d, one, false);
    cases_mod_two(
        d,
        &p,
        m_succ,
        &|d, x| xor_bit_claim(d, &p, x, bit_n),
        outer_zero,
        outer_one,
    )
}

/// The genuinely bitwise case: `m = succ pm`, `n = succ pn` both literal.
/// One step of `bitwiseAux`'s recursor exposes the per-bit combine; the
/// higher-order recursive term (`bitwiseAux xor_fn pm (m/2) (n/2)`) is
/// never inspected, only bound as `recursive` so `mod_two_mul_add_of_lt`
/// can erase it.
fn even_xor_hard_case(d: &mut NatDev<'_>, p: &NatPrelude, pm: ExprId, pn: ExprId) -> ExprId {
    let p = *p;
    let m_succ = d.succ(pm);
    let n_succ = d.succ(pn);
    let two = d.num(2);
    let zero = d.zero();

    let half_m = d.div(m_succ, two);
    let half_n = d.div(n_succ, two);
    let xor_ = xor_fn(d);
    let recursive = d.const_app(p.bitwise_aux, &[xor_, pm, half_m, half_n]);
    let bit_m = d.modulo(m_succ, two);
    let bit_n = d.modulo(n_succ, two);
    let combined = xor_bit(d, bit_m, bit_n);
    let doubled = d.mul(two, recursive);
    let xn_reduced = d.add(doubled, combined);

    // `Lt combined two`: `combined` is `bool_select_nat cond 1 0` for a
    // (possibly symbolic) `Bool` `cond` -- decide it directly by `Bool.rec`.
    let combined_lt_two = {
        let one = d.num(1);
        let bit_m_bool = d.beq(bit_m, one);
        let bit_n_bool = d.beq(bit_n, one);
        let cond = d.apply(xor_, &[bit_m_bool, bit_n_bool]);
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

    let mod_xn_eq_combined =
        super::parity::mod_two_mul_add_of_lt(d, &p, recursive, combined, combined_lt_two);

    let even_xn_ty = d.lemma(p.even, &[xn_reduced]);
    let mod_xn_two = d.modulo(xn_reduced, two);
    let mod_xn_eq_zero_ty = d.eq(mod_xn_two, zero);
    let combined_eq_zero_ty = d.eq(combined, zero);

    let mod_to_combined_iff = {
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let rev = d.symm(mod_xn_two, combined, mod_xn_eq_combined);
            let res = d.trans(combined, mod_xn_two, zero, rev, h);
            d.lam_fv(h_fv, mod_xn_eq_zero_ty, res)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let res = d.trans(mod_xn_two, combined, zero, mod_xn_eq_combined, h);
            d.lam_fv(h_fv, combined_eq_zero_ty, res)
        };
        d.const_app(
            p.logic.iff_intro,
            &[mod_xn_eq_zero_ty, combined_eq_zero_ty, mp, mpr],
        )
    };

    let even_xn_bridge = d.lemma(p.even_iff_mod_two_eq_zero, &[xn_reduced]);
    let even_xn_to_combined = iff_trans(
        d,
        &p,
        even_xn_ty,
        mod_xn_eq_zero_ty,
        combined_eq_zero_ty,
        even_xn_bridge,
        mod_to_combined_iff,
    );

    let numeric_iff = xor_bit_numeric_iff(d, &p, m_succ, n_succ);
    let bit_m_eq_zero_ty = d.eq(bit_m, zero);
    let bit_n_eq_zero_ty = d.eq(bit_n, zero);
    let bits_iff_ty = d.const_app(p.logic.iff, &[bit_m_eq_zero_ty, bit_n_eq_zero_ty]);

    let even_m_ty = d.lemma(p.even, &[m_succ]);
    let even_n_ty = d.lemma(p.even, &[n_succ]);
    let even_m_bridge = d.lemma(p.even_iff_mod_two_eq_zero, &[m_succ]);
    let even_n_bridge = d.lemma(p.even_iff_mod_two_eq_zero, &[n_succ]);
    let parity_cong = iff_congr_iff(
        d,
        &p,
        even_m_ty,
        bit_m_eq_zero_ty,
        even_n_ty,
        bit_n_eq_zero_ty,
        even_m_bridge,
        even_n_bridge,
    );
    let evenmn_ty = d.const_app(p.logic.iff, &[even_m_ty, even_n_ty]);
    let parity_cong_symm = iff_symm(d, &p, evenmn_ty, bits_iff_ty, parity_cong);

    let step1 = iff_trans(
        d,
        &p,
        even_xn_ty,
        combined_eq_zero_ty,
        bits_iff_ty,
        even_xn_to_combined,
        numeric_iff,
    );
    iff_trans(
        d,
        &p,
        even_xn_ty,
        bits_iff_ty,
        evenmn_ty,
        step1,
        parity_cong_symm,
    )
}

fn declare_even_xor(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.even_xor, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);

        let goal_at = |d: &mut NatDev<'_>, mx: ExprId, nx: ExprId| -> ExprId {
            let xor_mn = d.const_app(p.xor, &[mx, nx]);
            let even_xor_ty = d.lemma(p.even, &[xor_mn]);
            let even_m_ty = d.lemma(p.even, &[mx]);
            let even_n_ty = d.lemma(p.even, &[nx]);
            let inner = d.const_app(p.logic.iff, &[even_m_ty, even_n_ty]);
            d.const_app(p.logic.iff, &[even_xor_ty, inner])
        };

        let motive = |d: &mut NatDev<'_>, mx: ExprId| -> ExprId { goal_at(d, mx, n) };

        let proof = cases_zero_succ(
            d,
            m,
            &motive,
            &|d| {
                // m = 0: `xor 0 n` reduces (refl) to `n`. Build a proof of
                // `Iff (Even n) (Iff (Even 0) (Even n))` -- defeq to the
                // stated goal at `m := 0`.
                let even0 = even_zero(d, &p);
                let zero = d.zero();
                let even0_ty = d.lemma(p.even, &[zero]);
                let even_n_ty = d.lemma(p.even, &[n]);
                let inner_ty = d.const_app(p.logic.iff, &[even0_ty, even_n_ty]);

                let mp = {
                    let hn_fv = d.fresh_fvar();
                    let hn = d.kernel().fvar(hn_fv);
                    let inner_mp = {
                        let a_fv = d.fresh_fvar();
                        d.lam_fv(a_fv, even0_ty, hn)
                    };
                    let inner_mpr = {
                        let b_fv = d.fresh_fvar();
                        d.lam_fv(b_fv, even_n_ty, even0)
                    };
                    let inner_iff = d.const_app(
                        p.logic.iff_intro,
                        &[even0_ty, even_n_ty, inner_mp, inner_mpr],
                    );
                    d.lam_fv(hn_fv, even_n_ty, inner_iff)
                };
                let mpr = {
                    let hiff_fv = d.fresh_fvar();
                    let hiff = d.kernel().fvar(hiff_fv);
                    let mp_fn = d.const_app(p.logic.iff_mp, &[even0_ty, even_n_ty, hiff]);
                    let hn_from = d.apply(mp_fn, &[even0]);
                    d.lam_fv(hiff_fv, inner_ty, hn_from)
                };
                d.const_app(p.logic.iff_intro, &[even_n_ty, inner_ty, mp, mpr])
            },
            &|d, pm| {
                let m_succ = d.succ(pm);
                cases_zero_succ(
                    d,
                    n,
                    &|d, nx| goal_at(d, m_succ, nx),
                    &|d| {
                        // n = 0, m = succ pm already: `xor m 0` reduces
                        // (refl) to `m`. Build a proof of
                        // `Iff (Even m) (Iff (Even m) (Even 0))`.
                        let even0 = even_zero(d, &p);
                        let zero = d.zero();
                        let even0_ty = d.lemma(p.even, &[zero]);
                        let even_m_ty = d.lemma(p.even, &[m_succ]);
                        let inner_ty = d.const_app(p.logic.iff, &[even_m_ty, even0_ty]);

                        let mp = {
                            let hm_fv = d.fresh_fvar();
                            let hm = d.kernel().fvar(hm_fv);
                            let inner_mp = {
                                let a_fv = d.fresh_fvar();
                                d.lam_fv(a_fv, even_m_ty, even0)
                            };
                            let inner_mpr = {
                                let b_fv = d.fresh_fvar();
                                d.lam_fv(b_fv, even0_ty, hm)
                            };
                            let inner_iff = d.const_app(
                                p.logic.iff_intro,
                                &[even_m_ty, even0_ty, inner_mp, inner_mpr],
                            );
                            d.lam_fv(hm_fv, even_m_ty, inner_iff)
                        };
                        let mpr = {
                            let hiff_fv = d.fresh_fvar();
                            let hiff = d.kernel().fvar(hiff_fv);
                            let mpr_fn = d.const_app(p.logic.iff_mpr, &[even_m_ty, even0_ty, hiff]);
                            let hm_from = d.apply(mpr_fn, &[even0]);
                            d.lam_fv(hiff_fv, inner_ty, hm_from)
                        };
                        d.const_app(p.logic.iff_intro, &[even_m_ty, inner_ty, mp, mpr])
                    },
                    &|d, pn| even_xor_hard_case(d, &p, pm, pn),
                )
            },
        );
        (goal_at(d, m, n), proof)
    })?;
    Ok(())
}

/// Declare `Nat.even_xor`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_xor_parity_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_even_xor(d, p)?;
    Ok(())
}
