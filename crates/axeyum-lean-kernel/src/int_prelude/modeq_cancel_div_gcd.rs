//! `Int.ModEq.cancel_left_div_gcd`/`cancel_right_div_gcd` -- the ℤ mirrors
//! of `nat_prelude/modeq_cancel_div_gcd.rs`'s Nat family:
//!
//! - `Int.ModEq.cancel_left_div_gcd`
//!   (`F:ml430-int-modeq-cancel-left-div-gcd-b2d407e8`):
//!   `0 < m -> c*a ≡ c*b [ZMOD m] -> a ≡ b [ZMOD m / ↑(m.gcd c)]`.
//! - `Int.ModEq.cancel_right_div_gcd`
//!   (`F:ml430-int-modeq-cancel-right-div-gcd-00cd73fa`):
//!   `0 < m -> a*c ≡ b*c [ZMOD m] -> a ≡ b [ZMOD m / ↑(m.gcd c)]`.
//!
//! `int-dvd-mirrors` (`docs/plan/status/335-int-dvd-mirrors.md`) left these
//! open, sized as needing "new machinery relating `c*(b-a)` divisibility by
//! `m` to `(b-a)` divisibility by `m/gcd(m,c)`, built from
//! `gcd_div_gcd_div_gcd`". `Int.gcd_div_gcd_div_gcd` already existed
//! (`gcd.rs`) by the time this lane started; what was genuinely missing --
//! and is new in this file -- is a way to CANCEL a shared nonzero factor
//! from an `Int.dvd` statement. This development has no `Int` multiplicative
//! cancellation lemma under any name (every existing use of
//! `mul_left_cancel_of_pos` routes through `Nat.mul_left_cancel_of_pos` on
//! `natAbs` quantities instead, e.g. `gcd_div_gcd_div_gcd`'s own proof) --
//! [`imul_left_cancel_of_ne`] is the first, built from `Int.mul_eq_zero`
//! (ℤ has no zero divisors) plus basic `add`/`neg`/`sub` algebra, no case
//! split needed.
//!
//! # The argument
//!
//! With `g := ofNat (gcd m c)`, `qm := m.ediv g`, `qc := c.ediv g`:
//!
//! 1. `g > 0` (as a `Nat`), via `natAbs m > 0` (from `0 < m`,
//!    [`pos_nat_abs_of_pos`]) and `Nat.gcd_dvd_left`/`Nat.one_le_of_dvd_pos`
//!    applied directly to `natAbs m`/`natAbs c` -- `Int.gcd m c` unfolds to
//!    exactly `Nat.gcd (natAbs m) (natAbs c)` by definition, so this needs no
//!    bridge lemma, only defeq.
//! 2. `m = g*qm`, `c = g*qc` exactly ([`iexact`], mirroring `gcd.rs`'s
//!    private `exact` closure inside `declare_gcd_div_gcd_div_gcd` -- same
//!    construction, extracted as its own function since this file needs it
//!    twice with a different divisor's positivity witness reused for both,
//!    exactly as that closure reuses its capture).
//! 3. `gcd qm qc = 1` directly from `Int.gcd_div_gcd_div_gcd(m, c, pos)`.
//! 4. The hypothesis `ModEq m (c*a) (c*b)` bridges to `dvd m (c*(b-a))`
//!    (`modeq_to_dvd` + `Int.mul_sub`, both already unconditional), then
//!    rewrites through `m = g*qm`, `c = g*qc` to
//!    `dvd (g*qm) (g*(qc*(b-a)))`, and [`idvd_cancel_scale`] cancels the
//!    shared `g` (nonzero, from step 1) to reach `dvd qm (qc*(b-a))`.
//! 5. `Int.gauss_lemma` (coprime `qm qc`, `qm ∣ qc*(b-a)`) gives
//!    `qm ∣ (b-a)`, and `dvd_to_modeq` closes it as `ModEq qm a b`.
//!
//! `cancel_right_div_gcd` is not re-derived: it commutes to
//! `cancel_left_div_gcd` via `Int.mul_comm`, exactly Mathlib's own proof and
//! exactly how the Nat mirror closes the same way.

use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.natAbs a`. Local copy (every file in this development keeps its own,
/// per the established convention -- see `gcd.rs`'s module doc).
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// `Int.gcd a b`. Local copy.
fn igcd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().gcd;
    d.const_app(f, &[a, b])
}

/// From `h : Eq Int p q` and an `Int -> Nat` context `f`, derive
/// `Eq Nat (f p) (f q)`. Local copy of `gcd.rs`'s private `icongr_nat`.
fn icongr_nat(
    d: &mut IntDev<'_>,
    p: ExprId,
    q: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fp = f(d, p);
    let motive = d.ieq_motive(p, &|d, x| {
        let fx = f(d, x);
        d.eq(fp, fx)
    });
    let refl_case = d.refl(fp);
    d.itransport(p, motive, refl_case, q, h)
}

/// Eliminate `witness : Exists Int predicate` into `target`, given
/// `minor : ∀ (u : Int), predicate u → target`. Local copy of the same
/// combinator `gcd.rs`/`euler.rs`/`euler_totient.rs`/`crt.rs`/
/// `dvd_gcd_mirrors.rs` each keep.
fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, predicate])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// `Int.lt zero x -> Nat.lt zero (natAbs x)`. Bridges `Int` positivity to
/// `Nat` positivity of the magnitude, via `Int.of_nat_nat_abs_of_nonneg`
/// (`ofNat (natAbs x) = x` for `x ≥ 0`) and the fact that
/// `Int.lt (ofNat a) (ofNat b)` unfolds to exactly `Nat.lt a b`.
fn pos_nat_abs_of_pos(d: &mut IntDev<'_>, x: ExprId, hx: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let le_i = d.const_app(p.le_of_lt, &[zero_i, x, hx]); // Ile zero_i x
    let nax = nat_abs(d, x);
    let of_nax = d.of_nat(nax);
    let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[x, le_i]); // Eq Int of_nax x
    let bridge_rev = d.isymm(of_nax, x, bridge); // Eq Int x of_nax
    let motive = d.ieq_motive(x, &|d, y| d.ilt(zero_i, y));
    d.itransport(x, motive, hx, of_nax, bridge_rev)
}

/// `Nat.lt zero n -> Not (Eq Int (ofNat n) zero)`. Via `natAbs`: assuming
/// `ofNat n = zero`, congruence by `natAbs` gives (up to the `natAbs (ofNat
/// n) ≡ n` / `natAbs zero ≡ zero` reductions) `Eq Nat n zero`, transported
/// into the hypothesis `Nat.lt zero n` to reach `Nat.lt zero zero`, refuted
/// by `Nat.not_succ_le_zero`.
fn int_ne_zero_of_nat_pos(d: &mut IntDev<'_>, n: ExprId, hpos: ExprId) -> ExprId {
    let p = d.int();
    let zero_n = d.zero();
    let of_n = d.of_nat(n);
    let zero_i = d.izero();
    let eq_ty = d.ieq(of_n, zero_i);
    let eq_fv = d.fresh_fvar();
    let eq_proof = d.kernel().fvar(eq_fv);

    let nat_abs_congr = icongr_nat(d, of_n, zero_i, eq_proof, &|d, y| nat_abs(d, y));
    // nat_abs_congr : Eq Nat (natAbs of_n) (natAbs zero_i), defeq Eq Nat n zero_n

    let motive = d.eq_motive(n, &|d, x| d.lt(zero_n, x));
    let transported = d.transport(n, motive, hpos, zero_n, nat_abs_congr);
    // transported : Nat.lt zero_n zero_n, defeq Nat.le (succ zero_n) zero_n

    let false_pf = d.lemma(p.nat.not_succ_le_zero, &[zero_n, transported]);
    d.lam_fv(eq_fv, eq_ty, false_pf)
}

/// `Eq Int x y -> Eq Int (sub x y) zero`. Small algebraic step, not present
/// anywhere in this development under any name.
fn ieq_sub_eq_zero_of_eq(d: &mut IntDev<'_>, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let neg_y = d.ineg(y);
    let x_negy = d.iadd(x, neg_y);
    let sub_xy = d.isub(x, y);
    let add_neg_eq_sub_proof = d.const_app(p.add_neg_eq_sub, &[x, y]); // Eq x_negy sub_xy
    let sub_xy_eq_x_negy = d.isymm(x_negy, sub_xy, add_neg_eq_sub_proof); // Eq sub_xy x_negy

    let y_negy = d.iadd(y, neg_y);
    let step = d.icongr(x, y, h, &|d, t| d.iadd(t, neg_y)); // Eq x_negy y_negy
    let add_neg_y = d.const_app(p.add_neg, &[y]); // Eq y_negy zero

    let (_, chained) = d.ichain(
        sub_xy,
        &[
            (x_negy, sub_xy_eq_x_negy),
            (y_negy, step),
            (zero_i, add_neg_y),
        ],
    );
    chained
}

/// `Eq Int (sub a b) zero -> Eq Int a b`. The converse algebraic step.
fn ieq_of_sub_eq_zero(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let neg_b = d.ineg(b);
    let sub_ab = d.isub(a, b);
    let a_negb = d.iadd(a, neg_b);
    let a_zero = d.iadd(a, zero_i);

    let add_zero_a = d.const_app(p.add_zero, &[a]); // Eq a_zero a
    let step1 = d.isymm(a_zero, a, add_zero_a); // Eq a a_zero

    let neg_b_b = d.iadd(neg_b, b);
    let add_left_neg_b = d.const_app(p.add_left_neg, &[b]); // Eq neg_b_b zero
    let zero_eq_negbb = d.isymm(neg_b_b, zero_i, add_left_neg_b); // Eq zero neg_b_b
    let a_negbb = d.iadd(a, neg_b_b);
    let step2 = d.icongr(zero_i, neg_b_b, zero_eq_negbb, &|d, x| d.iadd(a, x)); // Eq a_zero a_negbb

    let assoc = d.const_app(p.add_assoc, &[a, neg_b, b]); // Eq (add a_negb b) a_negbb
    let a_negb_b = d.iadd(a_negb, b);
    let step3 = d.isymm(a_negb_b, a_negbb, assoc); // Eq a_negbb a_negb_b

    let add_neg_eq_sub_proof = d.const_app(p.add_neg_eq_sub, &[a, b]); // Eq a_negb sub_ab
    let sub_ab_b = d.iadd(sub_ab, b);
    let step4 = d.icongr(a_negb, sub_ab, add_neg_eq_sub_proof, &|d, x| d.iadd(x, b)); // Eq a_negb_b sub_ab_b

    let zero_b = d.iadd(zero_i, b);
    let step5 = d.icongr(sub_ab, zero_i, h, &|d, x| d.iadd(x, b)); // Eq sub_ab_b zero_b

    let b_zero = d.iadd(b, zero_i);
    let step6 = d.const_app(p.add_comm, &[zero_i, b]); // Eq zero_b b_zero
    let step7 = d.const_app(p.add_zero, &[b]); // Eq b_zero b

    let (_, chained) = d.ichain(
        a,
        &[
            (a_zero, step1),
            (a_negbb, step2),
            (a_negb_b, step3),
            (sub_ab_b, step4),
            (zero_b, step5),
            (b_zero, step6),
            (b, step7),
        ],
    );
    chained
}

/// `Not (Eq Int c zero) -> Eq Int (mul c a) (mul c b) -> Eq Int a b`. The
/// FIRST `Int` multiplicative cancellation lemma in this development (every
/// prior use of `mul_left_cancel_of_pos` routed through the `Nat` version on
/// `natAbs` quantities instead). Via `Int.mul_eq_zero` (ℤ has no zero
/// divisors): `c*(a-b) = c*a - c*b = 0` forces `c = 0` or `a-b = 0`; the
/// first is excluded by hypothesis.
fn imul_left_cancel_of_ne(
    d: &mut IntDev<'_>,
    c: ExprId,
    a: ExprId,
    b: ExprId,
    hc_ne: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let ca = d.imul(c, a);
    let cb = d.imul(c, b);
    let sub_ab = d.isub(a, b);
    let c_sub_ab = d.imul(c, sub_ab);
    let sub_ca_cb = d.isub(ca, cb);

    let msub = d.const_app(p.mul_sub, &[c, a, b]); // Eq c_sub_ab sub_ca_cb
    let sub_ca_cb_eq_zero = ieq_sub_eq_zero_of_eq(d, ca, cb, heq); // Eq sub_ca_cb zero

    let (_, c_sub_ab_eq_zero) =
        d.ichain(c_sub_ab, &[(sub_ca_cb, msub), (zero_i, sub_ca_cb_eq_zero)]);

    let disj = d.const_app(p.mul_eq_zero, &[c, sub_ab, c_sub_ab_eq_zero]);
    // disj : Or (Eq c zero) (Eq sub_ab zero)

    let c_zero_ty = d.ieq(c, zero_i);
    let sub_zero_ty = d.ieq(sub_ab, zero_i);
    let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let false_pf = d.apply(hc_ne, &[h]);
        d.absurd(sub_zero_ty, false_pf)
    };
    let on_right = &|_d: &mut IntDev<'_>, h: ExprId| -> ExprId { h };
    let sub_ab_eq_zero = d.or_elim(c_zero_ty, sub_zero_ty, sub_zero_ty, disj, on_left, on_right);

    ieq_of_sub_eq_zero(d, a, b, sub_ab_eq_zero)
}

/// From `x`, `cc`, `dvd_cc_x : idvd(cc, x)` and `pos_cc : Nat.lt zero (gcd
/// _ _)` reused directly as `Int.lt zero cc` (defeq, `cc` always being
/// `ofNat` of that gcd at every call site here -- the same reuse
/// `gcd.rs`'s own `declare_gcd_div_gcd_div_gcd` makes), derive
/// `Eq Int x (cc * x.ediv cc)`. Mirrors `gcd.rs`'s private `exact` closure
/// inside that same declaration.
fn iexact(d: &mut IntDev<'_>, cc: ExprId, x: ExprId, dvd_cc_x: ExprId, pos_cc: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let ediv_xc = d.iediv(x, cc);
    let emod_xc = d.iemod(x, cc);
    let zero_eq_ty = d.ieq(emod_xc, zero_i);
    let dvd_ty = super::dvd::idvd(d, cc, x);
    let iff_xc = d.const_app(p.emod_eq_zero_iff_dvd, &[x, cc, pos_cc]);
    let mpr = d.const_app(p.logic.iff_mpr, &[zero_eq_ty, dvd_ty, iff_xc]);
    let emod_eq_zero = d.apply(mpr, &[dvd_cc_x]);

    let mul_q = d.imul(cc, ediv_xc);
    let sum_with_emod = d.iadd(mul_q, emod_xc);
    let full_eq = d.const_app(p.ediv_add_emod, &[x, cc]); // Eq(sum_with_emod, x)
    let full_eq_rev = d.isymm(sum_with_emod, x, full_eq); // Eq(x, sum_with_emod)
    let sum_with_zero = d.iadd(mul_q, zero_i);
    let step = d.icongr(emod_xc, zero_i, emod_eq_zero, &|d, y| d.iadd(mul_q, y));
    let add_zero_q = d.const_app(p.add_zero, &[mul_q]); // Eq(sum_with_zero, mul_q)
    let (_, chained) = d.ichain(sum_with_emod, &[(sum_with_zero, step), (mul_q, add_zero_q)]);
    d.itrans(x, sum_with_emod, mul_q, full_eq_rev, chained) // Eq(x, cc*(x/cc))
}

/// `idvd (mul scale modulus) (mul scale x)`, `Not (Eq Int scale zero)` ->
/// `idvd modulus x`. Unpacks the single-level existential witness `k` from
/// `mul scale x = (mul scale modulus)*k`, reassociates to
/// `scale*x = scale*(modulus*k)`, cancels `scale` via
/// [`imul_left_cancel_of_ne`], and re-packs `k` as the witness for
/// `idvd modulus x`.
fn idvd_cancel_scale(
    d: &mut IntDev<'_>,
    scale: ExprId,
    modulus: ExprId,
    x: ExprId,
    scale_ne: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let int_ty = d.int_ty();
    let one = d.level_one();
    let scaled_modulus = d.imul(scale, modulus);
    let scaled_x = d.imul(scale, x);
    let pred = super::dvd::dvd_predicate(d, scaled_modulus, scaled_x);
    let target = super::dvd::idvd(d, modulus, x);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let mod_k = d.imul(modulus, k);
        let scaled_modulus_k = d.imul(scaled_modulus, k);
        let eq_ty = d.ieq(scaled_x, scaled_modulus_k);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);

        let scale_modk = d.imul(scale, mod_k);
        let assoc = d.const_app(p.mul_assoc, &[scale, modulus, k]); // Eq scaled_modulus_k scale_modk
        let (_, eq2) = d.ichain(
            scaled_x,
            &[(scaled_modulus_k, eq_proof), (scale_modk, assoc)],
        );
        // eq2 : Eq scaled_x scale_modk

        let cancelled = imul_left_cancel_of_ne(d, scale, x, mod_k, scale_ne, eq2); // Eq x mod_k

        let target_pred = super::dvd::dvd_predicate(d, modulus, x);
        let exists_intro_name = d.int().logic.exists_intro;
        let intro = d.kernel().const_(exists_intro_name, vec![one]);
        let witness_proof = d.apply(intro, &[int_ty, target_pred, k, cancelled]);

        let with_eq = d.lam_fv(eq_fv, eq_ty, witness_proof);
        d.lam_fv(k_fv, int_ty, with_eq)
    };
    int_exists_elim(d, pred, target, h, minor)
}

/// Declares `Int.ModEq.cancel_left_div_gcd` and `Int.ModEq.cancel_right_div_gcd`
/// -- see the module doc.
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not
/// type-check.
pub(super) fn declare_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let cancel_left_name = d.int().mod_eq_cancel_left_div_gcd;
    let cancel_right_name = d.int().mod_eq_cancel_right_div_gcd;

    // Int.ModEq.cancel_left_div_gcd :
    //   0 < m -> c*a ≡ c*b [ZMOD m] -> a ≡ b [ZMOD m / ofNat(gcd m c)]
    d.int_theorem(cancel_left_name, 4, &|d, v| {
        let (m, a, b, c) = (v[0], v[1], v[2], v[3]);
        let p = d.int();
        let zero_i = d.izero();
        let hm_ty = d.ilt(zero_i, m);
        let ca = d.imul(c, a);
        let cb = d.imul(c, b);
        let h_ty = super::modeq::imodeq(d, m, ca, cb);
        let g_nat = igcd(d, m, c);
        let g = d.of_nat(g_nat);
        let qm = d.iediv(m, g);
        let concl = super::modeq::imodeq(d, qm, a, b);
        let inner = d.arrow(h_ty, concl);
        let stmt = d.arrow(hm_ty, inner);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // g > 0 (as a Nat), via natAbs m > 0.
        let pos_natabs_m = pos_nat_abs_of_pos(d, m, hm); // Nat.lt zero (natAbs m)
        let nat_abs_m = nat_abs(d, m);
        let nat_abs_c = nat_abs(d, c);
        let nat_gcd_dvd_m = d.lemma(p.nat.gcd_dvd_left, &[nat_abs_m, nat_abs_c]);
        // Nat.dvd (Nat.gcd nat_abs_m nat_abs_c) nat_abs_m, defeq Nat.dvd g_nat nat_abs_m
        let pos_g_nat = d.lemma(
            p.nat.one_le_of_dvd_pos,
            &[g_nat, nat_abs_m, pos_natabs_m, nat_gcd_dvd_m],
        ); // Nat.lt zero g_nat (defeq, via Le one)

        // Exact division: m = g*qm, c = g*qc.
        let dvd_g_m = d.const_app(p.gcd_dvd_left, &[m, c]); // idvd(g, m)
        let dvd_g_c = d.const_app(p.gcd_dvd_right, &[m, c]); // idvd(g, c)
        let qc = d.iediv(c, g);
        let m_eq = iexact(d, g, m, dvd_g_m, pos_g_nat); // Eq m (g*qm)
        let c_eq = iexact(d, g, c, dvd_g_c, pos_g_nat); // Eq c (g*qc)

        // Coprimality of qm, qc.
        let coprime_qm_qc = d.const_app(p.gcd_div_gcd_div_gcd, &[m, c, pos_g_nat]);
        // Eq Nat (gcd qm qc) 1, defeq Coprime qm qc

        // h : modEq m (c*a) (c*b) -> dvd m (cb - ca)
        let dvd_m_diff = super::modeq::modeq_to_dvd(d, m, ca, cb, h);

        // Rewrite cb - ca to c*(b-a).
        let ba = d.isub(b, a);
        let c_ba = d.imul(c, ba);
        let cb_ca = d.isub(cb, ca);
        let msub = d.const_app(p.mul_sub, &[c, b, a]); // Eq c_ba cb_ca
        let msub_rev = d.isymm(c_ba, cb_ca, msub); // Eq cb_ca c_ba
        let motive1 = d.ieq_motive(cb_ca, &|d, x| super::dvd::idvd(d, m, x));
        let dvd_m_c_ba = d.itransport(cb_ca, motive1, dvd_m_diff, c_ba, msub_rev);
        // dvd_m_c_ba : idvd(m, c*(b-a))

        // Rewrite the divisor m -> g*qm.
        let g_qm = d.imul(g, qm);
        let motive2 = d.ieq_motive(m, &|d, x| super::dvd::idvd(d, x, c_ba));
        let dvd_gqm_cba = d.itransport(m, motive2, dvd_m_c_ba, g_qm, m_eq);
        // dvd_gqm_cba : idvd(g*qm, c*(b-a))

        // Rewrite c*(b-a) -> g*(qc*(b-a)).
        let g_qc = d.imul(g, qc);
        let qc_ba = d.imul(qc, ba);
        let g_qc_ba = d.imul(g, qc_ba);
        let gqc_ba = d.imul(g_qc, ba);
        let step1 = d.icongr(c, g_qc, c_eq, &|d, x| d.imul(x, ba)); // Eq c_ba gqc_ba
        let assoc = d.const_app(p.mul_assoc, &[g, qc, ba]); // Eq gqc_ba g_qc_ba
        let (_, eq_c_ba_full) = d.ichain(c_ba, &[(gqc_ba, step1), (g_qc_ba, assoc)]);
        let motive3 = d.ieq_motive(c_ba, &|d, x| super::dvd::idvd(d, g_qm, x));
        let dvd_final = d.itransport(c_ba, motive3, dvd_gqm_cba, g_qc_ba, eq_c_ba_full);
        // dvd_final : idvd(g*qm, g*(qc*(b-a)))

        // Cancel g.
        let g_ne_zero = int_ne_zero_of_nat_pos(d, g_nat, pos_g_nat); // Not(Eq Int g zero)
        let dvd_qm_qcba = idvd_cancel_scale(d, g, qm, qc_ba, g_ne_zero, dvd_final);
        // dvd_qm_qcba : idvd(qm, qc*(b-a))

        // Gauss: coprime qm qc, dvd qm (qc*(b-a)) -> dvd qm (b-a).
        let dvd_qm_ba = d.const_app(p.gauss_lemma, &[qm, qc, ba, coprime_qm_qc, dvd_qm_qcba]);

        let result = super::modeq::dvd_to_modeq(d, qm, a, b, dvd_qm_ba);

        let with_h = d.lam_fv(h_fv, h_ty, result);
        let proof = d.lam_fv(hm_fv, hm_ty, with_h);
        (stmt, proof)
    })?;

    // Int.ModEq.cancel_right_div_gcd :
    //   0 < m -> a*c ≡ b*c [ZMOD m] -> a ≡ b [ZMOD m / ofNat(gcd m c)]
    d.int_theorem(cancel_right_name, 4, &|d, v| {
        let (m, a, b, c) = (v[0], v[1], v[2], v[3]);
        let p = d.int();
        let zero_i = d.izero();
        let hm_ty = d.ilt(zero_i, m);
        let ac = d.imul(a, c);
        let bc = d.imul(b, c);
        let h_ty = super::modeq::imodeq(d, m, ac, bc);
        let g_nat = igcd(d, m, c);
        let g = d.of_nat(g_nat);
        let qm = d.iediv(m, g);
        let concl = super::modeq::imodeq(d, qm, a, b);
        let inner = d.arrow(h_ty, concl);
        let stmt = d.arrow(hm_ty, inner);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let ca = d.imul(c, a);
        let cb = d.imul(c, b);
        let comm_a = d.const_app(p.mul_comm, &[a, c]); // Eq ac ca
        let comm_b = d.const_app(p.mul_comm, &[b, c]); // Eq bc cb
        let motive_a = d.ieq_motive(ac, &|d, x| super::modeq::imodeq(d, m, x, bc));
        let step1 = d.itransport(ac, motive_a, h, ca, comm_a);
        let motive_b = d.ieq_motive(bc, &|d, x| super::modeq::imodeq(d, m, ca, x));
        let h2 = d.itransport(bc, motive_b, step1, cb, comm_b);
        // h2 : modEq m (c*a) (c*b)

        let result = d.const_app(p.mod_eq_cancel_left_div_gcd, &[m, a, b, c, hm, h2]);

        let with_h = d.lam_fv(h_fv, h_ty, result);
        let proof = d.lam_fv(hm_fv, hm_ty, with_h);
        (stmt, proof)
    })?;

    Ok(())
}
