//! `Int.gcd_dvd_iff : ∀ a b n, Iff (Nat.dvd (Int.gcd a b) n) (Exists (fun x =>
//! Exists (fun y => Eq Int (ofNat n) (add (mul a x) (mul b y)))))` -- an
//! `ml430` mirror (`F:ml430-int-gcd-dvd-iff-66fa03b3`).
//!
//! Both directions route through the already-checked Bézout identity at the
//! *named computable witnesses* `Int.gcdA`/`Int.gcdB`
//! (`bezout_witnesses::declare_gcd_eq_gcd_ab_witnesses`,
//! `p.gcd_eq_gcd_ab_witnesses : Eq Int (ofNat (gcd a b)) (a*gcdA a b + b*gcdB
//! a b)`), so neither direction needs to eliminate an existential to *reach*
//! the Bézout coefficients -- only the fact's own quantifiers need
//! elimination/introduction.
//!
//! - **mpr** (`∃x y, … → dvd`): destructure the two-level witness (two
//!   `Exists.rec` applications, mirroring `dvd.rs::declare_dvd_trans`'s
//!   single-level shape via [`int_exists_elim`]), then `dvd_trans`+
//!   `dvd_mul_right` lift `ofNat (gcd a b) ∣ a`/`∣ b`
//!   (`gcd_dvd_left`/`gcd_dvd_right`) to `∣ a*x`/`∣ b*y`, `dvd_add` combines
//!   them into `∣ (a*x+b*y)`, transport along the hypothesis equation lands
//!   on `∣ ofNat n`, and `nat_abs_dvd_nat_abs_of_dvd` drops to the stated
//!   `Nat.dvd` (`natAbs (ofNat _) ≡ _` by `rfl`, so no cast bridge is needed
//!   for either side).
//! - **mp** (`dvd → ∃x y, …`): `Nat.dvd`'s own witness `q` (`n = gcd*q`,
//!   eliminated via `int_prelude::ops::exists_elim`, the `Nat`-quantified
//!   helper) scales BOTH Bézout coefficients: `x := gcdA a b * ofNat q`, `y
//!   := gcdB a b * ofNat q`. The equation chain is `ofNat n = ofNat (gcd*q) =
//!   ofNat gcd * ofNat q` (the last step pure `δ/ι` -- `Int.mul` on two
//!   `ofNat` operands reduces directly to `ofNat` of the `Nat` product, the
//!   same fact `sign.rs::declare_mul_assoc`'s `(OfNat,OfNat,OfNat)` branch
//!   relies on) `= (a*gcdA+b*gcdB) * ofNat q` (congr on
//!   `gcd_eq_gcd_ab_witnesses`) `= a*gcdA*ofNat q + b*gcdB*ofNat q`
//!   (`add_mul`) `= a*x + b*y` (`mul_assoc` twice).

use super::dvd::idvd;
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Exists Int predicate`.
fn mk_exists(d: &mut IntDev<'_>, predicate: ExprId) -> ExprId {
    let one = d.level_one();
    let exists_name = d.int().logic.exists_;
    let exists = d.kernel().const_(exists_name, vec![one]);
    let int_ty = d.int_ty();
    d.apply(exists, &[int_ty, predicate])
}

/// Eliminate `witness : Exists Int predicate` into `target`, given a
/// `minor : Pi (x : Int), predicate x -> target`. Local copy of
/// `int_prelude::ops::exists_elim`'s shape, over `Int` instead of `Nat`
/// (that helper hardcodes the `Nat`-quantified case, and this file needs
/// both).
fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let exists_ty = mk_exists(d, predicate);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// Build `Exists.intro Int predicate witness proof`.
fn int_exists_intro(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[int_ty, predicate, witness, proof])
}

/// `fun (y : Int) => Eq Int lhs (add (mul a x) (mul b y))`.
fn inner_pred(d: &mut IntDev<'_>, lhs: ExprId, a: ExprId, x: ExprId, b: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let ax = d.imul(a, x);
    let by = d.imul(b, y);
    let sum = d.iadd(ax, by);
    let body = d.ieq(lhs, sum);
    d.lam_fv(y_fv, int_ty, body)
}

/// `fun (x : Int) => Exists (fun y => Eq Int lhs (add (mul a x) (mul b y)))`.
fn outer_pred(d: &mut IntDev<'_>, lhs: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = {
        let ip = inner_pred(d, lhs, a, x, b);
        mk_exists(d, ip)
    };
    d.lam_fv(x_fv, int_ty, body)
}

/// Given `proof : idvd(of_g, b1)` and `eq_b1_b2 : Eq Int b1 b2`, build
/// `idvd(of_g, b2)`.
fn dvd_transport_rhs(
    d: &mut IntDev<'_>,
    of_g: ExprId,
    b1: ExprId,
    b2: ExprId,
    eq_b1_b2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.ieq_motive(b1, &|d, x| idvd(d, of_g, x));
    d.itransport(b1, motive, proof, b2, eq_b1_b2)
}

/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gcd_dvd_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_dvd_iff, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let nat = d.nat_ty();
        let int_ty = d.int_ty();

        let g = d.const_app(p.gcd, &[a, b]);
        let of_g = d.of_nat(g);
        let of_n = d.of_nat(n);

        let dvd_ty = NatOps::dvd(d, g, n);
        let op = outer_pred(d, of_n, a, b);
        let exists_ty_applied = mk_exists(d, op);

        // --- mp : dvd -> exists --------------------------------------------
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let dvd_pred = NatOps::dvd_predicate(d, g, n);
            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let gq = NatOps::mul(d, g, q);
                let eq_ty = d.eq(n, gq);
                let eq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(eq_fv);

                let of_q = d.of_nat(q);
                let u = d.const_app(p.gcd_a, &[a, b]);
                let vv = d.const_app(p.gcd_b, &[a, b]);
                let x = d.imul(u, of_q);
                let y = d.imul(vv, of_q);

                let bezout = d.const_app(p.gcd_eq_gcd_ab_witnesses, &[a, b]); // Eq(of_g, a*u+b*vv)
                let au = d.imul(a, u);
                let bv = d.imul(b, vv);
                let au_bv = d.iadd(au, bv);

                // ofNat n = ofNat (g*q)  [heq : Eq Nat n gq lifted to Eq Int]
                let step1 = d.nat_eq_to_int(n, gq, heq, &|d, z| d.of_nat(z));
                // ofNat(g*q) is defeq to imul(of_g, of_q); use that as the
                // chain's next term.
                let of_g_of_q = d.imul(of_g, of_q);

                // imul(of_g,of_q) = imul(a*u+b*vv, of_q)  [congr bezout]
                let step2 = d.icongr(of_g, au_bv, bezout, &|d, z| d.imul(z, of_q));
                let next2 = d.imul(au_bv, of_q);

                // (a*u+b*vv)*of_q = (a*u)*of_q + (b*vv)*of_q  [add_mul]
                let step3 = d.const_app(p.add_mul, &[au, bv, of_q]);
                let au_q = d.imul(au, of_q);
                let bv_q = d.imul(bv, of_q);
                let next3 = d.iadd(au_q, bv_q);

                // (a*u)*of_q = a*x  [mul_assoc]
                let assoc_a = d.const_app(p.mul_assoc, &[a, u, of_q]); // Eq(au_q, a*x)
                let ax = d.imul(a, x);
                let step4 = d.icongr(au_q, ax, assoc_a, &|d, z| d.iadd(z, bv_q));
                let next4 = d.iadd(ax, bv_q);

                // (b*vv)*of_q = b*y  [mul_assoc]
                let assoc_b = d.const_app(p.mul_assoc, &[b, vv, of_q]); // Eq(bv_q, b*y)
                let by = d.imul(b, y);
                let step5 = d.icongr(bv_q, by, assoc_b, &|d, z| d.iadd(ax, z));
                let next5 = d.iadd(ax, by);

                let (_, whole) = d.ichain(
                    of_n,
                    &[
                        (of_g_of_q, step1),
                        (next2, step2),
                        (next3, step3),
                        (next4, step4),
                        (next5, step5),
                    ],
                );

                let ip = inner_pred(d, of_n, a, x, b);
                let inner_ex = int_exists_intro(d, ip, y, whole);
                let outer_ex = int_exists_intro(d, op, x, inner_ex);

                let with_heq = d.lam_fv(eq_fv, eq_ty, outer_ex);
                d.lam_fv(q_fv, nat, with_heq)
            };
            let body = super::ops::exists_elim(d, dvd_pred, exists_ty_applied, h, minor);
            d.lam_fv(h_fv, dvd_ty, body)
        };

        // --- mpr : exists -> dvd --------------------------------------------
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let minor_outer = {
                let x_fv = d.fresh_fvar();
                let x = d.kernel().fvar(x_fv);
                let ip = inner_pred(d, of_n, a, x, b);

                let minor_inner = {
                    let y_fv = d.fresh_fvar();
                    let y = d.kernel().fvar(y_fv);
                    let ax = d.imul(a, x);
                    let by = d.imul(b, y);
                    let sum = d.iadd(ax, by);
                    let eq_ty = d.ieq(of_n, sum);
                    let eq_fv = d.fresh_fvar();
                    let heq = d.kernel().fvar(eq_fv);

                    let dvd_g_a = d.const_app(p.gcd_dvd_left, &[a, b]); // idvd(of_g,a)
                    let dvd_a_ax = d.const_app(p.dvd_mul_right, &[a, x]); // idvd(a,ax)
                    let dvd_g_ax = d.const_app(p.dvd_trans, &[of_g, a, ax, dvd_g_a, dvd_a_ax]);

                    let dvd_g_b = d.const_app(p.gcd_dvd_right, &[a, b]); // idvd(of_g,b)
                    let dvd_b_by = d.const_app(p.dvd_mul_right, &[b, y]); // idvd(b,by)
                    let dvd_g_by = d.const_app(p.dvd_trans, &[of_g, b, by, dvd_g_b, dvd_b_by]);

                    let dvd_g_sum = d.const_app(p.dvd_add, &[of_g, ax, by, dvd_g_ax, dvd_g_by]); // idvd(of_g,sum)

                    let heq_rev = d.isymm(of_n, sum, heq); // Eq(sum, of_n)
                    let dvd_g_of_n = dvd_transport_rhs(d, of_g, sum, of_n, heq_rev, dvd_g_sum);

                    let nat_dvd =
                        d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_g, of_n, dvd_g_of_n]);
                    let with_heq = d.lam_fv(eq_fv, eq_ty, nat_dvd);
                    d.lam_fv(y_fv, int_ty, with_heq)
                };
                let hx_fv = d.fresh_fvar();
                let hx = d.kernel().fvar(hx_fv);
                let hx_ty = mk_exists(d, ip);
                let elim = int_exists_elim(d, ip, dvd_ty, hx, minor_inner);
                let with_hx = d.lam_fv(hx_fv, hx_ty, elim);
                d.lam_fv(x_fv, int_ty, with_hx)
            };
            let body = int_exists_elim(d, op, dvd_ty, h, minor_outer);
            d.lam_fv(h_fv, exists_ty_applied, body)
        };

        let iff_stmt = d.const_app(p.logic.iff, &[dvd_ty, exists_ty_applied]);
        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_ty, exists_ty_applied, mp, mpr]);

        // `n` is not one of `int_theorem`'s two auto-quantified (Int) vars,
        // so it must be Pi/lam-wrapped here explicitly, inside the a/b
        // quantifiers `int_theorem` adds itself.
        let stmt = d.pi_fv(n_fv, nat, iff_stmt);
        let proof = d.lam_fv(n_fv, nat, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}
