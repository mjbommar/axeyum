//! Modular cancellation by dividing the modulus by `gcd(m,c)` -- three
//! `ml430` mirrors that generalize `euler.rs`'s coprime-only
//! `Nat.mod_eq_cancel` to an arbitrary common factor `c`:
//!
//! - `Nat.ModEq.cancel_left_div_gcd`
//!   (`F:ml430-nat-modeq-cancel-left-div-gcd-57ef8287`):
//!   `0 < m -> c*a ≡ c*b [MOD m] -> a ≡ b [MOD m / gcd m c]`.
//! - `Nat.ModEq.cancel_right_div_gcd`
//!   (`F:ml430-nat-modeq-cancel-right-div-gcd-22a4f40d`):
//!   `0 < m -> a*c ≡ b*c [MOD m] -> a ≡ b [MOD m / gcd m c]`.
//! - `Nat.ModEq.cancel_left_div_gcd'`
//!   (`F:ml430-nat-modeq-cancel-left-div-gcd-cfca1225`, Rust name
//!   `mod_eq_cancel_left_div_gcd_general` -- identifiers cannot carry `'`):
//!   `0 < m -> c ≡ d [MOD m] -> c*a ≡ d*b [MOD m] -> a ≡ b [MOD m / gcd m c]`.
//!
//! Two prior lanes (`docs/plan/status/329-nat-modeq-mirrors.md`,
//! `docs/plan/status/335-int-dvd-mirrors.md`) sized this family as needing a
//! new "divide-by-gcd factorization" slice (rewriting `m = g*(m/g)`,
//! coprimality of the quotients). By the time this lane started,
//! `Nat.gcd_mul_right` (`gcd_mul_right.rs`) had already landed for a sibling
//! family, but it turns out NOT to be what this family needs -- what closes
//! it is `Nat.gcd_cofactors_coprime` (`bezout.rs`), which predates both
//! prior lanes and neither one searched for. This file adds NO new
//! low-level arithmetic, only composes:
//!
//! - `Nat.div_gcd_pos_of_pos_left`-style positivity is not even needed: `g`'s
//!   positivity comes from `Nat.one_le_of_dvd_pos` fed the hypothesis `0 < m`
//!   directly (defeq to `1 ≤ m`, the same pattern `min_fac.rs` uses).
//! - `Nat.div_mul_cancel_of_dvd` (`divisibility.rs`): `g*(m/g) = m` and
//!   `g*(c/g) = c` for `g := gcd m c`.
//! - `Nat.gcd_cofactors_coprime` (`bezout.rs`): substituting those two
//!   equations into `gcd c m = gcd m c` (`gcd_comm`) `= g` gives
//!   `gcd (g*(c/g)) (g*(m/g)) = g` directly (no `gcd_mul_right` needed), so
//!   `gcd (c/g) (m/g) = 1`.
//! - A small local helper, [`mod_eq_cancel_scale`], that cancels a common
//!   POSITIVE scale factor from a `modEq` and its modulus simultaneously
//!   (`modEq (g*n) (g*x) (g*y) -> modEq n x y`), built the same way
//!   `euler.rs`'s `cancel_common_right_addend` peels `ModEq`'s nested
//!   existential: the SAME witnesses survive, because
//!   `g*(x + n*u) = g*x + (g*n)*u` is pure `left_distrib`/`mul_assoc`, and
//!   `Nat.mul_left_cancel_of_pos` peels the shared `g` off the resulting
//!   equation directly.
//!
//! Once the modulus and both endpoints share the SAME factored form
//! `modEq (g*(m/g)) (g*((c/g)*a)) (g*((c/g)*b))`, [`mod_eq_cancel_scale`]
//! strips `g`, and the pre-existing coprime `Nat.mod_eq_cancel` (`euler.rs`)
//! finishes.
//!
//! `cancel_left_div_gcd'` (the third fact) is NOT re-derived from scratch: it
//! reduces to the first fact via `Nat.mod_eq_mul_right`/`Nat.mod_eq_trans`,
//! exactly Mathlib's own proof (`(h.trans (hcd.symm.mul_right b))
//! .cancel_left_div_gcd hm`); `cancel_right_div_gcd` reduces to the first
//! fact by commuting both sides (`Nat.mul_comm`), also matching Mathlib.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Eq l r`, `Eq l l2`, `Eq r r2` -> `Eq l2 r2` -- rewrite both sides of a
/// plain equation. Local copy of the pattern `euler.rs`'s `rewrite_mod_eq`
/// uses for a `modEq` target, specialized here to a plain `Eq` target.
#[allow(clippy::too_many_arguments)]
fn rewrite_eq(
    d: &mut NatDev<'_>,
    l: ExprId,
    r: ExprId,
    l2: ExprId,
    r2: ExprId,
    eq_l: ExprId,
    eq_r: ExprId,
    h: ExprId,
) -> ExprId {
    let motive_l = d.eq_motive(l, &|d, x| d.eq(x, r));
    let step1 = d.transport(l, motive_l, h, l2, eq_l);
    let motive_r = d.eq_motive(r, &|d, x| d.eq(l2, x));
    d.transport(r, motive_r, step1, r2, eq_r)
}

/// `modEq d a b`, plus rewriting equalities for the modulus `d` and the two
/// endpoints `a`, `b` into `d2`, `a2`, `b2` -> `modEq d2 a2 b2`. Generalizes
/// `euler.rs`'s `rewrite_mod_eq` (which only rewrites the two endpoints) by
/// also transporting the modulus.
#[allow(clippy::too_many_arguments)]
fn rewrite_mod_eq3(
    d: &mut NatDev<'_>,
    modulus: ExprId,
    a: ExprId,
    b: ExprId,
    modulus2: ExprId,
    a2: ExprId,
    b2: ExprId,
    eq_mod: ExprId,
    eq_a: ExprId,
    eq_b: ExprId,
    h: ExprId,
) -> ExprId {
    let motive_mod = d.eq_motive(modulus, &|d, x| d.mod_eq(x, a, b));
    let step1 = d.transport(modulus, motive_mod, h, modulus2, eq_mod);
    let motive_a = d.eq_motive(a, &|d, x| d.mod_eq(modulus2, x, b));
    let step2 = d.transport(a, motive_a, step1, a2, eq_a);
    let motive_b = d.eq_motive(b, &|d, x| d.mod_eq(modulus2, a2, x));
    d.transport(b, motive_b, step2, b2, eq_b)
}

/// `modEq (mul scale modulus) (mul scale x) (mul scale y)`, `Le one scale`
/// -> `modEq modulus x y`. Peels the two-level existential the same way
/// `euler.rs`'s `cancel_common_right_addend` does, and finishes by pulling
/// `scale` back out of each side (`left_distrib`/`mul_assoc`) and cancelling
/// it (`Nat.mul_left_cancel_of_pos`) -- the SAME witnesses `u,v` survive.
#[allow(clippy::too_many_arguments)]
fn mod_eq_cancel_scale(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    scale: ExprId,
    modulus: ExprId,
    x: ExprId,
    y: ExprId,
    pos_scale: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let scaled_modulus = d.mul(scale, modulus);
    let scaled_x = d.mul(scale, x);
    let scaled_y = d.mul(scale, y);
    let source = d.mod_eq(scaled_modulus, scaled_x, scaled_y);
    let target = d.mod_eq(modulus, x, y);
    let outer_predicate = d.mod_eq_outer_predicate(scaled_modulus, scaled_x, scaled_y);
    let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
    let outer_minor = {
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let inner_source = d.mod_eq_inner_exists(scaled_modulus, scaled_x, scaled_y, u);
        let inner_source_fv = d.fresh_fvar();
        let inner_source_proof = d.kernel().fvar(inner_source_fv);
        let inner_predicate = d.mod_eq_inner_predicate(scaled_modulus, scaled_x, scaled_y, u);
        let inner_motive = d
            .kernel()
            .lam(anon, inner_source, target, BinderInfo::Default);
        let inner_minor = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let du = d.mul(scaled_modulus, u);
            let dv = d.mul(scaled_modulus, v);
            let lhs0 = d.add(scaled_x, du);
            let rhs0 = d.add(scaled_y, dv);
            let eq_ty = d.eq(lhs0, rhs0);
            let eq_fv = d.fresh_fvar();
            let eq_proof = d.kernel().fvar(eq_fv);

            let mod_u = d.mul(modulus, u);
            let mod_v = d.mul(modulus, v);
            let scale_mod_u = d.mul(scale, mod_u);
            let scale_mod_v = d.mul(scale, mod_v);
            let x_plus = d.add(x, mod_u);
            let y_plus = d.add(y, mod_v);
            let scale_x_plus = d.mul(scale, x_plus);
            let scale_y_plus = d.mul(scale, y_plus);

            // lhs0 = scale*x + (scale*modulus)*u
            //      = scale*x + scale*(modulus*u)     [mul_assoc, reversed]
            //      = scale*(x + modulus*u)            [left_distrib, reversed]
            //      = scale_x_plus
            // `mul_assoc(scale, modulus, u) : Eq (mul (mul scale modulus) u)
            // (mul scale (mul modulus u))`, i.e. `Eq du scale_mod_u` directly
            // -- NOT `Eq scale_mod_u du` (a prior version of this file got
            // this backwards and it type-checked as a swapped-equality
            // `TypeMismatch`, found via `Kernel::render_lean` on both sides).
            let du_eq_scale_mod_u = d.lemma(p.mul_assoc, &[scale, modulus, u]); // Eq du scale_mod_u
            let step_u = d.congr(du, scale_mod_u, du_eq_scale_mod_u, &|d, t| {
                d.add(scaled_x, t)
            });
            let lhs1 = d.add(scaled_x, scale_mod_u);
            let distrib_l = d.lemma(p.left_distrib, &[scale, x, mod_u]); // Eq scale_x_plus lhs1
            let distrib_l_rev = d.symm(scale_x_plus, lhs1, distrib_l);
            let (_, eq_l_full) = d.chain(lhs0, &[(lhs1, step_u), (scale_x_plus, distrib_l_rev)]);

            let dv_eq_scale_mod_v = d.lemma(p.mul_assoc, &[scale, modulus, v]); // Eq dv scale_mod_v
            let step_v = d.congr(dv, scale_mod_v, dv_eq_scale_mod_v, &|d, t| {
                d.add(scaled_y, t)
            });
            let rhs1 = d.add(scaled_y, scale_mod_v);
            let distrib_r = d.lemma(p.left_distrib, &[scale, y, mod_v]); // Eq scale_y_plus rhs1
            let distrib_r_rev = d.symm(scale_y_plus, rhs1, distrib_r);
            let (_, eq_r_full) = d.chain(rhs0, &[(rhs1, step_v), (scale_y_plus, distrib_r_rev)]);

            let final_eq = rewrite_eq(
                d,
                lhs0,
                rhs0,
                scale_x_plus,
                scale_y_plus,
                eq_l_full,
                eq_r_full,
                eq_proof,
            );
            // final_eq : Eq (scale*x_plus) (scale*y_plus)
            let cancelled = d.lemma(
                p.mul_left_cancel_of_pos,
                &[scale, x_plus, y_plus, pos_scale, final_eq],
            );
            // cancelled : Eq x_plus y_plus
            //           = Eq (mod_eq_sum modulus x u) (mod_eq_sum modulus y v)

            let target_inner_pred = d.mod_eq_inner_predicate(modulus, x, y, u);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let inner_exists_proof = d.apply(intro, &[nat, target_inner_pred, v, cancelled]);
            let target_outer_pred = d.mod_eq_outer_predicate(modulus, x, y);
            let full_proof = d.apply(intro, &[nat, target_outer_pred, u, inner_exists_proof]);

            let with_eq = d.lam_fv(eq_fv, eq_ty, full_proof);
            d.lam_fv(v_fv, nat, with_eq)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                inner_predicate,
                inner_motive,
                inner_minor,
                inner_source_proof,
            ],
        );
        let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
        d.lam_fv(u_fv, nat, with_inner)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, outer_predicate, outer_motive, outer_minor, h])
}

/// Declares `Nat.ModEq.cancel_left_div_gcd`, `Nat.ModEq.cancel_right_div_gcd`
/// and `Nat.ModEq.cancel_left_div_gcd'` -- see the module doc. Must run
/// after `declare_gcd_semantics` (`Nat.gcd_dvd_left`/`_right`, `gcd.rs`),
/// `declare_divisibility` (`Nat.div_mul_cancel_of_dvd`,
/// `Nat.one_le_of_dvd_pos`), `bezout.rs`'s `declare_gcd_bezout` family
/// (`Nat.gcd_cofactors_coprime`), `declare_multiplicative_theorems`
/// (`Nat.mul_assoc`/`Nat.mul_comm`/`Nat.left_distrib`/
/// `Nat.mul_left_cancel_of_pos`), and `euler.rs`'s `declare_mod_eq_cancel`
/// (`Nat.mod_eq_cancel`) and `modular.rs`'s congruence family
/// (`Nat.mod_eq_symm`/`Nat.mod_eq_trans`/`Nat.mod_eq_mul_right`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not
/// type-check.
pub(super) fn declare_modeq_cancel_div_gcd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // Nat.ModEq.cancel_left_div_gcd :
    //   0 < m -> c*a ≡ c*b [MOD m] -> a ≡ b [MOD m / gcd m c]
    d.theorem(p.mod_eq_cancel_left_div_gcd, 4, &|d, v| {
        let (m, a, b, c) = (v[0], v[1], v[2], v[3]);
        let zero = d.zero();
        let hm_ty = d.lt(zero, m);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let h_ty = d.mod_eq(m, ca, cb);
        let g = d.gcd(m, c);
        let m1 = d.div(m, g);
        let concl = d.mod_eq(m1, a, b);
        let inner_arrow = d.arrow(h_ty, concl);
        let stmt = d.arrow(hm_ty, inner_arrow);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let hmd = d.lemma(p.gcd_dvd_left, &[m, c]); // dvd g m
        let hcd = d.lemma(p.gcd_dvd_right, &[m, c]); // dvd g c
        let one_le_g = d.lemma(p.one_le_of_dvd_pos, &[g, m, hm, hmd]); // Le one g

        let c1 = d.div(c, g);
        let eq_m = d.lemma(p.div_mul_cancel_of_dvd, &[g, m, one_le_g, hmd]); // Eq (g*m1) m
        let eq_c = d.lemma(p.div_mul_cancel_of_dvd, &[g, c, one_le_g, hcd]); // Eq (g*c1) c

        let g_m1 = d.mul(g, m1);
        let g_c1 = d.mul(g, c1);

        // gcd (g*c1) (g*m1) = gcd c (g*m1) = gcd c m = gcd m c (gcd_comm) = g.
        let start = d.gcd(g_c1, g_m1);
        let gcd_c_gm1 = d.gcd(c, g_m1);
        let gcd_c_m = d.gcd(c, m);
        let step_a = d.congr(g_c1, c, eq_c, &|d, x| d.gcd(x, g_m1));
        let step_b = d.congr(g_m1, m, eq_m, &|d, x| d.gcd(c, x));
        let comm = d.lemma(p.gcd_comm, &[c, m]); // Eq (gcd c m) (gcd m c) = Eq gcd_c_m g
        let (_, cofactor_eq) = d.chain(start, &[(gcd_c_gm1, step_a), (gcd_c_m, step_b), (g, comm)]);
        // cofactor_eq : Eq (gcd g_c1 g_m1) g

        let coprime = d.lemma(p.gcd_cofactors_coprime, &[g, c1, m1, one_le_g, cofactor_eq]);
        // coprime : Eq (gcd c1 m1) 1

        let eq_mod = d.symm(g_m1, m, eq_m); // Eq m g_m1
        let c1a = d.mul(c1, a);
        let c1b = d.mul(c1, b);
        let g_c1a = d.mul(g, c1a);
        let g_c1b = d.mul(g, c1b);

        let eq_a = {
            let g_c1_a = d.mul(g_c1, a);
            let eq_c_rev = d.symm(g_c1, c, eq_c); // Eq c g_c1
            let step1 = d.congr(c, g_c1, eq_c_rev, &|d, x| d.mul(x, a)); // Eq ca g_c1_a
            let step2 = d.lemma(p.mul_assoc, &[g, c1, a]); // Eq g_c1_a g_c1a
            let (_, e) = d.chain(ca, &[(g_c1_a, step1), (g_c1a, step2)]);
            e
        };
        let eq_b = {
            let g_c1_b = d.mul(g_c1, b);
            let eq_c_rev = d.symm(g_c1, c, eq_c); // Eq c g_c1
            let step1 = d.congr(c, g_c1, eq_c_rev, &|d, x| d.mul(x, b)); // Eq cb g_c1_b
            let step2 = d.lemma(p.mul_assoc, &[g, c1, b]); // Eq g_c1_b g_c1b
            let (_, e) = d.chain(cb, &[(g_c1_b, step1), (g_c1b, step2)]);
            e
        };

        let h2 = rewrite_mod_eq3(d, m, ca, cb, g_m1, g_c1a, g_c1b, eq_mod, eq_a, eq_b, h);
        // h2 : modEq (g*m1) (g*(c1*a)) (g*(c1*b))

        let h3 = mod_eq_cancel_scale(d, &p, g, m1, c1a, c1b, one_le_g, h2);
        // h3 : modEq m1 (c1*a) (c1*b)

        let result = d.lemma(p.mod_eq_cancel, &[m1, c1, a, b, coprime, h3]);
        // result : modEq m1 a b

        let with_h = d.lam_fv(h_fv, h_ty, result);
        let proof = d.lam_fv(hm_fv, hm_ty, with_h);
        (stmt, proof)
    })?;
    // Nat.ModEq.cancel_right_div_gcd :
    //   0 < m -> a*c ≡ b*c [MOD m] -> a ≡ b [MOD m / gcd m c]
    d.theorem(p.mod_eq_cancel_right_div_gcd, 4, &|d, v| {
        let (m, a, b, c) = (v[0], v[1], v[2], v[3]);
        let zero = d.zero();
        let hm_ty = d.lt(zero, m);
        let ac = d.mul(a, c);
        let bc = d.mul(b, c);
        let h_ty = d.mod_eq(m, ac, bc);
        let g = d.gcd(m, c);
        let m1 = d.div(m, g);
        let concl = d.mod_eq(m1, a, b);
        let inner_arrow = d.arrow(h_ty, concl);
        let stmt = d.arrow(hm_ty, inner_arrow);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let comm_a = d.lemma(p.mul_comm, &[a, c]); // Eq ac ca
        let comm_b = d.lemma(p.mul_comm, &[b, c]); // Eq bc cb
        let h2 = {
            let motive_a = d.eq_motive(ac, &|d, x| d.mod_eq(m, x, bc));
            let step1 = d.transport(ac, motive_a, h, ca, comm_a);
            let motive_b = d.eq_motive(bc, &|d, x| d.mod_eq(m, ca, x));
            d.transport(bc, motive_b, step1, cb, comm_b)
        };
        // h2 : modEq m (c*a) (c*b)
        let result = d.lemma(p.mod_eq_cancel_left_div_gcd, &[m, a, b, c, hm, h2]);
        // result : modEq (div m (gcd m c)) a b

        let with_h = d.lam_fv(h_fv, h_ty, result);
        let proof = d.lam_fv(hm_fv, hm_ty, with_h);
        (stmt, proof)
    })?;

    // Nat.ModEq.cancel_left_div_gcd' :
    //   0 < m -> c ≡ d [MOD m] -> c*a ≡ d*b [MOD m] -> a ≡ b [MOD m / gcd m c]
    // Bound variable named `d2` here (Mathlib's `d`), since `d` is this
    // closure's `NatDev` handle.
    d.theorem(p.mod_eq_cancel_left_div_gcd_general, 5, &|d, v| {
        let (m, a, b, c, d2) = (v[0], v[1], v[2], v[3], v[4]);
        let zero = d.zero();
        let hm_ty = d.lt(zero, m);
        let hcd_ty = d.mod_eq(m, c, d2);
        let ca = d.mul(c, a);
        let d2b = d.mul(d2, b);
        let h_ty = d.mod_eq(m, ca, d2b);
        let g = d.gcd(m, c);
        let m1 = d.div(m, g);
        let concl = d.mod_eq(m1, a, b);
        let arrow1 = d.arrow(h_ty, concl);
        let arrow2 = d.arrow(hcd_ty, arrow1);
        let stmt = d.arrow(hm_ty, arrow2);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let hcd_fv = d.fresh_fvar();
        let hcd = d.kernel().fvar(hcd_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let hcd_symm = d.lemma(p.mod_eq_symm, &[m, c, d2, hcd]); // modEq m d2 c
        let cb = d.mul(c, b);
        let scaled = d.lemma(p.mod_eq_mul_right, &[m, d2, c, b, hcd_symm]); // modEq m d2b cb
        let t = d.lemma(p.mod_eq_trans, &[m, ca, d2b, cb, h, scaled]); // modEq m ca cb
        let result = d.lemma(p.mod_eq_cancel_left_div_gcd, &[m, a, b, c, hm, t]);
        // result : modEq m1 a b

        let with_h = d.lam_fv(h_fv, h_ty, result);
        let with_hcd = d.lam_fv(hcd_fv, hcd_ty, with_h);
        let proof = d.lam_fv(hm_fv, hm_ty, with_hcd);
        (stmt, proof)
    })?;

    Ok(())
}
