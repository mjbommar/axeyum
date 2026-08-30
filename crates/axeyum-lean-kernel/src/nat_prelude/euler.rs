//! Multiplicative cancellation modulo `n` — the engine of Euler's totient
//! theorem, landed alone because the theorem itself is blocked (see below).
//!
//! [`declare_mod_eq_cancel`] is `Nat.mod_eq_cancel : gcd c n = 1 →
//! modEq n (c*a) (c*b) → modEq n a b`. The classical argument ("multiply by
//! `c`'s inverse mod `n`") has to be built without ever forming that inverse
//! as a single term, because [`super::bezout::declare_gcd_bezout`]'s
//! certificate is a **balanced** all-naturals identity
//! (`1 + c*mn + n*nn = c*mp + n*np`, avoiding signed subtraction entirely,
//! same convention [`super::bezout::declare_euclid_lemma`] uses) rather than
//! a signed Bézout pair. That identity is not itself a `modEq` witness for
//! `c*mp ≡ 1 [n]` — it carries an extra `c*mn` term on the `1` side that
//! doesn't vanish on its own.
//!
//! The proof used here never tries to isolate "the inverse". Instead:
//!
//! 1. The Bézout equation, read literally, already has the *shape* of a
//!    `modEq` witness: `(1 + c*mn) + n*nn = (c*mp) + n*np` is exactly
//!    `modEq n (1+c*mn) (c*mp)` with witnesses `(nn, np)`. No rewriting
//!    needed — [`bezout_elim`] hands us `mp,mn,np,nn` and the equation
//!    directly in that shape.
//! 2. Scale that `modEq` by `a` and by `b` (`Nat.mod_eq_mul_right`), and
//!    scale the hypothesis `modEq n (c*a) (c*b)` by `mp` and by `mn`
//!    (`Nat.mod_eq_mul_left`). Four applications, no existentials touched.
//! 3. Chain those four through `mod_eq_trans`/`mod_eq_symm` to reach
//!    `modEq n (a + c*mn*a) (b + c*mn*a)` — both sides now share the same
//!    extra addend `c*mn*a`, which is *why* step 2 scaled the hypothesis by
//!    `mn` as well as by `mp`: it is exactly what is needed to make the two
//!    "extra" terms line up and cancel later, rather than merely being
//!    congruent to each other.
//! 4. [`cancel_common_right_addend`] peels the shared addend off a `modEq`
//!    the same way ordinary `+k` cancels off an `Eq`: unpack the two-level
//!    existential, reassociate so the addend sits at the same place on both
//!    sides of the underlying witness equation, and finish with
//!    `Nat.add_right_cancel`. The same `u,v` witnesses survive the
//!    cancellation unchanged.
//!
//! ## What does not land here
//!
//! `Nat.euler_totient_theorem` itself does not land in this slice.
//! [`super::totient`]'s own module doc already says why, independently of
//! this file: the standard proof needs a product over the *subset* of
//! residues in `[0,n)` coprime to `n`, shown to be permuted by
//! multiplication by `a`. This kernel has `Nat.prodRange` over a
//! *contiguous* range (`factorization.rs`) and `Nat.countRange` over a
//! Boolean-predicate subset (`totient.rs`), but no product restricted to a
//! predicate-defined subset, and no lemma that multiplication-by-`a`
//! permutes such a subset as an index set. `restrict_pair.rs` restricts
//! `[0,n)` bijections to a fixed two-element complement, not to an arbitrary
//! predicate; `permutation.rs` builds inverses for bijections already known
//! on all of `[0,n)`. Building "product over a predicate-defined subset,
//! plus a permutation lemma for it" is a separate, larger slice — this is
//! the same missing primitive noted for uniqueness of prime factorization
//! and for permutations-as-group-elements, not a new gap.
//!
//! This lemma is exactly the piece that does not need that machinery
//! (per the task brief: "This should follow from `euclid_lemma`/Bézout
//! without any permutation machinery"), so it lands on its own.

use super::NatPrelude;
use super::bezout::bezout_elim;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Small algebraic helpers, in the same no-subtraction style as
// `bezout.rs`/`fermat.rs`: every step is `mul_assoc`/`mul_comm`/`add_assoc`/
// `add_comm`/`(left|right)_distrib`/`one_mul` plus `congr`/`chain`.
// ============================================================================

/// `k*(c*x) = (c*k)*x`, via `mul_assoc` then `mul_comm`.
fn scale_reorder(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId, c: ExprId, x: ExprId) -> ExprId {
    let p = *p;
    let cx = d.mul(c, x);
    let start = d.mul(k, cx);
    let kc = d.mul(k, c);
    let kc_x = d.mul(kc, x);
    let assoc = d.lemma(p.mul_assoc, &[k, c, x]);
    let step1 = d.symm(kc_x, start, assoc);
    let ck = d.mul(c, k);
    let ck_x = d.mul(ck, x);
    let commute = d.lemma(p.mul_comm, &[k, c]);
    let step2 = d.congr(kc, ck, commute, &|d, t| d.mul(t, x));
    let (_e, proof) = d.chain(start, &[(kc_x, step1), (ck_x, step2)]);
    proof
}

/// `(1+k)*x = x + k*x`, via `right_distrib` then `one_mul`.
fn distrib_one_plus(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId, x: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let one_plus_k = d.add(one, k);
    let start = d.mul(one_plus_k, x);
    let one_x = d.mul(one, x);
    let k_x = d.mul(k, x);
    let mid1 = d.add(one_x, k_x);
    let rd = d.lemma(p.right_distrib, &[one, k, x]);
    let one_mul_x = d.lemma(p.one_mul, &[x]);
    let target = d.add(x, k_x);
    let step2 = d.congr(one_x, x, one_mul_x, &|d, t| d.add(t, k_x));
    let (_e, proof) = d.chain(start, &[(mid1, rd), (target, step2)]);
    proof
}

/// `(a+k)+m = (a+m)+k`, via `add_assoc` twice and `add_comm` in the middle.
fn swap_tail(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, k: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    let ak = d.add(a, k);
    let start = d.add(ak, m);
    let km = d.add(k, m);
    let mid1 = d.add(a, km);
    let assoc1 = d.lemma(p.add_assoc, &[a, k, m]);
    let mk = d.add(m, k);
    let mid2 = d.add(a, mk);
    let commute = d.lemma(p.add_comm, &[k, m]);
    let step2 = d.congr(km, mk, commute, &|d, t| d.add(a, t));
    let am = d.add(a, m);
    let target = d.add(am, k);
    let assoc2 = d.lemma(p.add_assoc, &[a, m, k]);
    let step3 = d.symm(target, mid2, assoc2);
    let (_e, proof) = d.chain(start, &[(mid1, assoc1), (mid2, step2), (target, step3)]);
    proof
}

/// `modEq d a b`, `Eq a a2`, `Eq b b2` → `modEq d a2 b2`, by transporting
/// each endpoint of the congruence across the given equality.
#[allow(clippy::too_many_arguments)]
pub(super) fn rewrite_mod_eq(
    d: &mut NatDev<'_>,
    modulus: ExprId,
    a: ExprId,
    b: ExprId,
    a2: ExprId,
    b2: ExprId,
    eq_a: ExprId,
    eq_b: ExprId,
    h: ExprId,
) -> ExprId {
    let motive_a = d.eq_motive(a, &|d, x| d.mod_eq(modulus, x, b));
    let step1 = d.transport(a, motive_a, h, a2, eq_a);
    let motive_b = d.eq_motive(b, &|d, x| d.mod_eq(modulus, a2, x));
    d.transport(b, motive_b, step1, b2, eq_b)
}

/// `modEq d (a+k) (b+k) → modEq d a b`.
///
/// Peels the two-level existential (mirroring `mod_eq_symm`'s/
/// `mod_eq_mul_left`'s own peeling shape), reassociates each side's witness
/// equation `(a+k)+d*u = (b+k)+d*v` so `k` sits at the tail on both sides
/// ([`swap_tail`]), and finishes with `Nat.add_right_cancel`. The surviving
/// witnesses for `modEq d a b` are the SAME `u,v` the hypothesis carried.
pub(super) fn cancel_common_right_addend(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    a: ExprId,
    b: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let ak = d.add(a, k);
    let bk = d.add(b, k);
    let source = d.mod_eq(modulus, ak, bk);
    let target = d.mod_eq(modulus, a, b);
    let outer_predicate = d.mod_eq_outer_predicate(modulus, ak, bk);
    let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
    let outer_minor = {
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let inner_source = d.mod_eq_inner_exists(modulus, ak, bk, u);
        let inner_source_fv = d.fresh_fvar();
        let inner_source_proof = d.kernel().fvar(inner_source_fv);
        let inner_predicate = d.mod_eq_inner_predicate(modulus, ak, bk, u);
        let inner_motive = d
            .kernel()
            .lam(anon, inner_source, target, BinderInfo::Default);
        let inner_minor = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let du = d.mul(modulus, u);
            let dv = d.mul(modulus, v);
            let lhs0 = d.add(ak, du);
            let rhs0 = d.add(bk, dv);
            let eq_ty = d.eq(lhs0, rhs0);
            let eq_fv = d.fresh_fvar();
            let eq_proof = d.kernel().fvar(eq_fv);

            let a_du = d.add(a, du);
            let b_dv = d.add(b, dv);
            let lhs1 = d.add(a_du, k);
            let rhs1 = d.add(b_dv, k);
            let lhs_rearranged = swap_tail(d, &p, a, k, du);
            let rhs_rearranged = swap_tail(d, &p, b, k, dv);

            let lhs1_eq_lhs0 = d.symm(lhs0, lhs1, lhs_rearranged);
            let t1 = d.trans(lhs1, lhs0, rhs0, lhs1_eq_lhs0, eq_proof);
            let t2 = d.trans(lhs1, rhs0, rhs1, t1, rhs_rearranged);

            let cancelled = d.lemma(p.add_right_cancel, &[a_du, b_dv, k, t2]);

            let target_inner_pred = d.mod_eq_inner_predicate(modulus, a, b, u);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let inner_exists_proof = d.apply(intro, &[nat, target_inner_pred, v, cancelled]);
            // `inner_exists_proof : mod_eq_inner_exists(modulus, a, b, u)` —
            // one level (∃v). Wrap the outer `∃u` too, so the result is the
            // full `target = mod_eq(modulus, a, b)`, not just its `u`-slice.
            let target_outer_pred = d.mod_eq_outer_predicate(modulus, a, b);
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

/// `Nat.mod_eq_cancel : ∀ n c a b, gcd c n = 1 → modEq n (c*a) (c*b) →
/// modEq n a b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_mod_eq_cancel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_cancel, 4, &|d, v| {
        let (modulus, c, a, b) = (v[0], v[1], v[2], v[3]);
        let one = d.num(1);
        let gcd_cn = d.gcd(c, modulus);
        let coprime_ty = d.eq(gcd_cn, one);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let hyp_ty = d.mod_eq(modulus, ca, cb);
        let concl = d.mod_eq(modulus, a, b);
        let inner_arrow = d.arrow(hyp_ty, concl);
        let stmt = d.arrow(coprime_ty, inner_arrow);

        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        // Bezout certificate at g = 1, transported from `gcd_bezout`'s own
        // `g = gcd c modulus` via the coprimality hypothesis.
        let certificate = {
            let base = d.lemma(p.gcd_bezout, &[c, modulus]);
            let motive = d.eq_motive(gcd_cn, &|d, x| d.bezout(c, modulus, x));
            d.transport(gcd_cn, motive, base, one, cop)
        };

        let body = bezout_elim(
            d,
            c,
            modulus,
            one,
            concl,
            certificate,
            &|d, mp, mn, np, nn, equation| {
                // `equation : (1 + c*mn) + modulus*nn = (c*mp) + modulus*np`
                // — already the shape of `modEq modulus (1+c*mn) (c*mp)`
                // with witnesses `(nn, np)`.
                let c_mn = d.mul(c, mn);
                let one_plus_c_mn = d.add(one, c_mn);
                let c_mp = d.mul(c, mp);
                let bz = {
                    let one_level = d.level_one();
                    let intro = d.kernel().const_(p.logic.exists_intro, vec![one_level]);
                    let nat = d.nat_ty();
                    let inner_pred = d.mod_eq_inner_predicate(modulus, one_plus_c_mn, c_mp, nn);
                    let inner = d.apply(intro, &[nat, inner_pred, np, equation]);
                    let outer_pred = d.mod_eq_outer_predicate(modulus, one_plus_c_mn, c_mp);
                    d.apply(intro, &[nat, outer_pred, nn, inner])
                };

                // Scale `bz` by `a` and by `b`.
                let bz_a = d.lemma(p.mod_eq_mul_right, &[modulus, one_plus_c_mn, c_mp, a, bz]);
                let bz_b = d.lemma(p.mod_eq_mul_right, &[modulus, one_plus_c_mn, c_mp, b, bz]);

                // Rewrite the `(1+c*mn)*x` endpoint of each to `x + c*mn*x`;
                // the `c*mp*x` endpoint is already in that form.
                let c_mn_a = d.mul(c_mn, a);
                let a_plus = d.add(a, c_mn_a);
                let eq_a = distrib_one_plus(d, &p, c_mn, a);
                let lhs_a_old = d.mul(one_plus_c_mn, a);
                let rhs_a = d.mul(c_mp, a);
                let refl_rhs_a = d.refl(rhs_a);
                let bz_a2 = rewrite_mod_eq(
                    d, modulus, lhs_a_old, rhs_a, a_plus, rhs_a, eq_a, refl_rhs_a, bz_a,
                );

                let c_mn_b = d.mul(c_mn, b);
                let b_plus = d.add(b, c_mn_b);
                let eq_b = distrib_one_plus(d, &p, c_mn, b);
                let lhs_b_old = d.mul(one_plus_c_mn, b);
                let rhs_b = d.mul(c_mp, b);
                let refl_rhs_b = d.refl(rhs_b);
                let bz_b2 = rewrite_mod_eq(
                    d, modulus, lhs_b_old, rhs_b, b_plus, rhs_b, eq_b, refl_rhs_b, bz_b,
                );

                // Scale the hypothesis `modEq modulus (c*a) (c*b)` by `mp`
                // and by `mn`.
                let h_mp = d.lemma(p.mod_eq_mul_left, &[modulus, ca, cb, mp, hyp]);
                let h_mn = d.lemma(p.mod_eq_mul_left, &[modulus, ca, cb, mn, hyp]);

                let mp_ca = d.mul(mp, ca);
                let mp_cb = d.mul(mp, cb);
                let c_mp_a = d.mul(c_mp, a);
                let c_mp_b = d.mul(c_mp, b);
                let eq_mp_a = scale_reorder(d, &p, mp, c, a);
                let eq_mp_b = scale_reorder(d, &p, mp, c, b);
                let h_mp2 = rewrite_mod_eq(
                    d, modulus, mp_ca, mp_cb, c_mp_a, c_mp_b, eq_mp_a, eq_mp_b, h_mp,
                );

                let mn_ca = d.mul(mn, ca);
                let mn_cb = d.mul(mn, cb);
                let c_mn_a2 = d.mul(c_mn, a);
                let c_mn_b2 = d.mul(c_mn, b);
                let eq_mn_a = scale_reorder(d, &p, mn, c, a);
                let eq_mn_b = scale_reorder(d, &p, mn, c, b);
                let h_mn2 = rewrite_mod_eq(
                    d, modulus, mn_ca, mn_cb, c_mn_a2, c_mn_b2, eq_mn_a, eq_mn_b, h_mn,
                );

                // Chain: a_plus ≡ c_mp*a ≡ c_mp*b ≡ b_plus  [modulus]
                let t1 = d.lemma(
                    p.mod_eq_trans,
                    &[modulus, a_plus, c_mp_a, c_mp_b, bz_a2, h_mp2],
                );
                let bz_b2_symm = d.lemma(p.mod_eq_symm, &[modulus, b_plus, c_mp_b, bz_b2]);
                let t2 = d.lemma(
                    p.mod_eq_trans,
                    &[modulus, a_plus, c_mp_b, b_plus, t1, bz_b2_symm],
                );

                // t2 : modEq modulus (a + c_mn*a) (b + c_mn*b). Bring both
                // sides to share the SAME extra addend `c_mn*a`, via `h_mn2`
                // scaled additively by `b` on the left.
                let t3 = d.lemma(p.mod_eq_add_left, &[modulus, c_mn_a2, c_mn_b2, b, h_mn2]);
                let b_plus_a = d.add(b, c_mn_a2);
                let t3_symm = d.lemma(p.mod_eq_symm, &[modulus, b_plus_a, b_plus, t3]);
                let t4 = d.lemma(
                    p.mod_eq_trans,
                    &[modulus, a_plus, b_plus, b_plus_a, t2, t3_symm],
                );
                // t4 : modEq modulus (a + c_mn*a) (b + c_mn*a)

                cancel_common_right_addend(d, &p, modulus, a, b, c_mn_a2, t4)
            },
        );

        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        let proof = d.lam_fv(cop_fv, coprime_ty, with_hyp);
        (stmt, proof)
    })?;
    Ok(())
}
