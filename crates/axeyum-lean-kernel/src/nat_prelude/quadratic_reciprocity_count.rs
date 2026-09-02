//! **The `Nat`-side half of quadratic reciprocity's assembly** — ADR-1552's
//! residue 1, step 1.
//!
//! Two declarations, both pure assembly over inputs that already existed:
//!
//! ```text
//! Nat.gaussCount_sum_even : ∀ m n, Eq (gcd (succ (2*n)) (succ (2*m))) 1 →
//!   Even (add (add N_p N_q) (mul n m))
//!
//! Nat.gaussCount_sum_modEq : ∀ m n, Eq (gcd (succ (2*n)) (succ (2*m))) 1 →
//!   modEq 2 (add N_p N_q) (mul n m)
//! ```
//!
//! with `pp := succ (2*m)`, `q := succ (2*n)`,
//! `N_p := gaussNegCount pp q m`, `N_q := gaussNegCount q pp n`,
//! `F_p := Σ_{x<m} ⌊q(x+1)/pp⌋` and `F_q := Σ_{y<n} ⌊pp(y+1)/q⌋`.
//!
//! # What this is
//!
//! `N_p` is the exponent Gauss's lemma (`Int.gaussLemmaSignCount`) puts on
//! `-1` to name the Legendre symbol `(q|pp)`; `N_q` names `(pp|q)`. So
//! `N_p + N_q ≡ n·m (mod 2)` **is** quadratic reciprocity, one `(-1)^·` away
//! from the classical statement. The `Int`-side half of the assembly lives in
//! `int_prelude/quadratic_reciprocity.rs`.
//!
//! # The three inputs, and that they line up
//!
//! Nothing new is proved here. The content is that ADR-1552's two halves
//! mesh, index function for index function:
//!
//! - `Nat.eisenstein_lemma m n` gives `Even (F_p + N_p)`, on `gcd q pp = 1`.
//! - `Nat.eisenstein_lemma n m` gives `Even (F_q + N_q)`, on `gcd pp q = 1` —
//!   at `(n, m)` its own `pp` is `succ (2*n) = q` and its own `a` is
//!   `succ (2*m) = pp`, so its floor sum is literally `F_q` and its count is
//!   literally `N_q`. **The two instances share no term but the hypothesis**,
//!   which is why the pairing is legitimate rather than a coincidence of
//!   spelling.
//! - `Nat.eisenstein_floor_sum_min_free m n` gives `F_p + F_q = n·m`, on
//!   `gcd pp q = 1`. Its two summands are spelled exactly as the two
//!   `eisenstein_lemma` instances spell theirs (`fun j => div (mul q (succ j))
//!   pp` and its mirror), so no congruence is needed to align them.
//!
//! The hypothesis orders differ — `eisenstein_lemma` takes `gcd q pp = 1` and
//! the other two take `gcd pp q = 1` — so one `Nat.gcd_comm` is the only
//! bridging step in the file.
//!
//! # The arithmetic
//!
//! ```text
//!   (N_p + N_q) + n·m
//! = (N_p + N_q) + (F_p + F_q)          [floor sum, backwards]
//! = (F_p + F_q) + (N_p + N_q)          [add_comm]
//! = (F_p + N_p) + (F_q + N_q)          [regroup_four]
//! = (k₁ + k₁) + (k₂ + k₂)              [the two Even witnesses]
//! = (k₁ + k₂) + (k₁ + k₂)              [regroup_four]
//! ```
//!
//! so `Even` holds at `k := k₁ + k₂`. No subtraction anywhere, which is why
//! the truncated `Nat.sub` never enters.
//!
//! The congruence form is the same two-line corollary
//! `Nat.eisenstein_lemma_modEq` is: `Nat.modEq d a b := ∃ u v, a + d*u =
//! b + d*v` is the BALANCED form, so from `S + T = k + k` the witnesses are
//! `u := T` and `v := k`, and `S + 2·T = (S + T) + T = (k + k) + T` matches
//! `T + 2·k = T + (k + k)` by one `add_comm`.
//!
//! # What this does NOT prove
//!
//! Nothing about primality. Both inputs ask only for coprimality of the two
//! odd numbers, so this statement does too — a strict generalization of the
//! textbook one, in the same way ADR-1544 recorded for
//! `Nat.eisenstein_floor_sum`. At two distinct odd primes `p = 2m+1`,
//! `q = 2n+1` the hypothesis is discharged by `Nat.coprime_primes`-style
//! reasoning or, at concrete pairs, by `Eq.refl`.

use super::NatPrelude;
use super::eisenstein_lemma::{regroup_four, two_mul};
use super::ops::{NatDev, NatOps};
use super::parity::even_predicate;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `fun j => body (succ j)` — the one-based shift every index function in
/// this family shares. A per-file copy of `eisenstein_lemma.rs`'s private
/// helper of the same name (this prelude's stated convention); it must build
/// the *same* term, which is what lets the floor sums match without a
/// congruence.
fn shifted(d: &mut NatDev<'_>, body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let b = body(d, sj);
    d.lam_fv(j_fv, nat, b)
}

/// Every term the two declarations share, built once at `(m, n)`.
struct Shapes {
    /// `succ (2*m)`.
    pp: ExprId,
    /// `succ (2*n)`.
    q: ExprId,
    /// `Σ_{x<m} ⌊q(x+1)/pp⌋`.
    f_p: ExprId,
    /// `Σ_{y<n} ⌊pp(y+1)/q⌋`.
    f_q: ExprId,
    /// `gaussNegCount pp q m`.
    n_p: ExprId,
    /// `gaussNegCount q pp n`.
    n_q: ExprId,
    /// `add N_p N_q`.
    s: ExprId,
    /// `mul n m`.
    t: ExprId,
}

fn shapes(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> Shapes {
    let two = d.num(2);
    let ap = d.mul(two, m);
    let pp = d.succ(ap);
    let aq = d.mul(two, n);
    let q = d.succ(aq);

    let floor_p = shifted(d, &|d, k| {
        let prod = d.mul(q, k);
        d.div(prod, pp)
    });
    let f_p = d.sum_range(floor_p, m);
    let floor_q = shifted(d, &|d, k| {
        let prod = d.mul(pp, k);
        d.div(prod, q)
    });
    let f_q = d.sum_range(floor_q, n);

    let n_p = d.const_app(p.gauss_neg_count, &[pp, q, m]);
    let n_q = d.const_app(p.gauss_neg_count, &[q, pp, n]);
    let s = d.add(n_p, n_q);
    let t = d.mul(n, m);

    Shapes {
        pp,
        q,
        f_p,
        f_q,
        n_p,
        n_q,
        s,
        t,
    }
}

/// `Nat.gaussCount_sum_even` — see this module's doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_gauss_count_sum_even(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.gauss_count_sum_even, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let nat = d.nat_ty();
        let level_one = d.level_one();
        let sh = shapes(d, &p, m, n);

        let one = d.num(1);
        let g_qp = d.gcd(sh.q, sh.pp);
        let cop_ty = d.eq(g_qp, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        // `gcd pp q = 1`, the argument order the other two inputs take.
        let g_pq = d.gcd(sh.pp, sh.q);
        let cop_flip = {
            let h = d.lemma(p.gcd_comm, &[sh.pp, sh.q]);
            d.trans(g_pq, g_qp, one, h, cop)
        };

        let x = d.add(sh.s, sh.t);
        let even_x = d.const_app(p.even, &[x]);
        let stmt = d.arrow(cop_ty, even_x);

        let hf = d.lemma(p.eisenstein_floor_sum_min_free, &[m, n, cop_flip]);
        let e1 = d.lemma(p.eisenstein_lemma, &[m, n, cop]);
        let e2 = d.lemma(p.eisenstein_lemma, &[n, m, cop_flip]);

        let x1 = d.add(sh.f_p, sh.n_p);
        let x2 = d.add(sh.f_q, sh.n_q);
        let even_x1 = d.const_app(p.even, &[x1]);
        let even_x2 = d.const_app(p.even, &[x2]);
        let pred1 = even_predicate(d, x1);
        let pred2 = even_predicate(d, x2);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);

        let minor1 = {
            let k1_fv = d.fresh_fvar();
            let k1 = d.kernel().fvar(k1_fv);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let k1k1 = d.add(k1, k1);
            let h1_ty = d.eq(x1, k1k1);

            let minor2 = {
                let k2_fv = d.fresh_fvar();
                let k2 = d.kernel().fvar(k2_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let k2k2 = d.add(k2, k2);
                let h2_ty = d.eq(x2, k2k2);

                let fpq = d.add(sh.f_p, sh.f_q);
                let step1 = d.add(sh.s, fpq);
                let e_1 = {
                    let back = d.symm(fpq, sh.t, hf);
                    d.congr(sh.t, fpq, back, &|d, z| d.add(sh.s, z))
                };
                let step2 = d.add(fpq, sh.s);
                let e_2 = d.lemma(p.add_comm, &[sh.s, fpq]);
                let step3 = d.add(x1, x2);
                let e_3 = regroup_four(d, &p, sh.f_p, sh.f_q, sh.n_p, sh.n_q);
                let step4 = d.add(k1k1, x2);
                let e_4 = d.congr(x1, k1k1, h1, &|d, z| d.add(z, x2));
                let step5 = d.add(k1k1, k2k2);
                let e_5 = d.congr(x2, k2k2, h2, &|d, z| d.add(k1k1, z));
                let k12 = d.add(k1, k2);
                let target = d.add(k12, k12);
                let e_6 = regroup_four(d, &p, k1, k1, k2, k2);

                let (_end, equation) = d.chain(
                    x,
                    &[
                        (step1, e_1),
                        (step2, e_2),
                        (step3, e_3),
                        (step4, e_4),
                        (step5, e_5),
                        (target, e_6),
                    ],
                );

                let pred_x = even_predicate(d, x);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
                let proof = d.apply(intro, &[nat, pred_x, k12, equation]);
                let with_h2 = d.lam_fv(h2_fv, h2_ty, proof);
                d.lam_fv(k2_fv, nat, with_h2)
            };

            let motive2 = {
                let anon = d.anon_name();
                d.kernel().lam(anon, even_x2, even_x, BinderInfo::Default)
            };
            let body2 = d.apply(rec, &[nat, pred2, motive2, minor2, e2]);
            let with_h1 = d.lam_fv(h1_fv, h1_ty, body2);
            d.lam_fv(k1_fv, nat, with_h1)
        };

        let motive1 = {
            let anon = d.anon_name();
            d.kernel().lam(anon, even_x1, even_x, BinderInfo::Default)
        };
        let body = d.apply(rec, &[nat, pred1, motive1, minor1, e1]);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.gaussCount_sum_modEq` — the congruence form. See this module's doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_gauss_count_sum_mod_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.gauss_count_sum_mod_eq, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let nat = d.nat_ty();
        let level_one = d.level_one();
        let two = d.num(2);
        let sh = shapes(d, &p, m, n);

        let one = d.num(1);
        let g_qp = d.gcd(sh.q, sh.pp);
        let cop_ty = d.eq(g_qp, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        let x = d.add(sh.s, sh.t);
        let target_ty = d.mod_eq(two, sh.s, sh.t);
        let even_x = d.const_app(p.even, &[x]);
        let even_pred = even_predicate(d, x);
        let evidence = d.lemma(p.gauss_count_sum_even, &[m, n, cop]);

        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let kk = d.add(k, k);
            let hk_ty = d.eq(x, kk);

            // `S + 2*T = (S + T) + T = (k + k) + T = T + (k + k) = T + 2*k`.
            let two_t = d.mul(two, sh.t);
            let start = d.add(sh.s, two_t);
            let tt = d.add(sh.t, sh.t);
            let step1 = d.add(sh.s, tt);
            let e_1 = {
                let tm = two_mul(d, &p, sh.t);
                d.congr(two_t, tt, tm, &|d, z| d.add(sh.s, z))
            };
            let step2 = d.add(x, sh.t);
            let e_2 = {
                let fwd = d.lemma(p.add_assoc, &[sh.s, sh.t, sh.t]);
                d.symm(step2, step1, fwd)
            };
            let step3 = d.add(kk, sh.t);
            let e_3 = d.congr(x, kk, hk, &|d, z| d.add(z, sh.t));
            let step4 = d.add(sh.t, kk);
            let e_4 = d.lemma(p.add_comm, &[kk, sh.t]);
            let two_k = d.mul(two, k);
            let target = d.add(sh.t, two_k);
            let e_5 = {
                let tm = two_mul(d, &p, k);
                let back = d.symm(two_k, kk, tm);
                d.congr(kk, two_k, back, &|d, z| d.add(sh.t, z))
            };
            let (_end, equation) = d.chain(
                start,
                &[
                    (step1, e_1),
                    (step2, e_2),
                    (step3, e_3),
                    (step4, e_4),
                    (target, e_5),
                ],
            );

            let inner_pred = d.mod_eq_inner_predicate(two, sh.s, sh.t, sh.t);
            let outer_pred = d.mod_eq_outer_predicate(two, sh.s, sh.t);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
            let inner = d.apply(intro, &[nat, inner_pred, k, equation]);
            let proof = d.apply(intro, &[nat, outer_pred, sh.t, inner]);

            let with_hk = d.lam_fv(hk_fv, hk_ty, proof);
            d.lam_fv(k_fv, nat, with_hk)
        };

        let motive = {
            let anon = d.anon_name();
            d.kernel().lam(anon, even_x, target_ty, BinderInfo::Default)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
        let body = d.apply(rec, &[nat, even_pred, motive, minor, evidence]);

        let stmt = d.arrow(cop_ty, target_ty);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// Declare everything this module owns.
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_quadratic_reciprocity_count_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_gauss_count_sum_even(d, p)?;
    declare_gauss_count_sum_mod_eq(d, p)?;
    Ok(())
}
