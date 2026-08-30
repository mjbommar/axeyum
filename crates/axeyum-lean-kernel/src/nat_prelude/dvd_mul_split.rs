//! `Nat.dvd_mul_split : ∀ k m n, dvd k (mul m n) ↔ ∃ k1 k2, dvd k1 m ∧ dvd k2
//! n ∧ mul k1 k2 = k` -- Mathlib's `Nat.dvd_mul`
//! (`F:ml430-nat-dvd-mul-ebd102e2`).
//!
//! **Not named `Nat.dvd_mul`.** That kernel name is already taken by the
//! unrelated trivial lemma `∀ a q, dvd a (a*q)` (`nat_prelude.rs`'s
//! `dvd_mul` field, used pervasively as "a divides a*anything" -- checked
//! before writing this file: `pub dvd_mul: NameId` doc reads
//! `Nat.dvd_mul : ∀ a q, dvd a (a * q)`). Declaring under Mathlib's literal
//! name would hit `DeclarationExists` -- exactly the `Nat.inverseIndex`
//! collision class this development has hit before. `dvd_mul_split` is free
//! in both `nat_prelude` and `int_prelude` (checked before writing this
//! file: `grep -n '"dvd_mul_split"' nat_prelude.rs int_prelude.rs` is
//! empty).
//!
//! Two prior lanes sized this as "no short route" before `Nat.gcd_mul_right`
//! existed (`gcd_mul_right.rs`, landed same day). With it, the forward
//! direction is a direct application, no new induction.
//!
//! # Strategy
//!
//! **Reverse (`mpr`).** Fully uniform, no case split: given `k1 ∣ m`
//! (witness `q1`, `m = k1*q1`) and `k2 ∣ n` (witness `q2`, `n = k2*q2`) and
//! `k1*k2 = k`, `m*n = (k1*q1)*(k2*q2) = (k1*k2)*(q1*q2) = k*(q1*q2)`
//! (`mul_mul_mul_comm` below), giving `k ∣ m*n` with witness `q1*q2`. Works
//! uniformly even when `k1` or `k2` is `0`.
//!
//! **Forward (`mp`), case split on `k` (`cases_zero_succ`).**
//!
//! - `k = 0`: `h : dvd 0 (m*n)` gives `m*n = 0` (`dvd_elim` + `zero_mul`),
//!   so `mul_eq_zero` splits into `m = 0` or `n = 0`.
//!   - `m = 0`: witnesses `(k1, k2) := (0, n)`. `dvd 0 m` from `m=0`;
//!     `dvd n n` (`dvd_refl`); `0*n = 0 = k`.
//!   - `n = 0`: witnesses `(k1, k2) := (m, 0)`, symmetric.
//!   Neither branch touches the gcd construction below -- this is exactly
//!   the corner the task's own working notes warned "a slick argument
//!   silently breaks" on: the general formula's `k2 := k/gcd(k,m)` would
//!   need `gcd(0,m) = m` and `0/m = 0`, which does NOT reproduce a valid
//!   witness pair when `n ≠ 0 = m` (it would force `k2 = 0`, needing
//!   `0 ∣ n`, false in general). Direct case split sidesteps this entirely.
//! - `k = succ pred =: K` (so `pos_k : Lt 0 K` via `NatOps::zero_lt_succ`,
//!   free): let `g := gcd(K, m)`.
//!   - `k1 := g`. `dvd g m` is `gcd_dvd_right(K, m)` directly.
//!   - `dvd_g_k := gcd_dvd_left(K, m) : dvd g K`. `one_le_g :=
//!     one_le_of_dvd_pos(g, K, pos_k, dvd_g_k) : Le 1 g` -- a divisor of a
//!     positive number is positive, no case split on `g` needed.
//!   - `dvd_elim` on `dvd_g_k` gives witness `q` with `K = g*q`; `k2 := q`,
//!     and `symm` of that equation is directly the third conjunct
//!     `Eq (mul g q) K`.
//!   - The real content, `dvd q n`: `K ∣ K*n` (`dvd_mul`) and `K ∣ m*n`
//!     (`h`) combine via `dvd_gcd` into `K ∣ gcd(K*n, m*n)`; `gcd_mul_right`
//!     rewrites the gcd to `g*n`, giving `K ∣ g*n`; substituting `K = g*q`
//!     gives `g*q ∣ g*n`; cancelling the common positive factor `g`
//!     (`dvd_cancel_left_of_pos`, local copy of `lcm_gcd_lemmas.rs`'s
//!     helper) gives `q ∣ n`.

use super::NatPrelude;
use super::binomial::mul_left_comm;
use super::helpers::{and_left, and_right, transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Local term-building helpers (this development's per-file-copy convention;
// see `divisibility.rs`/`lcm_gcd_lemmas.rs`/`coprime_lemmas.rs` etc. for the
// canonical originals).
// ---------------------------------------------------------------------------

fn dvd_elim(
    d: &mut NatDev<'_>,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec_name = d.prelude().logic.exists_rec;
    let rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

fn dvd_intro(
    d: &mut NatDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// Local copy of `lcm_gcd_lemmas.rs`'s private helper of the same name and
/// signature: given `k_pos : Le 1 k` and `dvd_hyp : dvd (mul k a) (mul k b)`,
/// build a proof of `dvd a b`.
fn dvd_cancel_left_of_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    dvd_hyp: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let kb = d.mul(k, b);
    let goal = d.dvd(a, b);
    dvd_elim(d, ka, kb, goal, dvd_hyp, &|d, q, eq_proof| {
        // eq_proof : Eq kb (mul ka q)
        let ka_q = d.mul(ka, q);
        let aq = d.mul(a, q);
        let k_aq = d.mul(k, aq);
        let assoc = d.lemma(p.mul_assoc, &[k, a, q]); // Eq ka_q k_aq
        let (_, kb_eq_k_aq) = d.chain(kb, &[(ka_q, eq_proof), (k_aq, assoc)]);
        let cancelled = d.lemma(p.mul_left_cancel_of_pos, &[k, b, aq, k_pos, kb_eq_k_aq]); // Eq b aq
        dvd_intro(d, a, b, q, cancelled)
    })
}

/// `Eq (mul (mul a b) (mul c dd)) (mul (mul a c) (mul b dd))` -- the
/// four-factor regrouping the reverse direction needs to land
/// `(k1*q1)*(k2*q2)` on `(k1*k2)*(q1*q2)`.
fn mul_mul_mul_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> ExprId {
    let p = *p;
    let ab = d.mul(a, b);
    let cd = d.mul(c, dd);
    let start = d.mul(ab, cd); // (a*b)*(c*d)

    let bcd = d.mul(b, cd); // b*(c*d)
    let step1 = d.lemma(p.mul_assoc, &[a, b, cd]); // Eq start (a*bcd)
    let a_bcd = d.mul(a, bcd);

    let bd = d.mul(b, dd); // b*d
    let cbd = d.mul(c, bd); // c*(b*d)
    let step2 = mul_left_comm(d, &p, b, c, dd); // Eq bcd cbd
    let congr2 = d.congr(bcd, cbd, step2, &|d, t| d.mul(a, t)); // Eq a_bcd (a*cbd)
    let a_cbd = d.mul(a, cbd);

    let ac = d.mul(a, c);
    let target = d.mul(ac, bd); // (a*c)*(b*d)
    let step3 = d.lemma(p.mul_assoc, &[a, c, bd]); // Eq target a_cbd
    let step3_rev = d.symm(target, a_cbd, step3); // Eq a_cbd target

    let (_, proof) = d.chain(start, &[(a_bcd, step1), (a_cbd, congr2), (target, step3_rev)]);
    proof
}

// ---------------------------------------------------------------------------
// `∃ k1 k2, And (dvd k1 m) (And (dvd k2 n) (Eq (mul k1 k2) k))` -- the type,
// its introduction, and its elimination. Written once, non-generically, for
// exactly this shape (this development's convention: see `dvd_elim`'s own
// doubling in `dvd_cancel_left_of_pos` above for the same style one level
// shallower).
// ---------------------------------------------------------------------------

/// The `And` body (no outer `Exists`), as a TYPE, for concrete `k1`, `k2`.
fn split_body_ty(
    d: &mut NatDev<'_>,
    k1: ExprId,
    k2: ExprId,
    m: ExprId,
    n: ExprId,
    k: ExprId,
) -> ExprId {
    let logic = d.prelude().logic;
    let dvd_k1_m = d.dvd(k1, m);
    let dvd_k2_n = d.dvd(k2, n);
    let k1k2 = d.mul(k1, k2);
    let eq_k1k2_k = d.eq(k1k2, k);
    let inner = d.const_app(logic.and, &[dvd_k2_n, eq_k1k2_k]);
    d.const_app(logic.and, &[dvd_k1_m, inner])
}

/// `∃ k1 k2, And (dvd k1 m) (And (dvd k2 n) (Eq (mul k1 k2) k))`, as a TYPE.
fn split_exists_ty(d: &mut NatDev<'_>, m: ExprId, n: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let inner_predicate = {
        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let body = split_body_ty(d, k1, k2, m, n, k);
        d.lam_fv(k2_fv, nat, body)
    };
    let exists = d.kernel().const_(exists_name, vec![one]);
    let inner_exists = d.apply(exists, &[nat, inner_predicate]);
    let outer_predicate = d.lam_fv(k1_fv, nat, inner_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, outer_predicate])
}

/// Introduce `∃ k1 k2, And (dvd k1 m) (And (dvd k2 n) (Eq (mul k1 k2) k))`
/// from concrete `k1`, `k2` and a proof of the (concrete) body.
#[allow(clippy::too_many_arguments)]
fn split_exists_intro(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    k1: ExprId,
    k2: ExprId,
    body_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let intro_name = d.prelude().logic.exists_intro;
    let exists_name = d.prelude().logic.exists_;

    let k2_predicate = {
        let k2_fv = d.fresh_fvar();
        let k2_var = d.kernel().fvar(k2_fv);
        let body = split_body_ty(d, k1, k2_var, m, n, k);
        d.lam_fv(k2_fv, nat, body)
    };
    let intro = d.kernel().const_(intro_name, vec![one]);
    let k2_exists_proof = d.apply(intro, &[nat, k2_predicate, k2, body_proof]);

    let k1_predicate = {
        let k1_fv = d.fresh_fvar();
        let k1_var = d.kernel().fvar(k1_fv);
        let k1_body = {
            let k2_fv2 = d.fresh_fvar();
            let k2_var2 = d.kernel().fvar(k2_fv2);
            let body = split_body_ty(d, k1_var, k2_var2, m, n, k);
            let k2_predicate2 = d.lam_fv(k2_fv2, nat, body);
            let exists = d.kernel().const_(exists_name, vec![one]);
            d.apply(exists, &[nat, k2_predicate2])
        };
        d.lam_fv(k1_fv, nat, k1_body)
    };
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, k1_predicate, k1, k2_exists_proof])
}

/// Eliminate `witness : ∃ k1 k2, And (dvd k1 m) (And (dvd k2 n) (Eq (mul k1
/// k2) k))` against an arbitrary `goal`, given a continuation that consumes
/// concrete (bound) `k1`, `k2` and the (concrete) body proof.
#[allow(clippy::too_many_arguments)]
fn split_exists_elim(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    goal: ExprId,
    witness: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.prelude().logic.exists_;
    let exists_rec_name = d.prelude().logic.exists_rec;

    let outer_predicate = {
        let k1_fv = d.fresh_fvar();
        let k1_var = d.kernel().fvar(k1_fv);
        let inner_predicate = {
            let k2_fv = d.fresh_fvar();
            let k2_var = d.kernel().fvar(k2_fv);
            let body = split_body_ty(d, k1_var, k2_var, m, n, k);
            d.lam_fv(k2_fv, nat, body)
        };
        let exists_c = d.kernel().const_(exists_name, vec![one]);
        let inner_exists = d.apply(exists_c, &[nat, inner_predicate]);
        d.lam_fv(k1_fv, nat, inner_exists)
    };
    let outer_ty = {
        let exists_c = d.kernel().const_(exists_name, vec![one]);
        d.apply(exists_c, &[nat, outer_predicate])
    };
    let outer_motive = d.kernel().lam(anon, outer_ty, goal, BinderInfo::Default);

    let outer_minor = {
        let k1_fv = d.fresh_fvar();
        let k1_var = d.kernel().fvar(k1_fv);

        let inner_predicate = {
            let k2_fv = d.fresh_fvar();
            let k2_var = d.kernel().fvar(k2_fv);
            let body = split_body_ty(d, k1_var, k2_var, m, n, k);
            d.lam_fv(k2_fv, nat, body)
        };
        let inner_ty = {
            let exists_c = d.kernel().const_(exists_name, vec![one]);
            d.apply(exists_c, &[nat, inner_predicate])
        };
        let inner_motive = d.kernel().lam(anon, inner_ty, goal, BinderInfo::Default);
        let inner_minor = {
            let k2_fv = d.fresh_fvar();
            let k2_var = d.kernel().fvar(k2_fv);
            let body_ty = split_body_ty(d, k1_var, k2_var, m, n, k);
            let body_fv = d.fresh_fvar();
            let body_var = d.kernel().fvar(body_fv);
            let result = continuation(d, k1_var, k2_var, body_var);
            let with_body = d.lam_fv(body_fv, body_ty, result);
            d.lam_fv(k2_fv, nat, with_body)
        };
        let inner_pf_fv = d.fresh_fvar();
        let inner_pf_var = d.kernel().fvar(inner_pf_fv);
        let inner_rec = d.kernel().const_(exists_rec_name, vec![one]);
        let inner_result = d.apply(
            inner_rec,
            &[nat, inner_predicate, inner_motive, inner_minor, inner_pf_var],
        );
        let with_inner = d.lam_fv(inner_pf_fv, inner_ty, inner_result);
        d.lam_fv(k1_fv, nat, with_inner)
    };
    let outer_rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(
        outer_rec,
        &[nat, outer_predicate, outer_motive, outer_minor, witness],
    )
}

// ---------------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------------

/// `Nat.dvd_mul_split : ∀ k m n, Iff (dvd k (mul m n)) (∃ k1 k2, And (dvd k1
/// m) (And (dvd k2 n) (Eq (mul k1 k2) k)))`. See the module doc.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_dvd_mul_split(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let logic = d.prelude().logic;

    d.theorem(p.dvd_mul_split, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let mn = d.mul(m, n);
        let dvd_k_mn = d.dvd(k, mn);
        let exists_ty = split_exists_ty(d, m, n, k);
        let stmt = d.const_app(logic.iff, &[dvd_k_mn, exists_ty]);

        // ---- mpr: the exists implies dvd k (m*n), uniformly, no case split.
        let mpr = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = split_exists_elim(d, m, n, k, dvd_k_mn, w, &|d, k1, k2, body_proof| {
                let dvd_k2_n = d.dvd(k2, n);
                let k1k2 = d.mul(k1, k2);
                let eq_k1k2_k = d.eq(k1k2, k);
                let dvd_k1_m = d.dvd(k1, m);
                let inner_ty = d.const_app(logic.and, &[dvd_k2_n, eq_k1k2_k]);
                let dvd_k1_m_proof = and_left(d, dvd_k1_m, inner_ty, body_proof);
                let inner_proof = and_right(d, dvd_k1_m, inner_ty, body_proof);
                let dvd_k2_n_proof = and_left(d, dvd_k2_n, eq_k1k2_k, inner_proof);
                let eq_k1k2_k_proof = and_right(d, dvd_k2_n, eq_k1k2_k, inner_proof);

                dvd_elim(d, k1, m, dvd_k_mn, dvd_k1_m_proof, &|d, q1, eq_m_k1q1| {
                    // eq_m_k1q1 : Eq m (mul k1 q1)
                    dvd_elim(d, k2, n, dvd_k_mn, dvd_k2_n_proof, &|d, q2, eq_n_k2q2| {
                        // eq_n_k2q2 : Eq n (mul k2 q2)
                        let k1q1 = d.mul(k1, q1);
                        let k2q2 = d.mul(k2, q2);
                        let congr_left = d.congr(m, k1q1, eq_m_k1q1, &|d, t| d.mul(t, n));
                        // congr_left : Eq (mul m n) (mul k1q1 n)
                        let mn2 = d.mul(k1q1, n);
                        let congr_right = d.congr(n, k2q2, eq_n_k2q2, &|d, t| d.mul(k1q1, t));
                        // congr_right : Eq (mul k1q1 n) (mul k1q1 k2q2)
                        let mn3 = d.mul(k1q1, k2q2);
                        let regroup = mul_mul_mul_comm(d, &p, k1, q1, k2, q2);
                        // regroup : Eq mn3 (mul (mul k1 k2) (mul q1 q2))
                        let k1k2_val = d.mul(k1, k2);
                        let q1q2 = d.mul(q1, q2);
                        let mn4 = d.mul(k1k2_val, q1q2);
                        let congr_k =
                            d.congr(k1k2_val, k, eq_k1k2_k_proof, &|d, t| d.mul(t, q1q2));
                        // congr_k : Eq mn4 (mul k q1q2)
                        let k_q1q2 = d.mul(k, q1q2);
                        let (_, eq_mn_k_q1q2) = d.chain(
                            mn,
                            &[
                                (mn2, congr_left),
                                (mn3, congr_right),
                                (mn4, regroup),
                                (k_q1q2, congr_k),
                            ],
                        );
                        dvd_intro(d, k, mn, q1q2, eq_mn_k_q1q2)
                    })
                })
            });
            d.lam_fv(w_fv, exists_ty, body)
        };

        // ---- mp: dvd k (m*n) implies the exists. Case split on k.
        let mp = cases_zero_succ(
            d,
            k,
            &|d, kv| {
                let dvd_ty = d.dvd(kv, mn);
                let ex_ty = split_exists_ty(d, m, n, kv);
                d.arrow(dvd_ty, ex_ty)
            },
            &|d| {
                let zero = d.zero();
                let dvd0_mn_ty = d.dvd(zero, mn);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let eq_ty = d.eq(mn, zero);
                let eq_mn_zero = dvd_elim(d, zero, mn, eq_ty, h, &|d, q, eq_proof| {
                    // eq_proof : Eq mn (mul zero q)
                    let zero_q = d.mul(zero, q);
                    let zm = d.lemma(p.zero_mul, &[q]); // Eq zero_q zero
                    let (_, chained) = d.chain(mn, &[(zero_q, eq_proof), (zero, zm)]);
                    chained
                });
                let disj = d.lemma(p.mul_eq_zero, &[m, n, eq_mn_zero]); // Or (Eq m 0) (Eq n 0)
                let m_eq0 = d.eq(m, zero);
                let n_eq0 = d.eq(n, zero);
                let target = split_exists_ty(d, m, n, zero);

                let left_branch = {
                    let hm_fv = d.fresh_fvar();
                    let hm = d.kernel().fvar(hm_fv); // Eq m zero
                    let mul_zero_zero = d.mul(zero, zero);
                    let zm0 = d.lemma(p.zero_mul, &[zero]); // Eq mul_zero_zero zero
                    let zm0_rev = d.symm(mul_zero_zero, zero, zm0); // Eq zero mul_zero_zero
                    let (_, m_eq_00) = d.chain(m, &[(zero, hm), (mul_zero_zero, zm0_rev)]);
                    let dvd0_m = dvd_intro(d, zero, m, zero, m_eq_00); // dvd zero m
                    let dvd_n_n = d.lemma(p.dvd_refl, &[n]); // dvd n n
                    let eq_0n_0 = d.lemma(p.zero_mul, &[n]); // Eq (mul zero n) zero
                    let dvd_n_n_ty = d.dvd(n, n);
                    let zero_n = d.mul(zero, n);
                    let eq_0n_0_ty = d.eq(zero_n, zero);
                    let dvd_0_m_ty = d.dvd(zero, m);
                    let inner_ty = d.const_app(logic.and, &[dvd_n_n_ty, eq_0n_0_ty]);
                    let inner_and =
                        d.const_app(logic.and_intro, &[dvd_n_n_ty, eq_0n_0_ty, dvd_n_n, eq_0n_0]);
                    let full_and =
                        d.const_app(logic.and_intro, &[dvd_0_m_ty, inner_ty, dvd0_m, inner_and]);
                    let proof = split_exists_intro(d, m, n, zero, zero, n, full_and);
                    d.lam_fv(hm_fv, m_eq0, proof)
                };
                let right_branch = {
                    let hn_fv = d.fresh_fvar();
                    let hn = d.kernel().fvar(hn_fv); // Eq n zero
                    let dvd_m_m = d.lemma(p.dvd_refl, &[m]); // dvd m m
                    let mul_zero_zero = d.mul(zero, zero);
                    let zm0 = d.lemma(p.zero_mul, &[zero]);
                    let zm0_rev = d.symm(mul_zero_zero, zero, zm0);
                    let (_, n_eq_00) = d.chain(n, &[(zero, hn), (mul_zero_zero, zm0_rev)]);
                    let dvd0_n = dvd_intro(d, zero, n, zero, n_eq_00); // dvd zero n
                    let eq_m0_0 = d.lemma(p.mul_zero, &[m]); // Eq (mul m zero) zero
                    let dvd_0_n_ty = d.dvd(zero, n);
                    let m_zero = d.mul(m, zero);
                    let eq_m0_0_ty = d.eq(m_zero, zero);
                    let dvd_m_m_ty = d.dvd(m, m);
                    let inner_ty = d.const_app(logic.and, &[dvd_0_n_ty, eq_m0_0_ty]);
                    let inner_and =
                        d.const_app(logic.and_intro, &[dvd_0_n_ty, eq_m0_0_ty, dvd0_n, eq_m0_0]);
                    let full_and =
                        d.const_app(logic.and_intro, &[dvd_m_m_ty, inner_ty, dvd_m_m, inner_and]);
                    let proof = split_exists_intro(d, m, n, zero, m, zero, full_and);
                    d.lam_fv(hn_fv, n_eq0, proof)
                };
                let or_elim_body = d.const_app(
                    logic.or_elim,
                    &[m_eq0, n_eq0, target, disj, left_branch, right_branch],
                );
                d.lam_fv(h_fv, dvd0_mn_ty, or_elim_body)
            },
            &|d, pred| {
                let kk = d.succ(pred);
                let dvd_k_mn_ty = d.dvd(kk, mn);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv); // dvd kk mn

                let pos_k = d.zero_lt_succ(pred); // Lt 0 kk
                let g = d.gcd(kk, m);
                let dvd_g_m = d.lemma(p.gcd_dvd_right, &[kk, m]); // dvd g m
                let dvd_g_k = d.lemma(p.gcd_dvd_left, &[kk, m]); // dvd g kk
                let one_le_g = d.lemma(p.one_le_of_dvd_pos, &[g, kk, pos_k, dvd_g_k]); // Le 1 g

                let target = split_exists_ty(d, m, n, kk);
                let result = dvd_elim(d, g, kk, target, dvd_g_k, &|d, q, eq_k_gq| {
                    // eq_k_gq : Eq kk (mul g q)
                    let gq = d.mul(g, q);
                    let eq_gq_k = d.symm(kk, gq, eq_k_gq); // Eq (mul g q) kk

                    let kk_n = d.mul(kk, n);
                    let dvd_kk_kkn = d.lemma(p.dvd_mul, &[kk, n]); // dvd kk (kk*n)
                    let dvd_kk_gcd = d.lemma(p.dvd_gcd, &[kk, kk_n, mn, dvd_kk_kkn, h]);
                    // dvd_kk_gcd : dvd kk (gcd kk_n mn)
                    let gmr = d.lemma(p.gcd_mul_right, &[kk, m, n]);
                    // gmr : Eq (gcd kk_n mn) (mul g n)
                    let gcd_kkn_mn = d.gcd(kk_n, mn);
                    let g_n = d.mul(g, n);
                    let dvd_kk_gn =
                        transport_dvd_right(d, kk, gcd_kkn_mn, g_n, gmr, dvd_kk_gcd);
                    // dvd_kk_gn : dvd kk (mul g n)
                    let dvd_gq_gn = transport_dvd_left(d, kk, gq, eq_k_gq, g_n, dvd_kk_gn);
                    // dvd_gq_gn : dvd (mul g q) (mul g n)
                    let dvd_q_n = dvd_cancel_left_of_pos(d, &p, g, q, n, one_le_g, dvd_gq_gn);

                    let dvd_q_n_ty = d.dvd(q, n);
                    let eq_gq_k_ty = d.eq(gq, kk);
                    let dvd_g_m_ty = d.dvd(g, m);
                    let inner_ty = d.const_app(logic.and, &[dvd_q_n_ty, eq_gq_k_ty]);
                    let inner_and = d.const_app(
                        logic.and_intro,
                        &[dvd_q_n_ty, eq_gq_k_ty, dvd_q_n, eq_gq_k],
                    );
                    let full_and =
                        d.const_app(logic.and_intro, &[dvd_g_m_ty, inner_ty, dvd_g_m, inner_and]);
                    split_exists_intro(d, m, n, kk, g, q, full_and)
                });
                d.lam_fv(h_fv, dvd_k_mn_ty, result)
            },
        );

        let proof = d.const_app(logic.iff_intro, &[dvd_k_mn, exists_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}
