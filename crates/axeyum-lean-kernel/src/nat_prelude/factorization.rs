//! `Nat.prodRange` and the existence half of the Fundamental Theorem of
//! Arithmetic: every `n ≥ 2` is the product of primes named by a function
//! `f : Nat → Nat` on `[0, k)`.
//!
//! ## Why this shape and not "the multiset of prime factors"
//!
//! This kernel has no `List`, `Finset`, or product type, so "the multiset of
//! prime factors" is not expressible. The statement here is the honest
//! substitute: `∃ k f, (∀ i < k, Prime (f i)) ∧ prodRange f k = n`. Primality
//! is spelled inline (`Le two x ∧ ∀ c, dvd c x → c = 1 ∨ c = x`), matching
//! [`super::NatPrelude::exists_prime_dvd`]'s own convention — this prelude
//! has no `Prime` predicate.
//!
//! Uniqueness needs multiset equality of the factor list, which needs a type
//! this kernel does not have, and is **not attempted here**.
//!
//! ## The proof: well-founded induction, not `Nat.rec`
//!
//! `n`'s least prime divisor `p` (`exists_prime_dvd`) either equals `n` — `n`
//! is prime, `k := 1` — or is a proper divisor, `n = p * q` with
//! `2 ≤ q < n`. The induction hypothesis (over `Nat.lt`, via the generic
//! `WellFounded.fix` already used by `Nat.gcd`) supplies a factorization of
//! `q`, which is extended by **prepending** `p`: the prepended function is
//! built with a raw `Nat.rec` "cons" (`fun i => Nat.rec p (fun j _ => f' j)
//! i`), so `cons p f'` unfolds to `p` at `0` and to `f' j` at `succ j` purely
//! definitionally — no congruence lemma over the primality side is needed.
//! The `prodRange` side still needs one genuine induction (`prodRange (cons p
//! f') (succ k') = p * prodRange f' k'`), proved inline by ordinary
//! induction on `k'` from `mul_assoc`.
//!
//! Every helper below hoists each sub-expression into its own `let` before
//! passing it to a `NatOps` method: `d.foo(a, d.bar(b))` does not borrow-check
//! (`&mut NatDev` cannot be reborrowed twice in one call), so nothing here
//! nests a `d.`-method call inside another one's argument list.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use super::steps::or_cases;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// The two conjuncts of primality, spelled inline: `Le two x` and
/// `∀ c, dvd c x → Eq c one ∨ Eq c x`. Kept separate so callers can
/// `and_left`/`and_right` a `PrimeCond x` proof without rebuilding the whole
/// `And` type by hand.
fn prime_cond_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let triv = d.eq(c, one);
    let whole = d.eq(c, x);
    let disj = d.const_app(p.logic.or, &[triv, whole]);
    let body = d.arrow(hyp, disj);
    let divisors = d.pi_fv(c_fv, nat, body);
    (lower, divisors)
}

/// `Le two x ∧ ∀ c, dvd c x → Eq c one ∨ Eq c x` — primality, matching
/// `exists_prime_dvd`'s own inline convention.
fn prime_cond(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (lower, divisors) = prime_cond_parts(d, p, x);
    d.const_app(p.logic.and, &[lower, divisors])
}

/// `∀ i, Lt i k → PrimeCond (f i)`.
fn all_prime_below(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let lt_ty = d.lt(i, k);
    let fi = d.apply(f, &[i]);
    let prime_fi = prime_cond(d, p, fi);
    let body = d.arrow(lt_ty, prime_fi);
    d.pi_fv(i_fv, nat, body)
}

/// `(∀ i, Lt i k → PrimeCond (f i)) ∧ Eq (prodRange f k) n`.
fn factorization_body(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    n: ExprId,
) -> ExprId {
    let all = all_prime_below(d, p, f, k);
    let pr = d.const_app(p.prod_range, &[f, k]);
    let eqn = d.eq(pr, n);
    d.const_app(p.logic.and, &[all, eqn])
}

/// `fun f => factorization_body f k n` — the predicate for `∃ f, …`.
fn body_pred(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let body = factorization_body(d, p, f, k, n);
    d.lam_fv(f_fv, fn_ty, body)
}

/// `∃ f : Nat → Nat, factorization_body f k n`.
fn exists_f(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let pred = body_pred(d, p, k, n);
    let one = d.level_one();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[fn_ty, pred])
}

/// `fun k => exists_f k n` — the predicate for the outer `∃ k, …`.
fn k_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = exists_f(d, p, k, n);
    d.lam_fv(k_fv, nat, body)
}

/// `∃ k, ∃ f, (∀ i, Lt i k → PrimeCond (f i)) ∧ Eq (prodRange f k) n`.
fn factorization_exists(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let pred = k_pred(d, p, n);
    let one = d.level_one();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Le two n → factorization_exists n` — the `WellFounded.fix` family, valued
/// at a single `n`.
fn family_body(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let two = d.num(2);
    let hn_ty = d.le(two, n);
    let concl = factorization_exists(d, p, n);
    d.arrow(hn_ty, concl)
}

/// `False.rec` into `target` from a proof of `False`.
fn from_false(d: &mut NatDev<'_>, p: &NatPrelude, false_proof: ExprId, target: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `fun i => Nat.rec head (fun j _ => tail j) i` — `head` at `0`, `tail j` at
/// `succ j`, both purely definitional (`Nat.rec`'s own β/ι reduction), so no
/// congruence lemma is needed to compute this function at a concrete index.
fn cons_fn(d: &mut NatDev<'_>, p: &NatPrelude, head: ExprId, tail: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = head;
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let body = d.apply(tail, &[j]);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let one = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, i]);
    d.lam_fv(i_fv, nat, body)
}

/// From `heq : Eq n (mul pw q)`, `hlt : Lt pw n`, `hq1 : Le one q`, derive
/// `Le two q`.
///
/// `q ≥ 1` splits (`two_le_succ_or_eq_one`, after `le_dest` exposes `q` as
/// `succ kk`) into `q ≥ 2` (done) or `q = 1`, which forces `n = pw`
/// (`mul_one`), contradicting `pw < n` via `lt_irrefl`.
#[allow(clippy::too_many_arguments)]
fn derive_two_le_q(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pw: ExprId,
    n: ExprId,
    q: ExprId,
    heq: ExprId,
    hlt: ExprId,
    hq1: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one_v = d.num(1);
    let two = d.num(2);
    let goal = d.le(two, q);
    let one_lvl = d.level_one();

    let dest = d.lemma(p.le_dest, &[one_v, q, hq1]);
    let pred_kk = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let one_kk = d.add(one_v, kk);
        let eqn = d.eq(one_kk, q);
        d.lam_fv(kk_fv, nat, eqn)
    };
    let motive_kk = {
        let h_fv = d.fresh_fvar();
        let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
        let ex_ty = d.apply(ex_const, &[nat, pred_kk]);
        d.lam_fv(h_fv, ex_ty, goal)
    };
    let minor_kk = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let one_kk = d.add(one_v, kk);
        let hk_ty = d.eq(one_kk, q);

        let zero_v = d.zero();
        let sa = d.lemma(p.succ_add, &[zero_v, kk]);
        let za = d.lemma(p.zero_add, &[kk]);
        let zero_kk = d.add(zero_v, kk);
        let succ_kk = d.succ(kk);
        let cong = d.congr(zero_kk, kk, za, &|d, x| d.succ(x));
        let succ_zero_kk = d.succ(zero_kk);
        let add_one_kk_eq_succ_kk = d.trans(one_kk, succ_zero_kk, succ_kk, sa, cong);
        let symm_add_one_kk = d.symm(one_kk, succ_kk, add_one_kk_eq_succ_kk);
        let succ_kk_eq_q = d.trans(succ_kk, one_kk, q, symm_add_one_kk, hk);

        let tw = d.lemma(p.two_le_succ_or_eq_one, &[kk]);
        let left_ty2 = d.le(two, succ_kk);
        let right_ty2 = d.eq(succ_kk, one_v);

        let left_minor2 = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive2 = d.eq_motive(succ_kk, &|d, x| {
                let two_e = d.num(2);
                d.le(two_e, x)
            });
            let res = d.transport(succ_kk, motive2, h, q, succ_kk_eq_q);
            d.lam_fv(h_fv, left_ty2, res)
        };
        let right_minor2 = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let symm_succ_kk_eq_q = d.symm(succ_kk, q, succ_kk_eq_q);
            let q_eq_one = d.trans(q, succ_kk, one_v, symm_succ_kk_eq_q, h);
            let motive3 = d.eq_motive(q, &|d, x| {
                let pwx = d.mul(pw, x);
                d.eq(n, pwx)
            });
            let heq_one = d.transport(q, motive3, heq, one_v, q_eq_one);
            let mul_one_pw = d.lemma(p.mul_one, &[pw]);
            let pw_one = d.mul(pw, one_v);
            let n_eq_pw = d.trans(n, pw_one, pw, heq_one, mul_one_pw);
            let motive4 = d.eq_motive(n, &|d, x| d.lt(pw, x));
            let hltpp = d.transport(n, motive4, hlt, pw, n_eq_pw);
            let false_proof = d.lemma(p.lt_irrefl, &[pw, hltpp]);
            let ex_falso = from_false(d, p, false_proof, goal);
            d.lam_fv(h_fv, right_ty2, ex_falso)
        };
        let or_result = or_cases(d, left_ty2, right_ty2, goal, left_minor2, right_minor2, tw);
        let inner = d.lam_fv(hk_fv, hk_ty, or_result);
        d.lam_fv(kk_fv, nat, inner)
    };
    let exists_rec_kk = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
    d.apply(exists_rec_kk, &[nat, pred_kk, motive_kk, minor_kk, dest])
}

/// From `heq : Eq n (mul pw q)`, `hp2 : Le two pw`, `hq1 : Le one q`, derive
/// `Lt q n`.
///
/// `pw ≥ 2` gives `2*q ≤ pw*q = n` (`mul_le_mul_left` + `mul_comm`), and
/// `2*q = q+q ≥ q+1 = succ q` since `q ≥ 1` (`add_le_add_left`; `q+1 ≡ succ
/// q` is definitional), so `succ q ≤ n`.
#[allow(clippy::too_many_arguments)]
fn derive_q_lt_n(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pw: ExprId,
    n: ExprId,
    q: ExprId,
    heq: ExprId,
    hp2: ExprId,
    hq1: ExprId,
) -> ExprId {
    let one_v = d.num(1);
    let two = d.num(2);

    let step_a = d.lemma(p.mul_le_mul_left, &[q, two, pw, hp2]);
    let mc1 = d.lemma(p.mul_comm, &[q, two]);
    let mc2 = d.lemma(p.mul_comm, &[q, pw]);

    let q_two = d.mul(q, two);
    let q_pw = d.mul(q, pw);
    let two_q = d.mul(two, q);
    let pw_q = d.mul(pw, q);

    let motive_l = d.eq_motive(q_two, &|d, x| d.le(x, q_pw));
    let step_b = d.transport(q_two, motive_l, step_a, two_q, mc1);

    let motive_r = d.eq_motive(q_pw, &|d, x| d.le(two_q, x));
    let step_c = d.transport(q_pw, motive_r, step_b, pw_q, mc2);

    let heq_sym = d.symm(n, pw_q, heq);
    let motive_n = d.eq_motive(pw_q, &|d, x| d.le(two_q, x));
    let step_d = d.transport(pw_q, motive_n, step_c, n, heq_sym);

    let sm = d.lemma(p.succ_mul, &[one_v, q]);
    let one_mul_q = d.lemma(p.one_mul, &[q]);
    let one_q = d.mul(one_v, q);
    let cong_add = d.congr(one_q, q, one_mul_q, &|d, x| d.add(x, q));
    let add_one_q_q = d.add(one_q, q);
    let q_q = d.add(q, q);
    let two_q_eq_add_qq = d.trans(two_q, add_one_q_q, q_q, sm, cong_add);

    let motive_e = d.eq_motive(two_q, &|d, x| d.le(x, n));
    let step_e = d.transport(two_q, motive_e, step_d, q_q, two_q_eq_add_qq);

    let al = d.lemma(p.add_le_add_left, &[q, one_v, q, hq1]);
    let succ_q = d.succ(q);
    d.lemma(p.le_trans, &[succ_q, q_q, n, al, step_e])
}

/// The `WellFounded.fix` step body: given `n`, the induction hypothesis `ih`
/// for every `m < n`, and (once applied) `hn : Le two n`, produce a proof of
/// `factorization_exists n`.
fn build_step_body(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, ih: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one_v = d.num(1);
    let one_lvl = d.level_one();
    let hn_ty = d.le(two, n);
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);
    let goal = factorization_exists(d, p, n);

    let hp_outer = d.lemma(p.exists_prime_dvd, &[n, hn]);
    let pred_outer = {
        let pw_fv = d.fresh_fvar();
        let pw = d.kernel().fvar(pw_fv);
        let prime_pw = prime_cond(d, p, pw);
        let dvd_pw_n = d.dvd(pw, n);
        let conj = d.const_app(p.logic.and, &[prime_pw, dvd_pw_n]);
        d.lam_fv(pw_fv, nat, conj)
    };
    let motive_outer = {
        let h_fv = d.fresh_fvar();
        let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
        let ex_ty = d.apply(ex_const, &[nat, pred_outer]);
        d.lam_fv(h_fv, ex_ty, goal)
    };
    let minor_outer = {
        let pw_fv = d.fresh_fvar();
        let pw = d.kernel().fvar(pw_fv);
        let hpand_fv = d.fresh_fvar();
        let hpand = d.kernel().fvar(hpand_fv);
        let (prime_lower_ty, prime_div_ty) = prime_cond_parts(d, p, pw);
        let prime_pw = d.const_app(p.logic.and, &[prime_lower_ty, prime_div_ty]);
        let dvd_pw_n = d.dvd(pw, n);
        let hpand_ty = d.const_app(p.logic.and, &[prime_pw, dvd_pw_n]);

        let hprime = and_left(d, prime_pw, dvd_pw_n, hpand);
        let hdvd = and_right(d, prime_pw, dvd_pw_n, hpand);
        let hp2 = and_left(d, prime_lower_ty, prime_div_ty, hprime);

        let le_refl_one = d.lemma(p.le_refl, &[one_v]);
        let le_one_two = d.lemma(p.le_step, &[one_v, one_v, le_refl_one]);
        let h1n = d.lemma(p.le_trans, &[one_v, two, n, le_one_two, hn]);

        let hple = d.lemma(p.le_of_dvd, &[pw, n, h1n, hdvd]);
        let hcase = d.lemma(p.lt_or_eq_of_le, &[pw, n, hple]);

        let lt_ty = d.lt(pw, n);
        let eq_ty = d.eq(pw, n);

        // ---- CASE A: pw = n, n itself is prime ----
        let right_minor = {
            let hpn_fv = d.fresh_fvar();
            let hpn = d.kernel().fvar(hpn_fv);
            let motive = d.eq_motive(pw, &|d, x| prime_cond(d, p, x));
            let hprime_n = d.transport(pw, motive, hprime, n, hpn);

            let k1 = d.num(1);
            let f_const = {
                let z_fv = d.fresh_fvar();
                d.lam_fv(z_fv, nat, n)
            };
            let hall1 = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let lt1 = d.lt(i, k1);
                let hi_fv = d.fresh_fvar();
                let inner = d.lam_fv(hi_fv, lt1, hprime_n);
                d.lam_fv(i_fv, nat, inner)
            };
            let heq1 = d.lemma(p.one_mul, &[n]);

            let all_ty = all_prime_below(d, p, f_const, k1);
            let pr1 = d.const_app(p.prod_range, &[f_const, k1]);
            let eq_ty1 = d.eq(pr1, n);
            let body_and = d.const_app(p.logic.and_intro, &[all_ty, eq_ty1, hall1, heq1]);

            let pred_f1 = body_pred(d, p, k1, n);
            let fn_ty = d.arrow(nat, nat);
            let exists_intro_f = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
            let inner_ex = d.apply(exists_intro_f, &[fn_ty, pred_f1, f_const, body_and]);

            let pred_k = k_pred(d, p, n);
            let exists_intro_k = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
            let outer_ex = d.apply(exists_intro_k, &[nat, pred_k, k1, inner_ex]);

            d.lam_fv(hpn_fv, eq_ty, outer_ex)
        };

        // ---- CASE B: pw < n, n = pw * q for a proper cofactor q ----
        let left_minor = {
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);

            let pred_q = d.dvd_predicate(pw, n);
            let motive_q = {
                let h_fv = d.fresh_fvar();
                let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                let ex_ty = d.apply(ex_const, &[nat, pred_q]);
                d.lam_fv(h_fv, ex_ty, goal)
            };
            let minor_q = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let pw_q = d.mul(pw, q);
                let heq_ty = d.eq(n, pw_q);

                let motive_le = d.eq_motive(n, &|d, x| d.le(two, x));
                let hn_mul = d.transport(n, motive_le, hn, pw_q, heq);
                let le_refl_one2 = d.lemma(p.le_refl, &[one_v]);
                let le_one_two2 = d.lemma(p.le_step, &[one_v, one_v, le_refl_one2]);
                let h1_mul = d.lemma(p.le_trans, &[one_v, two, pw_q, le_one_two2, hn_mul]);
                let hq1 = d.lemma(p.one_le_right_of_mul, &[pw, q, h1_mul]);

                let hq2 = derive_two_le_q(d, p, pw, n, q, heq, hlt, hq1);
                let hqn = derive_q_lt_n(d, p, pw, n, q, heq, hp2, hq1);

                let ih_q = d.apply(ih, &[q, hqn]);
                let fact_q = d.apply(ih_q, &[hq2]);

                let pred_k2 = k_pred(d, p, q);
                let motive_k2 = {
                    let h_fv = d.fresh_fvar();
                    let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                    let ex_ty = d.apply(ex_const, &[nat, pred_k2]);
                    d.lam_fv(h_fv, ex_ty, goal)
                };
                let minor_k2 = {
                    let kp_fv = d.fresh_fvar();
                    let kp = d.kernel().fvar(kp_fv);
                    let hf_fv = d.fresh_fvar();
                    let hf = d.kernel().fvar(hf_fv);
                    let ex_f2_ty = exists_f(d, p, kp, q);

                    let fn_ty = d.arrow(nat, nat);
                    let pred_f2 = body_pred(d, p, kp, q);
                    let motive_f2 = {
                        let h_fv = d.fresh_fvar();
                        let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                        let ex_ty = d.apply(ex_const, &[fn_ty, pred_f2]);
                        d.lam_fv(h_fv, ex_ty, goal)
                    };
                    let minor_f2 = {
                        let fp_fv = d.fresh_fvar();
                        let fp = d.kernel().fvar(fp_fv);
                        let hb_fv = d.fresh_fvar();
                        let hb = d.kernel().fvar(hb_fv);
                        let hb_ty = factorization_body(d, p, fp, kp, q);

                        let all_ty2 = all_prime_below(d, p, fp, kp);
                        let pr2 = d.const_app(p.prod_range, &[fp, kp]);
                        let eq_ty2 = d.eq(pr2, q);
                        let hall_p = and_left(d, all_ty2, eq_ty2, hb);
                        let heq_p = and_right(d, all_ty2, eq_ty2, hb);

                        let cons_f = cons_fn(d, p, pw, fp);
                        let k_new = d.succ(kp);

                        let hall_new = {
                            let motive_fn = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                                let lt_ty = d.lt(x, k_new);
                                let fx = d.apply(cons_f, &[x]);
                                let prime_fx = prime_cond(d, p, fx);
                                d.arrow(lt_ty, prime_fx)
                            };
                            let base_fn = |d: &mut NatDev<'_>| -> ExprId {
                                let zero_v = d.zero();
                                let lt_ty = d.lt(zero_v, k_new);
                                let hyp_fv = d.fresh_fvar();
                                d.lam_fv(hyp_fv, lt_ty, hprime)
                            };
                            let step_fn = |d: &mut NatDev<'_>, j: ExprId, _ih2: ExprId| -> ExprId {
                                let sj = d.succ(j);
                                let lt_ty = d.lt(sj, k_new);
                                let hyp_fv = d.fresh_fvar();
                                let hyp = d.kernel().fvar(hyp_fv);
                                let lt_j_kp = d.lemma(p.le_of_succ_le_succ, &[sj, kp, hyp]);
                                let result = d.apply(hall_p, &[j, lt_j_kp]);
                                d.lam_fv(hyp_fv, lt_ty, result)
                            };
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let induct_body = d.induct(&motive_fn, &base_fn, &step_fn, i);
                            d.lam_fv(i_fv, nat, induct_body)
                        };

                        let heq_new = {
                            let motive_l = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                                let sx = d.succ(x);
                                let lhs = d.const_app(p.prod_range, &[cons_f, sx]);
                                let rhs_inner = d.const_app(p.prod_range, &[fp, x]);
                                let rhs = d.mul(pw, rhs_inner);
                                d.eq(lhs, rhs)
                            };
                            let base_l = |d: &mut NatDev<'_>| -> ExprId {
                                let one_e = d.num(1);
                                let lhs2 = d.mul(one_e, pw);
                                let rhs2 = d.mul(pw, one_e);
                                let h1 = d.lemma(p.one_mul, &[pw]);
                                let h2 = d.lemma(p.mul_one, &[pw]);
                                let h2s = d.symm(rhs2, pw, h2);
                                d.trans(lhs2, pw, rhs2, h1, h2s)
                            };
                            let step_l = |d: &mut NatDev<'_>, j: ExprId, ih_l: ExprId| -> ExprId {
                                let sj = d.succ(j);
                                let prod_cf_sj = d.const_app(p.prod_range, &[cons_f, sj]);
                                let fpj = d.apply(fp, &[j]);
                                let pr_fp_j = d.const_app(p.prod_range, &[fp, j]);
                                let pw_pr_fp_j = d.mul(pw, pr_fp_j);
                                let step1 =
                                    d.congr(prod_cf_sj, pw_pr_fp_j, ih_l, &|d, x| d.mul(x, fpj));
                                let step2 = d.lemma(p.mul_assoc, &[pw, pr_fp_j, fpj]);
                                let lhs_full = d.mul(prod_cf_sj, fpj);
                                let mid = d.mul(pw_pr_fp_j, fpj);
                                let fp_j_fpj = d.mul(pr_fp_j, fpj);
                                let rhs_full = d.mul(pw, fp_j_fpj);
                                d.trans(lhs_full, mid, rhs_full, step1, step2)
                            };
                            let lemma_l = d.induct(&motive_l, &base_l, &step_l, kp);
                            let pr_fp_kp = d.const_app(p.prod_range, &[fp, kp]);
                            let step_eq = d.congr(pr_fp_kp, q, heq_p, &|d, x| d.mul(pw, x));
                            let pr_cf_knew = d.const_app(p.prod_range, &[cons_f, k_new]);
                            let pw_pr_fp_kp = d.mul(pw, pr_fp_kp);
                            let pw_q = d.mul(pw, q);
                            let combined = d.trans(pr_cf_knew, pw_pr_fp_kp, pw_q, lemma_l, step_eq);
                            let heq_sym2 = d.symm(n, pw_q, heq);
                            d.trans(pr_cf_knew, pw_q, n, combined, heq_sym2)
                        };

                        let all_new = all_prime_below(d, p, cons_f, k_new);
                        let pr_cf_knew2 = d.const_app(p.prod_range, &[cons_f, k_new]);
                        let eq_new = d.eq(pr_cf_knew2, n);
                        let and_new =
                            d.const_app(p.logic.and_intro, &[all_new, eq_new, hall_new, heq_new]);

                        let fn_ty2 = d.arrow(nat, nat);
                        let pred_f_new = body_pred(d, p, k_new, n);
                        let exists_intro_fnew =
                            d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
                        let inner_ex2 =
                            d.apply(exists_intro_fnew, &[fn_ty2, pred_f_new, cons_f, and_new]);

                        let pred_k_new = k_pred(d, p, n);
                        let exists_intro_knew =
                            d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
                        let outer_ex2 =
                            d.apply(exists_intro_knew, &[nat, pred_k_new, k_new, inner_ex2]);

                        let inner_hb = d.lam_fv(hb_fv, hb_ty, outer_ex2);
                        d.lam_fv(fp_fv, fn_ty, inner_hb)
                    };
                    let exists_rec_f2 = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                    let body_f2 =
                        d.apply(exists_rec_f2, &[fn_ty, pred_f2, motive_f2, minor_f2, hf]);
                    let inner_f2 = d.lam_fv(hf_fv, ex_f2_ty, body_f2);
                    d.lam_fv(kp_fv, nat, inner_f2)
                };
                let exists_rec_k2 = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                let body_k2 = d.apply(exists_rec_k2, &[nat, pred_k2, motive_k2, minor_k2, fact_q]);
                let inner_k2 = d.lam_fv(heq_fv, heq_ty, body_k2);
                d.lam_fv(q_fv, nat, inner_k2)
            };
            let exists_rec_q = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
            let body_dvd = d.apply(exists_rec_q, &[nat, pred_q, motive_q, minor_q, hdvd]);
            d.lam_fv(hlt_fv, lt_ty, body_dvd)
        };

        let or_result_outer = or_cases(d, lt_ty, eq_ty, goal, left_minor, right_minor, hcase);
        let inner_outer = d.lam_fv(hpand_fv, hpand_ty, or_result_outer);
        d.lam_fv(pw_fv, nat, inner_outer)
    };
    let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
    let proof_of_goal = d.apply(
        exists_rec_outer,
        &[nat, pred_outer, motive_outer, minor_outer, hp_outer],
    );
    d.lam_fv(hn_fv, hn_ty, proof_of_goal)
}

/// `Nat.prodRange f zero ≡ one`, `Nat.prodRange f (succ n) ≡ mul (prodRange
/// f n) (f n)` — structural recursion on the bound, mirroring
/// [`super::defs::declare_finite_ranges`]'s `sumRange`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.num(1);
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.mul(ih, fj);
        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.prod_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;

    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let one_v = d.num(1);
        let lhs = d.const_app(p.prod_range, &[f, zero]);
        let stmt = d.eq(lhs, one_v);
        let proof = d.refl(one_v);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        d.declare_theorem(p.prod_range_zero, ty, value)?;
    }
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.prod_range, &[f, sn]);
        let prior = d.const_app(p.prod_range, &[f, n]);
        let fj = d.apply(f, &[n]);
        let rhs = d.mul(prior, fj);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        d.declare_theorem(p.prod_range_succ, ty, value)?;
    }
    Ok(())
}

/// `Nat.exists_prime_factorization : ∀ n, Le two n → ∃ k f, (∀ i, Lt i k →
/// PrimeCond (f i)) ∧ Eq (prodRange f k) n` — the existence half of the
/// Fundamental Theorem of Arithmetic, by well-founded induction on `Nat.lt`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_exists_prime_factorization(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let zero_lvl = d.kernel().level_zero();

    let relation = d.kernel().const_(p.lt, vec![]);
    let family = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = family_body(d, &p, n);
        d.lam_fv(n_fv, nat, body)
    };
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    let step = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let ih_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let lt_ty = d.lt(y, x);
            let family_y = family_body(d, &p, y);
            let inner = d.arrow(lt_ty, family_y);
            d.pi_fv(y_fv, nat, inner)
        };
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = build_step_body(d, &p, x, ih);
        let with_ih = d.lam_fv(ih_fv, ih_ty, body);
        d.lam_fv(x_fv, nat, with_ih)
    };
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one_lvl, zero_lvl]);
    let value = d.apply(fix, &[nat, relation, family, well_founded, step]);

    let stmt = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = family_body(d, &p, n);
        d.pi_fv(n_fv, nat, body)
    };
    d.declare_theorem(p.exists_prime_factorization, stmt, value)?;
    Ok(())
}
