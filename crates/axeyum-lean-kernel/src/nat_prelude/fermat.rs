//! Fermat's little theorem over ℕ, via the Frobenius / "freshman's dream" route.
//!
//! [`declare_add_pow_modeq_prime`] is the Frobenius identity
//! `(a+b)^p ≡ a^p+b^p [p]` for prime `p`, proved from the binomial theorem
//! (`Nat.add_pow`, [`super::binomial`]) plus `Nat.prime_dvd_choose`
//! ([`super::bezout`]): every interior term of the expansion (`0 < k < p`)
//! carries a factor of `p ∣ choose p k`, so the interior sum vanishes mod `p`,
//! leaving only the two boundary terms `a^p` and `b^p`.
//! [`declare_pow_prime_modeq_self`] is Fermat's little theorem itself,
//! `a^p ≡ a [p]`, by induction on `a` using the Frobenius identity at `b = 1`
//! for the successor step.
//!
//! Both proofs need `p`'s sum bound in `succ`-of-something form (to peel a
//! `sumRange`'s back term, or to reduce `pow` at a successor exponent), but
//! `p` itself is only a free variable. [`pos_implies_succ_pred`] bridges that:
//! from `0 < p` (itself extracted from primality by [`prime_pos`]) it produces
//! `Eq p (succ (pred p))`, so the bulk of each proof is built entirely in
//! terms of `n := succ (pred p)` — syntactically a successor — and
//! transported back to `p` only at the very end.

use super::NatPrelude;
use super::binomial::{binom_term, binom_term_fn, binom_term_zero_eq_pow_b};
use super::helpers::and_left;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Small shared combinators. `ex_falso` and `shifted_fn` are local copies of
// private helpers in [`super::binomial`] (that module's own convention: see
// its `ex_falso`, "a local copy of `order_more::ex_falso`").
// ============================================================================

/// `False.rec (fun _ => target) false_proof : target`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `fun k => f (succ k)`.
fn shifted_fn(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let body = d.apply(f, &[sk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `2 ≤ x`, `∀ c, c ∣ x → c = 1 ∨ c = x` — the two conjuncts of primality,
/// spelled exactly as `Nat.prime_dvd_choose`'s own hypothesis (`bezout.rs`),
/// so a proof of [`prime_ty`] type-checks directly as that theorem's first
/// argument.
fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let two_le = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let is_one = d.eq(c, one);
    let is_x = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[is_one, is_x]);
    let inner = d.arrow(hyp, disjunction);
    let divisor_clause = d.pi_fv(c_fv, nat, inner);
    (two_le, divisor_clause)
}

/// `(2 ≤ x) ∧ (∀ c, c ∣ x → c = 1 ∨ c = x)`.
fn prime_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (two_le, divisor_clause) = prime_parts(d, p, x);
    d.const_app(p.logic.and, &[two_le, divisor_clause])
}

/// `prime x → Lt zero x`: extract `2 ≤ x` from the packed proof, then weaken
/// via `le_succ` (`1 ≤ 2`) and `le_trans`.
fn prime_pos(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, prime_proof: ExprId) -> ExprId {
    let (two_le_ty, divisor_clause_ty) = prime_parts(d, p, x);
    let two_le = and_left(d, two_le_ty, divisor_clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    d.lemma(p.le_trans, &[one, two, x, one_le_two, two_le])
}

/// `Lt zero n → Eq n (succ (pred n))`, by induction on `n`: the base case is
/// impossible (`not_lt_zero`); the successor case is `refl`, since
/// `pred (succ m)` reduces to `m` definitionally. Returns the arrow-typed
/// proof (apply it to a positivity witness to get the equation).
fn pos_implies_succ_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let zero = d.zero();
        let hyp = d.lt(zero, x);
        let px = d.pred(x);
        let spx = d.succ(px);
        let concl = d.eq(x, spx);
        d.arrow(hyp, concl)
    };
    d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = d.lt(zero, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let pz = d.pred(zero);
            let spz = d.succ(pz);
            let target_ty = d.eq(zero, spz);
            let not_lt = d.lemma(p.not_lt_zero, &[zero]);
            let false_proof = d.apply(not_lt, &[hyp]);
            let body = ex_falso(d, p, target_ty, false_proof);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d, m, _ih| {
            let sm = d.succ(m);
            let zero = d.zero();
            let hyp_ty = d.lt(zero, sm);
            let hyp_fv = d.fresh_fvar();
            let _hyp = d.kernel().fvar(hyp_fv);
            let body = d.refl(sm);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        n,
    )
}

/// `Eq a b → modEq d a b`, via `mod_eq_refl` transported along the equality.
fn eq_to_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    a: ExprId,
    b: ExprId,
    eq_ab: ExprId,
) -> ExprId {
    let refl_case = d.lemma(p.mod_eq_refl, &[modulus, a]);
    let motive = d.eq_motive(a, &|d, x| d.mod_eq(modulus, a, x));
    d.transport(a, motive, refl_case, b, eq_ab)
}

/// `binom_term a b row row = pow a row` — the back-boundary term of the
/// binomial expansion (the `k = row` term is exactly `a^row`), the mirror of
/// [`binom_term_zero_eq_pow_b`]'s front boundary.
fn binom_term_row_eq_pow_a(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    row: ExprId,
) -> ExprId {
    let start = binom_term(d, a, b, row, row);
    let c_rr = d.choose(row, row);
    let a_pow = d.pow(a, row);
    let sub_rr = d.sub(row, row);
    let b_pow = d.pow(b, sub_rr);

    let h_c = d.lemma(p.choose_self, &[row]);
    let one = d.num(1);
    let one_a = d.mul(one, a_pow);
    let mid1 = d.mul(one_a, b_pow);
    let h1 = d.congr(c_rr, one, h_c, &|d, t| {
        let ta = d.mul(t, a_pow);
        d.mul(ta, b_pow)
    });

    let h2v = d.lemma(p.one_mul, &[a_pow]);
    let mid2 = d.mul(a_pow, b_pow);
    let h2 = d.congr(one_a, a_pow, h2v, &|d, t| d.mul(t, b_pow));

    let h_sub = d.lemma(p.sub_self, &[row]);
    let zero = d.zero();
    let b_pow_zero = d.pow(b, zero);
    let mid3 = d.mul(a_pow, b_pow_zero);
    let h3 = d.congr(sub_rr, zero, h_sub, &|d, t| {
        let bp = d.pow(b, t);
        d.mul(a_pow, bp)
    });

    let mid4 = d.mul(a_pow, one);
    let h_defeq = d.refl(mid3);
    let h4 = d.lemma(p.mul_one, &[a_pow]);

    let (_e, proof) = d.chain(
        start,
        &[
            (mid1, h1),
            (mid2, h2),
            (mid3, h3),
            (mid4, h_defeq),
            (a_pow, h4),
        ],
    );
    proof
}

/// `prime row → 0 < k → k < row → dvd row (binom_term a b row k)`: every
/// interior term of the binomial expansion at `row` carries a factor of
/// `row ∣ choose row k`.
#[allow(clippy::too_many_arguments)]
fn interior_term_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    row: ExprId,
    k: ExprId,
    hk_pos: ExprId,
    hk_lt: ExprId,
    prime_proof: ExprId,
) -> ExprId {
    let choose_dvd = d.lemma(p.prime_dvd_choose, &[row, k, prime_proof, hk_pos, hk_lt]);
    let ak = d.pow(a, k);
    let c = d.choose(row, k);
    let c_ak = d.mul(c, ak);
    let step1 = d.lemma(p.dvd_mul_right_of_dvd, &[row, c, ak, choose_dvd]);
    let sub_rk = d.sub(row, k);
    let bpow = d.pow(b, sub_rk);
    d.lemma(p.dvd_mul_right_of_dvd, &[row, c_ak, bpow, step1])
}

// ============================================================================
// Step 1: `Nat.modEq_pow`.
// ============================================================================

/// `Nat.modEq_pow : ∀ d a b k, modEq d a b → modEq d (pow a k) (pow b k)`.
///
/// Induction on `k`: at `zero` both sides are `1` regardless of `a`/`b`
/// (`mod_eq_refl`); at `succ j`, `pow _ (succ j)` computes to `mul (pow _ j) _`
/// definitionally, so `mod_eq_mul` applied to the IH and the outer hypothesis
/// gives exactly the goal — no explicit `pow_succ` rewrite needed. Mirrors
/// `Int.ModEq.pow` (`int_prelude/modeq.rs`), minus the positivity hypothesis
/// `mod_eq_mul` doesn't need over ℕ.
pub(super) fn declare_mod_eq_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_pow, 4, &|d, v| {
        let (modulus, a, b, k) = (v[0], v[1], v[2], v[3]);
        let hyp_ty = d.mod_eq(modulus, a, b);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let pa = d.pow(a, x);
            let pb = d.pow(b, x);
            d.mod_eq(modulus, pa, pb)
        };
        let target = motive(d, k);

        let body = d.induct(
            &motive,
            &|d| {
                let one = d.num(1);
                d.lemma(p.mod_eq_refl, &[modulus, one])
            },
            &|d, j, ih| {
                let pa_j = d.pow(a, j);
                let pb_j = d.pow(b, j);
                d.lemma(p.mod_eq_mul, &[modulus, pa_j, pb_j, a, b, ih, hyp])
            },
            k,
        );
        let stmt = d.arrow(hyp_ty, target);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Step 2: a generic "divisible term-by-term implies divisible sum" lemma.
// ============================================================================

/// `Nat.dvd_sum_range_of_forall_lt :
///   ∀ d f n, (∀ k, Lt k n → dvd d (f k)) → dvd d (sumRange f n)`.
///
/// Induction on `n`: at `zero`, `sumRange f zero` is `zero` definitionally, so
/// `dvd_zero` closes it; at `succ m`, `sumRange f (succ m)` is definitionally
/// `sumRange f m + f m`, and `dvd_add` combines the restricted hypothesis
/// (`Lt k m → Lt k (succ m)`, via `le_step`) applied through the IH with the
/// hypothesis at `k = m` (via `lt_succ_self`).
pub(super) fn declare_dvd_sum_range_of_forall_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let divisor_fv = d.fresh_fvar();
    let divisor = d.kernel().fvar(divisor_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hyp_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lt_ty = d.lt(k, x);
        let fk = d.apply(f, &[k]);
        let concl = d.dvd(divisor, fk);
        let body = d.arrow(lt_ty, concl);
        d.pi_fv(k_fv, nat, body)
    };
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let hyp = hyp_at(d, x);
        let sx = d.sum_range(f, x);
        let concl = d.dvd(divisor, sx);
        d.arrow(hyp, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = hyp_at(d, zero);
            let hyp_fv = d.fresh_fvar();
            let _hyp = d.kernel().fvar(hyp_fv);
            let body = d.lemma(p.dvd_zero, &[divisor]);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let hyp_ty = hyp_at(d, sm);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let restricted = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let lt_ty = d.lt(k, m);
                let lt_fv = d.fresh_fvar();
                let lt_h = d.kernel().fvar(lt_fv);
                let sk = d.succ(k);
                let lifted = d.lemma(p.le_step, &[sk, m, lt_h]);
                let applied = d.apply(hyp, &[k, lifted]);
                let with_lt = d.lam_fv(lt_fv, lt_ty, applied);
                d.lam_fv(k_fv, nat, with_lt)
            };
            let sum_dvd = d.apply(ih, &[restricted]);

            let lt_m_sm = d.lemma(p.lt_succ_self, &[m]);
            let term_dvd = d.apply(hyp, &[m, lt_m_sm]);

            let sum_range_fm = d.sum_range(f, m);
            let fm = d.apply(f, &[m]);
            let body = d.lemma(p.dvd_add, &[divisor, sum_range_fm, fm, sum_dvd, term_dvd]);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(divisor_fv, nat, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(divisor_fv, nat, over_f)
    };
    d.declare_theorem(p.dvd_sum_range_of_forall_lt, ty, value)
}

// ============================================================================
// Step 3 (HEADLINE): the Frobenius identity / "freshman's dream".
// ============================================================================

/// `Nat.add_pow_modeq_prime : prime p → (a+b)^p ≡ a^p + b^p [p]`.
///
/// Built entirely in terms of `n := succ (pred p)` (propositionally equal to
/// `p` given positivity, via [`pos_implies_succ_pred`]), so the peeling
/// lemmas below see a literal successor: `add_pow`'s sum is peeled at the
/// FRONT (`sum_range_shift_front`, term `0` = `b^n`) and the resulting tail,
/// with bound literally `n = succ (pred p)`, is peeled at the BACK by pure
/// definitional reduction of `sumRange` (term `n` = `a^n`,
/// [`binom_term_row_eq_pow_a`]). What remains — indices `1..pred p` — is the
/// interior, divisible by `n` term-by-term
/// ([`interior_term_dvd`]/`prime_dvd_choose`) and hence as a sum
/// (`dvd_sum_range_of_forall_lt`), so it is `≡ 0 [n]` and collapses out,
/// leaving `a^n + b^n`. The whole `n`-phrased result is transported back to
/// `p` at the very end.
pub(super) fn declare_add_pow_modeq_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.add_pow_modeq_prime, 3, &|d, v| {
        let (pp, a, b) = (v[0], v[1], v[2]);
        let prime_ty_pp = prime_ty(d, &p, pp);
        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        // n := succ (pred pp), propositionally equal to pp given positivity.
        let zero_lt_pp = prime_pos(d, &p, pp, prime_proof);
        let eq_pp_n_fn = pos_implies_succ_pred(d, &p, pp);
        let eq_pp_n = d.apply(eq_pp_n_fn, &[zero_lt_pp]);
        let m = d.pred(pp);
        let n = d.succ(m);
        let eq_n_pp = d.symm(pp, n, eq_pp_n);

        // Transport the prime hypothesis from `pp` to `n`.
        let transport_motive = d.eq_motive(pp, &|d, x| prime_ty(d, &p, x));
        let prime_proof_n = d.transport(pp, transport_motive, prime_proof, n, eq_pp_n);

        // The binomial expansion of `(a+b)^n`.
        let f = binom_term_fn(d, a, b, n);
        let sn = d.succ(n);
        let s = d.sum_range(f, sn);
        let shifted_f = shifted_fn(d, f);

        // Front boundary: term(0) = b^n.
        let zero = d.zero();
        let term0 = binom_term(d, a, b, n, zero);
        let pow_b_n = d.pow(b, n);
        let term0_eq_pow_b_n = binom_term_zero_eq_pow_b(d, &p, a, b, n);

        let h_shift = d.lemma(p.sum_range_shift_front, &[f, n]);
        let tail = d.sum_range(shifted_f, n);
        let peeled = d.add(term0, tail);

        let mid1 = d.add(pow_b_n, tail);
        let h1 = d.congr(term0, pow_b_n, term0_eq_pow_b_n, &|d, t| d.add(t, tail));

        // Splitting the tail: interior (k = 1..pred pp) plus the back
        // boundary term(n) = a^n, exposed by `tail`'s own definitional
        // reduction (`n` is syntactically `succ m`).
        let interior = d.sum_range(shifted_f, m);
        let last = d.apply(shifted_f, &[m]);
        let interior_plus_last = d.add(interior, last);
        let mid2 = d.add(pow_b_n, interior_plus_last);
        let tail_refl = d.refl(tail);
        let h2 = d.congr(tail, interior_plus_last, tail_refl, &|d, t| {
            d.add(pow_b_n, t)
        });

        let pow_a_n = d.pow(a, n);
        let last_eq_pow_a_n = binom_term_row_eq_pow_a(d, &p, a, b, n);
        let interior_plus_pow_a = d.add(interior, pow_a_n);
        let mid3 = d.add(pow_b_n, interior_plus_pow_a);
        let h3 = d.congr(last, pow_a_n, last_eq_pow_a_n, &|d, t| {
            let ip = d.add(interior, t);
            d.add(pow_b_n, ip)
        });

        let (_e, eq_s_expanded) =
            d.chain(s, &[(peeled, h_shift), (mid1, h1), (mid2, h2), (mid3, h3)]);

        // The interior sum is divisible by `n`: every term `1 ≤ k ≤ pred pp`
        // (i.e. `0 < k < n`) carries a factor of `n ∣ choose n k`.
        let forall_hyp = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hlt_ty = d.lt(j, m);
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);
            let sj = d.succ(j);
            let hpos_sj = d.zero_lt_succ(j);
            let hlt_sj_n = d.lemma(p.le_succ_succ, &[sj, m, hlt]);
            let term_dvd = interior_term_dvd(d, &p, a, b, n, sj, hpos_sj, hlt_sj_n, prime_proof_n);
            let with_hlt = d.lam_fv(hlt_fv, hlt_ty, term_dvd);
            d.lam_fv(j_fv, nat, with_hlt)
        };
        let dvd_n_interior = d.lemma(p.dvd_sum_range_of_forall_lt, &[n, shifted_f, m, forall_hyp]);
        let interior_modeq_zero = d.lemma(p.mod_eq_zero_of_dvd, &[n, interior, dvd_n_interior]);

        // Collapse:
        //   S ≡ b^n + (interior + a^n)
        //     ≡ b^n + (0 + a^n)
        //     ≡ b^n + a^n
        //     ≡ a^n + b^n  [n]
        let step_a = d.lemma(
            p.mod_eq_add_right,
            &[n, interior, zero, pow_a_n, interior_modeq_zero],
        );
        let zero_plus_pow_a = d.add(zero, pow_a_n);
        let zero_add_pow_a = d.lemma(p.zero_add, &[pow_a_n]);
        let step_a2 = eq_to_mod_eq(d, &p, n, zero_plus_pow_a, pow_a_n, zero_add_pow_a);
        let step_a_full = d.lemma(
            p.mod_eq_trans,
            &[
                n,
                interior_plus_pow_a,
                zero_plus_pow_a,
                pow_a_n,
                step_a,
                step_a2,
            ],
        );

        let step_b = d.lemma(
            p.mod_eq_add_left,
            &[n, interior_plus_pow_a, pow_a_n, pow_b_n, step_a_full],
        );
        let pow_b_plus_a = d.add(pow_b_n, pow_a_n);
        let pow_a_plus_b = d.add(pow_a_n, pow_b_n);
        let add_comm_eq = d.lemma(p.add_comm, &[pow_b_n, pow_a_n]);
        let step_c = eq_to_mod_eq(d, &p, n, pow_b_plus_a, pow_a_plus_b, add_comm_eq);
        let step_bc = d.lemma(
            p.mod_eq_trans,
            &[n, mid3, pow_b_plus_a, pow_a_plus_b, step_b, step_c],
        );

        let s_to_mid3 = eq_to_mod_eq(d, &p, n, s, mid3, eq_s_expanded);
        let modeq_s_final = d.lemma(
            p.mod_eq_trans,
            &[n, s, mid3, pow_a_plus_b, s_to_mid3, step_bc],
        );

        let ab = d.add(a, b);
        let pow_ab_n = d.pow(ab, n);
        let eq_pow_s = d.lemma(p.add_pow, &[a, b, n]);
        let pow_to_s = eq_to_mod_eq(d, &p, n, pow_ab_n, s, eq_pow_s);
        let goal_n = d.lemma(
            p.mod_eq_trans,
            &[n, pow_ab_n, s, pow_a_plus_b, pow_to_s, modeq_s_final],
        );

        // Transport the `n`-phrased result back to `pp`.
        let final_motive = d.eq_motive(n, &|d, x| {
            let abx = d.pow(ab, x);
            let ax = d.pow(a, x);
            let bx = d.pow(b, x);
            let sum = d.add(ax, bx);
            d.mod_eq(x, abx, sum)
        });
        let final_proof = d.transport(n, final_motive, goal_n, pp, eq_n_pp);

        let ax = d.pow(a, pp);
        let bx = d.pow(b, pp);
        let pow_ab_pp = d.pow(ab, pp);
        let sum_pp = d.add(ax, bx);
        let target = d.mod_eq(pp, pow_ab_pp, sum_pp);
        let stmt = d.arrow(prime_ty_pp, target);
        let proof = d.lam_fv(prime_fv, prime_ty_pp, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Step 4 (HEADLINE): Fermat's little theorem.
// ============================================================================

/// `Nat.pow_prime_modeq_self : prime p → a^p ≡ a [p]`.
///
/// Induction on `a`. Base (`a = 0`): `0^p ≡ 0 [p]`, via `p = succ (pred p)`
/// (from positivity) and the pure definitional reduction `pow 0 (succ m) = 0`
/// (`pow_succ` then `mul_zero`). Step: `add_pow_modeq_prime` at `b = 1` gives
/// `(j+1)^p ≡ j^p + 1^p [p]`; `1^p = 1` (`one_pow`) and the IH `j^p ≡ j [p]`
/// close it, using `add(j,1) ≡ succ j` definitionally throughout.
pub(super) fn declare_pow_prime_modeq_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_prime_modeq_self, 2, &|d, v| {
        let (pp, a) = (v[0], v[1]);
        let prime_ty_pp = prime_ty(d, &p, pp);
        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let px = d.pow(x, pp);
            d.mod_eq(pp, px, x)
        };
        let target = motive(d, a);

        let body = d.induct(
            &motive,
            &|d| {
                // modEq pp (pow 0 pp) 0, via pp = succ m and
                // pow(0, succ m) = 0 (pow_succ then mul_zero, definitional).
                let zero_lt_pp = prime_pos(d, &p, pp, prime_proof);
                let eq_pp_n_fn = pos_implies_succ_pred(d, &p, pp);
                let eq_pp_n = d.apply(eq_pp_n_fn, &[zero_lt_pp]);
                let m = d.pred(pp);
                let n = d.succ(m);
                let eq_n_pp = d.symm(pp, n, eq_pp_n);
                let zero = d.zero();
                let base_at_n = d.lemma(p.mod_eq_refl, &[pp, zero]);
                let motive_base = d.eq_motive(n, &|d, x| {
                    let px = d.pow(zero, x);
                    d.mod_eq(pp, px, zero)
                });
                d.transport(n, motive_base, base_at_n, pp, eq_n_pp)
            },
            &|d, j, ih| {
                // modEq pp (pow j pp) j -> modEq pp (pow (succ j) pp) (succ j)
                let one = d.num(1);
                let frobenius = d.lemma(p.add_pow_modeq_prime, &[pp, j, one, prime_proof]);
                // frobenius : modEq pp (pow(add(j,one),pp)) (add(pow(j,pp),pow(one,pp)))
                //           ~ modEq pp (pow(succ j,pp)) (add(pow(j,pp),pow(one,pp)))  [defeq]
                let pow_j_pp = d.pow(j, pp);
                let pow_one_pp = d.pow(one, pp);
                let h_one_pow = d.lemma(p.one_pow, &[pp]);
                let rhs0 = d.add(pow_j_pp, pow_one_pp);
                let rhs1 = d.add(pow_j_pp, one);
                let step1 = d.congr(pow_one_pp, one, h_one_pow, &|d, t| d.add(pow_j_pp, t));
                let succ_j = d.succ(j);
                let pow_succ_j_pp = d.pow(succ_j, pp);

                let eq_to_mid = eq_to_mod_eq(d, &p, pp, rhs0, rhs1, step1);
                let frobenius_to_rhs1 = d.lemma(
                    p.mod_eq_trans,
                    &[pp, pow_succ_j_pp, rhs0, rhs1, frobenius, eq_to_mid],
                );

                let lifted_ih = d.lemma(p.mod_eq_add_right, &[pp, pow_j_pp, j, one, ih]);
                // lifted_ih : modEq pp (add(pow_j_pp,one)) (add(j,one))
                //           ~ modEq pp rhs1 (succ j)  [defeq]
                d.lemma(
                    p.mod_eq_trans,
                    &[
                        pp,
                        pow_succ_j_pp,
                        rhs1,
                        succ_j,
                        frobenius_to_rhs1,
                        lifted_ih,
                    ],
                )
            },
            a,
        );
        let stmt = d.arrow(prime_ty_pp, target);
        let proof = d.lam_fv(prime_fv, prime_ty_pp, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.modEq_pow`, `Nat.dvd_sum_range_of_forall_lt`,
/// `Nat.add_pow_modeq_prime`, and `Nat.pow_prime_modeq_self`, in dependency
/// order.
pub(super) fn declare_fermat(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_mod_eq_pow(d, p)?;
    declare_dvd_sum_range_of_forall_lt(d, p)?;
    declare_add_pow_modeq_prime(d, p)?;
    declare_pow_prime_modeq_self(d, p)?;
    Ok(())
}
