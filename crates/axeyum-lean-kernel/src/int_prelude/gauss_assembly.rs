//! **Gauss's lemma.** `Int.gaussLemmaSignCount : ∀ m a, Nat.PrimeCond (succ (mul 2
//! m)) → gcd a (succ (mul 2 m)) = 1 → ModEq (ofNat (succ (mul 2 m))) (pow
//! (ofNat a) m) (pow (neg one) (Nat.gaussNegCount (succ (mul 2 m)) a m))`
//!
//! — item 3 of the connecting theorem ADR-0990 sized in five pieces and
//! ADR-1070 reduced to two. Every ingredient is landed elsewhere; this file
//! wires them and adds no new induction, in the same shape
//! `euler_assembly.rs` uses for Euler's totient theorem (a permuted product,
//! cancelled by `Int.ModEq.cancel`) — with a SIGN in place of Euler's
//! coprimality predicate, which is why this one folds an unrestricted
//! `Int.prodRange` where Euler folds `prodRangeIf`.
//!
//! ## The chain
//!
//! Writing `pp := succ (2m)`, `A := ofNat a`, `ε_j := bool_select_int
//! (gaussSignNeg pp a (succ j)) (-1) 1`, `Φ_j := ofNat (gaussFold pp a
//! (succ j))`:
//!
//! ```text
//! A^m · m!  =  ∏_{j<m} (A · ofNat (succ j))            [prodRange_scaledIndexEqPowMulFactorial, symm]
//!           ≡  ∏_{j<m} (ε_j · Φ_j)             [pp]     [gaussTermModEq, lifted by modEq_prodRange_lt]
//!           =  (∏ ε_j) · (∏ Φ_j)                        [prodRange_mul]
//!           =  (-1)^gaussNegCount(pp,a,m) · m!          [gaussSignProdEqPowNegOneOfCount; ∏Φ = m! below]
//! ⟹  A^m ≡ (-1)^gaussNegCount(pp,a,m)  [pp]             [ModEq.cancel at m!, coprime since m < pp prime]
//! ```
//!
//! ## `∏_{j<m} Φ_j = m!` — the permutation half
//!
//! `Int.factorial m` is by definition `prodRange (fun k => ofNat (succ k))
//! m`, so this is `Int.prodRange_permute` at the self-map `σ j := pred
//! (gaussFold pp a (succ j))` — piece 2's `Nat.gauss_fold_shift_injective_on`
//! / `_maps_into` supply `InjectiveOn`/`MapsInto` on `[0,m)` verbatim, with
//! no `Nat`/`Int` bridging (they are already `Nat`-typed, which is what
//! `prodRange_permute` quantifies over). One `Int.prodRange_congr_lt` then
//! moves `ofNat (succ (σ j))` to `ofNat (gaussFold pp a (succ j))`, using
//! `Nat.succ_pred_of_pos` fed the positivity half of
//! `Nat.gauss_fold_in_range`.
//!
//! ## `m < pp` is unconditional, and that matters
//!
//! `Nat.coprime_factorial_of_lt_prime` needs `Lt m pp`. `gauss_lemma.rs`'s
//! own in-range proof derives `Lt m pp` through `lt_two_mul_of_pos`, which
//! requires `0 < m` — fine there (it always has an index `0 < k ≤ m` in
//! hand), useless here, since the theorem must also hold at `m = 0` (`pp =
//! 1`). This file instead goes through `Nat.le_add_right m m : Le m (m+m)`
//! transported along `2m = m+m`, then `Nat.lt_succ_of_le` — no positivity
//! hypothesis anywhere, so the statement carries none.
//!
//! ## What is NOT assumed about `pp`
//!
//! Only `Nat.PrimeCond pp` (for the factorial's coprimality) and `gcd a pp =
//! 1` (for the fold's injectivity). Oddness is structural: `pp` is written
//! `succ (mul 2 m)`, matching piece 2's own statements exactly, so no
//! separate parity fact is needed.

use super::modeq::imodeq;
use super::ops::IntDev;
use super::prod::bool_select_int;
use super::wilson::prime_condition;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun k => f (g k)` — a per-file local copy of `prod.rs`'s private
/// `compose` (this development's standing per-file-copy convention).
fn compose(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

/// `Int.gaussLemmaSignCount` — Gauss's lemma. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_gauss_lemma(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.theorem(p.gauss_lemma_sign_count, 2, &|d, v| {
        let (m, a) = (v[0], v[1]);
        let nat = d.nat_ty();

        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let mul2m = d.mul(two_nat, m);
        let pp = d.succ(mul2m);

        let prime_ty = prime_condition(d, pp);
        let gcd_a_pp = d.gcd(a, pp);
        let coprime_ty = d.eq(gcd_a_pp, one_nat);

        let n_int = d.of_nat(pp);
        let a_int = d.of_nat(a);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let count = d.const_app(p.nat.gauss_neg_count, &[pp, a, m]);
        let pow_a_m = d.ipow(a_int, m);
        let pow_neg_count = d.ipow(neg_one, count);
        let concl = imodeq(d, n_int, pow_a_m, pow_neg_count);

        let stmt = {
            let inner = d.arrow(coprime_ty, concl);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime = d.kernel().fvar(prime_fv);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        // `0 < pp` — the ONE positivity fact everything below wants, and it
        // is free: `pp` is a `succ`. `Int.lt zero (ofNat pp)` is defeq
        // `Nat.le 1 pp`, so the same term serves both carriers (the defeq
        // `wilson.rs`'s `nat_prime_pos` call site already relies on).
        let pos_pp = d.zero_lt_succ(mul2m);

        // ------------------------------------------------------------------
        // The four index functions.
        // ------------------------------------------------------------------
        // F j := A * ofNat (succ j) — the exact lambda
        // `prodRange_scaledIndexEqPowMulFactorial` states its LHS over.
        let big_f = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let ofsj = d.of_nat(sj);
            let body = d.imul(a_int, ofsj);
            d.lam_fv(j_fv, nat, body)
        };
        // EPS j := bool_select_int (gaussSignNeg pp a (succ j)) (-1) 1 — the
        // exact lambda `gaussSignProdEqPowNegOneOfCount` states its LHS over.
        let eps_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let t = d.const_app(p.nat.gauss_sign_neg, &[pp, a, sj]);
            let body = bool_select_int(d, t, neg_one, one_i);
            d.lam_fv(j_fv, nat, body)
        };
        // PHI j := ofNat (gaussFold pp a (succ j)).
        let fold_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let fold = d.const_app(p.nat.gauss_fold, &[pp, a, sj]);
            let body = d.of_nat(fold);
            d.lam_fv(j_fv, nat, body)
        };
        // G j := EPS j * PHI j, written out rather than as two beta redexes;
        // defeq `prodRange_mul`'s stated `fun k => mul (f k) (g k)`.
        let big_g = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let t = d.const_app(p.nat.gauss_sign_neg, &[pp, a, sj]);
            let sel = bool_select_int(d, t, neg_one, one_i);
            let fold = d.const_app(p.nat.gauss_fold, &[pp, a, sj]);
            let phi = d.of_nat(fold);
            let body = d.imul(sel, phi);
            d.lam_fv(j_fv, nat, body)
        };

        let prod_f = d.const_app(p.prod_range, &[big_f, m]);
        let prod_g = d.const_app(p.prod_range, &[big_g, m]);
        let prod_eps = d.const_app(p.prod_range, &[eps_fn, m]);
        let prod_fold = d.const_app(p.prod_range, &[fold_fn, m]);
        let fact_m = d.const_app(p.factorial, &[m]);

        // ------------------------------------------------------------------
        // Step 1: the per-term congruence, folded over `[0,m)`.
        // ------------------------------------------------------------------
        let pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, m);
            let hj_fv = d.fresh_fvar();
            let sj = d.succ(j);
            let term_fn = d.lemma(p.gauss_term_mod_eq, &[pp, a, sj]);
            // The per-term theorem holds for EVERY index; the `Lt j m`
            // hypothesis `modEq_prodRange_lt` supplies is simply unused.
            let term = d.apply(term_fn, &[pos_pp]);
            let with_hj = d.lam_fv(hj_fv, hj_ty, term);
            d.lam_fv(j_fv, nat, with_hj)
        };
        let step1 = d.lemma(
            p.mod_eq_prod_range_lt,
            &[n_int, big_f, big_g, m, pos_pp, pointwise],
        );
        // step1 : ModEq n_int prod_f prod_g

        // ------------------------------------------------------------------
        // Step 2: `∏ Φ = m!` — permutation plus the `succ ∘ pred` repair.
        // ------------------------------------------------------------------
        let sigma = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let fold = d.const_app(p.nat.gauss_fold, &[pp, a, sj]);
            let body = d.pred(fold);
            d.lam_fv(j_fv, nat, body)
        };
        let inj = d.const_app(p.nat.gauss_fold_shift_injective_on, &[m, a, cop]);
        let maps = d.const_app(p.nat.gauss_fold_shift_maps_into, &[m, a, cop]);
        let fi = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let body = d.of_nat(sk);
            d.lam_fv(k_fv, nat, body)
        };
        let permute = d.const_app(p.prod_range_permute, &[fi, m, sigma, inj, maps]);
        let fi_sigma = compose(d, fi, sigma);
        let prod_fi = d.const_app(p.prod_range, &[fi, m]);
        let prod_fi_sigma = d.const_app(p.prod_range, &[fi_sigma, m]);

        let pointwise_fold = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, m);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let sj = d.succ(j);
            let fold_sj = d.const_app(p.nat.gauss_fold, &[pp, a, sj]);
            let zero_nat = d.zero();
            let pos_fold_ty = d.lt(zero_nat, fold_sj);
            let le_fold_ty = d.le(fold_sj, m);

            let pos_sj = d.zero_lt_succ(j);
            let range_fn = d.const_app(p.nat.gauss_fold_in_range, &[m, a, sj]);
            // `hj : Lt j m` is defeq `Le (succ j) m`, exactly the third
            // hypothesis's shape at `k := succ j` — no bridging lemma.
            let range = d.apply(range_fn, &[cop, pos_sj, hj]);
            let pos_fold = d.and_left(pos_fold_ty, le_fold_ty, range);

            let sp = d.lemma(p.nat.succ_pred_of_pos, &[fold_sj, pos_fold]);
            // sp : Eq Nat (gaussFold …) (succ (pred (gaussFold …)))
            let pred_fold = d.pred(fold_sj);
            let succ_pred = d.succ(pred_fold);
            let sp_rev = d.symm(fold_sj, succ_pred, sp);
            let body = d.nat_eq_to_int(succ_pred, fold_sj, sp_rev, &|d, x| d.of_nat(x));
            // body : Eq Int (ofNat (succ (pred …))) (ofNat (gaussFold …)),
            // defeq `Eq Int (fi (sigma j)) (fold_fn j)`.
            let with_hj = d.lam_fv(hj_fv, hj_ty, body);
            d.lam_fv(j_fv, nat, with_hj)
        };
        let congr_fold = d.lemma(
            p.prod_range_congr_lt,
            &[fi_sigma, fold_fn, m, pointwise_fold],
        );
        let (_e, fact_eq_fold) = d.ichain(
            prod_fi,
            &[(prod_fi_sigma, permute), (prod_fold, congr_fold)],
        );
        // `prod_fi` is defeq `factorial m` (`Int.factorial`'s own body), so
        // this checks at `Eq Int (factorial m) prod_fold`.
        let fold_eq_fact = d.isymm(fact_m, prod_fold, fact_eq_fold);

        // ------------------------------------------------------------------
        // Step 3: rewrite both sides of `step1` into `m!`-factored form.
        // ------------------------------------------------------------------
        let scaled = d.lemma(p.prod_range_scaled_index_eq_pow_mul_factorial, &[a_int, m]);
        let pow_times_fact = d.imul(pow_a_m, fact_m);
        let s1 = d.int_eq_rewrite(prod_f, pow_times_fact, scaled, step1, &|d, t| {
            imodeq(d, n_int, t, prod_g)
        });

        let split = d.lemma(p.prod_range_mul, &[eps_fn, fold_fn, m]);
        let eps_times_fold = d.imul(prod_eps, prod_fold);
        let s2 = d.int_eq_rewrite(prod_g, eps_times_fold, split, s1, &|d, t| {
            imodeq(d, n_int, pow_times_fact, t)
        });

        let sign_prod = d.const_app(p.gauss_sign_prod_eq_pow_neg_one_of_count, &[pp, a, m]);
        let s3 = d.int_eq_rewrite(prod_eps, pow_neg_count, sign_prod, s2, &|d, t| {
            let rhs = d.imul(t, prod_fold);
            imodeq(d, n_int, pow_times_fact, rhs)
        });

        let neg_times_fact = d.imul(pow_neg_count, fact_m);
        let s4 = d.int_eq_rewrite(prod_fold, fact_m, fold_eq_fact, s3, &|d, t| {
            let rhs = d.imul(pow_neg_count, t);
            imodeq(d, n_int, pow_times_fact, rhs)
        });
        // s4 : ModEq n_int (pow_a_m * m!) (pow_neg_count * m!)

        // ------------------------------------------------------------------
        // Step 4: commute `m!` to the left on both sides and cancel it.
        // ------------------------------------------------------------------
        let fact_times_pow = d.imul(fact_m, pow_a_m);
        let comm_left = d.const_app(p.mul_comm, &[pow_a_m, fact_m]);
        let s5 = d.int_eq_rewrite(pow_times_fact, fact_times_pow, comm_left, s4, &|d, t| {
            imodeq(d, n_int, t, neg_times_fact)
        });

        let fact_times_neg = d.imul(fact_m, pow_neg_count);
        let comm_right = d.const_app(p.mul_comm, &[pow_neg_count, fact_m]);
        let s6 = d.int_eq_rewrite(neg_times_fact, fact_times_neg, comm_right, s5, &|d, t| {
            imodeq(d, n_int, fact_times_pow, t)
        });
        // s6 : ModEq n_int (m! * pow_a_m) (m! * pow_neg_count)

        // `Lt m pp`, with NO positivity hypothesis on `m` (see the module
        // doc): `Le m (m+m)` transported along `2m = m+m`, then
        // `lt_succ_of_le`.
        let add_m_m = d.add(m, m);
        let le_m_mm = d.lemma(p.nat.le_add_right, &[m, m]);
        let mul_one_m = d.mul(one_nat, m);
        let add_mul_one_m_m = d.add(mul_one_m, m);
        let succ_mul_eq = d.lemma(p.nat.succ_mul, &[one_nat, m]);
        let one_mul_eq = d.lemma(p.nat.one_mul, &[m]);
        let congr_one_mul = d.congr(mul_one_m, m, one_mul_eq, &|d, x| d.add(x, m));
        let two_mul_eq_add = d.trans(
            mul2m,
            add_mul_one_m_m,
            add_m_m,
            succ_mul_eq,
            congr_one_mul,
        );
        // two_mul_eq_add : Eq Nat (mul 2 m) (add m m)
        let add_eq_two_mul = d.symm(mul2m, add_m_m, two_mul_eq_add);
        let le_motive = d.eq_motive(add_m_m, &|d, x| d.le(m, x));
        let le_m_mul2m = d.transport(add_m_m, le_motive, le_m_mm, mul2m, add_eq_two_mul);
        let lt_m_pp = d.lemma(p.nat.lt_succ_of_le, &[m, mul2m, le_m_mul2m]);

        let cop_fact = d.const_app(
            p.coprime_factorial_of_lt_prime,
            &[pp, m, prime, lt_m_pp],
        );
        // cop_fact : Coprime (factorial m) (ofNat pp)

        let cancelled = d.const_app(
            p.mod_eq_cancel,
            &[n_int, fact_m, pow_a_m, pow_neg_count, pos_pp, cop_fact, s6],
        );
        // cancelled : ModEq n_int pow_a_m pow_neg_count — the conclusion.

        let with_cop = d.lam_fv(cop_fv, coprime_ty, cancelled);
        let proof = d.lam_fv(prime_fv, prime_ty, with_cop);
        (stmt, proof)
    })?;
    Ok(())
}
