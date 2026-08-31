//! **The first supplementary law of quadratic reciprocity**, residue half:
//! for an odd prime `p = 2m+1` with `m` EVEN (equivalently `p ≡ 1 (mod 4)`),
//! `-1` IS a quadratic residue mod `p`, and the witness is `m!`.
//!
//! `first_supplementary.rs` (ADR-1230) landed the other half. Together the two
//! are the law; neither alone is.
//!
//! ## Why the converse of Euler's criterion is not needed
//!
//! The residue half needs a WITNESS, and the textbook route to one is the
//! CONVERSE of Euler's criterion (`a^((p-1)/2) ≡ 1 ⟹ a is a residue`), which
//! `qr_criterion.rs`'s module doc records as needing a primitive root or a
//! root-counting argument this kernel cannot state. **Wilson's theorem gives
//! the witness outright**, with no converse anywhere:
//!
//! ```text
//!   (p-1)! = m! · ∏_{j=m+1}^{2m} j                       -- split at m
//!          = m! · ∏_{k<m} (2m - k)                       -- reflect the upper half
//!          ≡ m! · ∏_{k<m} (-(k+1))          [p]          -- 2m-k + (k+1) = p
//!          = m! · ((-1)^m · m!)                          -- scaled-index collapse
//! ```
//!
//! and Wilson makes the left side `-1`. That identity is
//! [`declare_wilson_half_split`], stated for EVERY `m` (both parities), and it
//! is the reusable half. At even `m` the sign is `1`, so `(m!)^2 ≡ -1` and
//! `m!` is the residue witness ([`declare_first_supplementary_law_residue`]).
//!
//! ## The reflection, and what it needed
//!
//! `Int.prodRange_permute` supplies the reversal given `InjectiveOn σ m` and
//! `MapsInto σ m` for `σ k := sub (pred m) k`. Neither existed. Both are
//! BOUNDED statements and that is not incidental: **`σ` is not a global
//! involution**, because `Nat.sub` truncates (`sub 3 (sub 3 5) = 3`, not `5`).
//! So `Nat.conjugate_injective`, whose hypothesis is an unbounded
//! `∀ x, t (t x) = x`, does not apply — but `wilson.rs`'s
//! [`injective_of_involutive_local`](super::wilson::injective_of_involutive_local)
//! takes exactly the bounded law `∀ k, Lt k n → σ (σ k) = k` and was already
//! written, generic over `σ`, for `Nat.inverseIndex`. It is reused verbatim.
//!
//! The one genuinely new lemma is `Nat.sub_sub_self`
//! (`nat_prelude/order.rs`): `Le k n → sub n (sub n k) = k`, which is both the
//! involution law and — through `sub_le` plus `sub_lt` — nothing to do with
//! `MapsInto`, which is a separate two-line bound.
//!
//! ## Index arithmetic
//!
//! The pointwise congruence needs, in `Nat` and for `k < m`,
//! `succ k + succ (m + σ k) = succ (2m)`. `Nat.add` recurses on its RIGHT
//! argument, so `add x (succ y)` iota-reduces and only ONE `succ_add` is
//! needed; the rest is `add_comm`/`add_assoc`, `sub_add_cancel` (which turns
//! `σ k + k` into `pred m`), and `succ_pred_of_pos`. `0 < m` is never a
//! hypothesis of anything here — it is derived from `k < m`, which is in hand
//! wherever it is needed.
//!
//! Lifting that to `ℤ` needs no `ofNat_add` lemma: `Int.add (ofNat a)
//! (ofNat b)` is definitionally `ofNat (add a b)`, so `nat_eq_to_int` carries
//! the whole identity across. `Int.modulus_modEq_zero` then gives `p ≡ 0 [p]`
//! unconditionally, and `ModEq.add_left_cancel'` peels the `ofNat (k+1)` off
//! both sides.

use super::euler::{int_exists_intro, is_quadratic_residue, residue_predicate};
use super::first_supplementary::pos_of_nat_succ;
use super::modeq::imodeq;
use super::ops::IntDev;
use super::prod::compose;
use super::second_supplementary::two_mul_eq_add_self;
use super::wilson::{injective_of_involutive_local, prime_condition};
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// The three index functions, built exactly the way their consumers build them
// ============================================================================

/// `fun j => ofNat (succ j)` — `Int.factorial`'s own body, so
/// `prodRange (factor_fn d) n` is definitionally `factorial n`.
fn factor_fn(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let body = d.of_nat(sj);
    d.lam_fv(j_fv, nat, body)
}

/// `fun k => f (add a k)` — the same shape `prod.rs`'s `prodRange_split`
/// produces for its tail factor, rebuilt here rather than beta-reduced so the
/// two terms match syntactically.
fn shifted_fn(d: &mut IntDev<'_>, f: ExprId, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let shifted = d.add(a, k);
    let body = d.apply(f, &[shifted]);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => sub (pred m) k` — the reflection of `[0,m)`.
fn reflect_fn(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pm = d.pred(m);
    let body = d.sub(pm, k);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => mul a (ofNat (succ k))` — the shape
/// `Int.prodRange_scaledIndexEqPowMulFactorial` is stated over.
fn scaled_fn(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let ofk = d.of_nat(sk);
    let body = d.imul(a, ofk);
    d.lam_fv(k_fv, nat, body)
}

// ============================================================================
// Side conditions, all derived from `Lt k m` rather than assumed
// ============================================================================

/// `Lt zero m` from `hk : Lt k m`. `Lt k m` IS `Le (succ k) m`, and
/// `Le 1 (succ k)` is `succ_le_succ` of `zero_le k`, so this is one
/// `le_trans` and no arithmetic.
fn pos_of_lt(d: &mut IntDev<'_>, k: ExprId, m: ExprId, hk: ExprId) -> ExprId {
    let np = d.prelude();
    let zero = d.zero();
    let one_nat = d.num(1);
    let sk = d.succ(k);
    let zle = d.lemma(np.zero_le, &[k]);
    let one_le_sk = d.lemma(np.succ_le_succ, &[zero, k, zle]);
    d.lemma(np.le_trans, &[one_nat, sk, m, one_le_sk, hk])
}

/// `Le k (pred m)` from `hk : Lt k m`, by `pred_le_pred` at `succ k ≤ m`
/// (`pred (succ k)` iota-reduces to `k`, so no further step is needed).
fn le_pred_of_lt(d: &mut IntDev<'_>, k: ExprId, m: ExprId, hk: ExprId) -> ExprId {
    let np = d.prelude();
    let sk = d.succ(k);
    d.lemma(np.pred_le_pred, &[sk, m, hk])
}

/// `∀ k, Lt k m → Eq Nat (sub (pred m) (sub (pred m) k)) k` — the reflection's
/// BOUNDED involution law, the input
/// [`injective_of_involutive_local`](super::wilson::injective_of_involutive_local)
/// takes.
fn reflect_involutive(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let np = d.prelude();
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, m);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let pm = d.pred(m);
    let le = le_pred_of_lt(d, k, m, hk);
    let body = d.lemma(np.sub_sub_self, &[pm, k, le]);

    let with_hk = d.lam_fv(hk_fv, hk_ty, body);
    d.lam_fv(k_fv, nat, with_hk)
}

/// `MapsInto (fun k => sub (pred m) k) m`, i.e.
/// `∀ i, Lt i m → Lt (sub (pred m) i) m`.
///
/// `sub_le` bounds the reflected index by `pred m`, and `sub_lt` puts
/// `pred m` strictly below `m` — the latter needing `0 < m`, which
/// [`pos_of_lt`] takes from the hypothesis already in hand. `sub m 1`
/// iota-reduces to `pred m`, so `sub_lt` is accepted at the `pred m` spelling
/// with no bridging step.
fn reflect_maps_into(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let np = d.prelude();
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, m);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let one_nat = d.num(1);
    let pm = d.pred(m);
    let pos_m = pos_of_lt(d, i, m, hi);
    // `Lt zero 1` is `Le 1 1`.
    let pos_one = d.lemma(np.le_refl, &[one_nat]);
    let pred_lt = d.lemma(np.sub_lt, &[m, one_nat, pos_m, pos_one]);
    let bounded = d.lemma(np.sub_le, &[pm, i]);
    let reflected = d.sub(pm, i);
    let body = d.lemma(np.lt_of_le_of_lt, &[reflected, pm, m, bounded, pred_lt]);

    let with_hi = d.lam_fv(hi_fv, hi_ty, body);
    d.lam_fv(i_fv, nat, with_hi)
}

// ============================================================================
// The pointwise congruence
// ============================================================================

/// `Eq Nat (add (succ k) (succ (add m (sub (pred m) k)))) (succ (mul 2 m))`,
/// for `k < m`.
///
/// The reflected upper-half factor and its partner `k+1` sum to `p` exactly.
/// One `succ_add` is the whole cost of the successor bookkeeping, because
/// `Nat.add` eats its RIGHT argument; `sub_add_cancel` collapses
/// `σ k + k` to `pred m`, and `succ_pred_of_pos` closes it at `m + m`.
fn index_sum_eq_p(d: &mut IntDev<'_>, m: ExprId, k: ExprId, hk: ExprId) -> ExprId {
    let np = d.prelude();
    let two_nat = d.num(2);
    let pm = d.pred(m);
    let j = d.sub(pm, k);
    let a_term = d.add(m, j);
    let sk = d.succ(k);
    let sa = d.succ(a_term);
    let start = d.add(sk, sa);

    // `add (succ k) (succ A)` iota-reduces to `succ (add (succ k) A)`;
    // `succ_add` turns the inner sum into `succ (add k A)`.
    let inner_start = d.add(sk, a_term);
    let k_plus_a = d.add(k, a_term);
    let succ_ka = d.succ(k_plus_a);
    let step_succ_add = d.lemma(np.succ_add, &[k, a_term]);
    let h1 = d.congr(inner_start, succ_ka, step_succ_add, &|d, x| d.succ(x));
    let t2 = d.succ(succ_ka);

    // `add k (add m j) = add m (pred m)`.
    let am_j_k = d.add(a_term, k);
    let j_plus_k = d.add(j, k);
    let m_jk = d.add(m, j_plus_k);
    let m_pm = d.add(m, pm);
    let comm = d.lemma(np.add_comm, &[k, a_term]);
    let assoc = d.lemma(np.add_assoc, &[m, j, k]);
    let le_pred = le_pred_of_lt(d, k, m, hk);
    let cancel = d.lemma(np.sub_add_cancel, &[k, pm, le_pred]);
    let congr_inner = d.congr(j_plus_k, pm, cancel, &|d, x| d.add(m, x));
    let (_, h_ka) = d.chain(
        k_plus_a,
        &[(am_j_k, comm), (m_jk, assoc), (m_pm, congr_inner)],
    );
    let t3 = {
        let inner = d.succ(m_pm);
        d.succ(inner)
    };
    let h2 = d.congr(k_plus_a, m_pm, h_ka, &|d, x| {
        let inner = d.succ(x);
        d.succ(inner)
    });

    // `succ (add m (pred m))` is `add m (succ (pred m))` by iota, so
    // `succ_pred_of_pos` lands it on `add m m` under one `succ`.
    let pos_m = pos_of_lt(d, k, m, hk);
    // `succ_pred_of_pos` states `m = succ (pred m)`, NOT the other direction.
    let succ_pred_rev = d.lemma(np.succ_pred_of_pos, &[m, pos_m]);
    let s_pm = d.succ(pm);
    let succ_pred = d.symm(m, s_pm, succ_pred_rev);
    let mm = d.add(m, m);
    let h3 = d.congr(s_pm, m, succ_pred, &|d, x| {
        let inner = d.add(m, x);
        d.succ(inner)
    });
    let t4 = d.succ(mm);

    // `add m m` back to `mul 2 m`.
    let mul2m = d.mul(two_nat, m);
    let half = two_mul_eq_add_self(d, m);
    let half_back = d.symm(mul2m, mm, half);
    let h4 = d.congr(mm, mul2m, half_back, &|d, x| d.succ(x));
    let pp = d.succ(mul2m);

    let (_, proof) = d.chain(start, &[(t2, h1), (t3, h2), (t4, h3), (pp, h4)]);
    proof
}

/// `ModEq (ofNat (succ (mul 2 m)))
///        (ofNat (succ (add m (sub (pred m) k))))
///        (mul (neg one) (ofNat (succ k)))`, for `k < m`.
///
/// The two naturals sum to `p` ([`index_sum_eq_p`]), and
/// `Int.add (ofNat a) (ofNat b)` is definitionally `ofNat (add a b)`, so the
/// sum lifts to `ℤ` by `nat_eq_to_int` alone. `modulus_modEq_zero` supplies
/// `p ≡ 0 [p]` with no positivity hypothesis, and
/// `ModEq.add_left_cancel'` removes the shared `ofNat (k+1)`.
fn pointwise_modeq(d: &mut IntDev<'_>, m: ExprId, k: ExprId, hk: ExprId) -> ExprId {
    let p = d.int();
    let two_nat = d.num(2);
    let mul2m = d.mul(two_nat, m);
    let pp = d.succ(mul2m);
    let pi = d.of_nat(pp);

    let pm = d.pred(m);
    let j = d.sub(pm, k);
    let x_nat = {
        let inner = d.add(m, j);
        d.succ(inner)
    };
    let z_nat = d.succ(k);
    let xi = d.of_nat(x_nat);
    let zi = d.of_nat(z_nat);

    let h_sum = index_sum_eq_p(d, m, k, hk);
    let sum_nat = d.add(z_nat, x_nat);
    let h_int = d.nat_eq_to_int(sum_nat, pp, h_sum, &|d, x| d.of_nat(x));
    let sum_int = d.iadd(zi, xi);

    let izero = d.izero();
    let mz = d.const_app(p.modulus_mod_eq_zero, &[pi]);
    let back = d.isymm(sum_int, pi, h_int);
    let s1 = d.int_eq_rewrite(pi, sum_int, back, mz, &|d, z| {
        let izero = d.izero();
        imodeq(d, pi, z, izero)
    });

    let neg_zi = d.ineg(zi);
    let z_plus_neg = d.iadd(zi, neg_zi);
    let h_an = d.const_app(p.add_neg, &[zi]);
    let an_back = d.isymm(z_plus_neg, izero, h_an);
    let s2 = d.int_eq_rewrite(izero, z_plus_neg, an_back, s1, &|d, z| {
        imodeq(d, pi, sum_int, z)
    });

    let res = d.const_app(p.mod_eq_add_left_cancel, &[pi, xi, neg_zi, zi, s2]);

    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let scaled = d.imul(neg_one, zi);
    let h_nm = d.const_app(p.neg_one_mul, &[zi]);
    let nm_back = d.isymm(scaled, neg_zi, h_nm);
    d.int_eq_rewrite(neg_zi, scaled, nm_back, res, &|d, z| imodeq(d, pi, xi, z))
}

// ============================================================================
// `Int.wilsonHalfSplit`
// ============================================================================

/// `Int.wilsonHalfSplit :
///   ∀ m, (2 ≤ succ (mul 2 m) ∧ ∀ d, d ∣ succ (mul 2 m) → d = 1 ∨ d = succ (mul 2 m)) →
///     ModEq (ofNat (succ (mul 2 m)))
///           (mul (factorial m) (mul (pow (neg one) m) (factorial m)))
///           (neg one)`
///
/// `(p-1)! = m! · ((-1)^m · m!)` mod `p`, for BOTH parities of `m`. See the
/// module doc for the four-step route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_wilson_half_split(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.wilson_half_split, 1, &|d, v| {
        let m = v[0];
        let nat = d.nat_ty();
        let two_nat = d.num(2);
        let mul2m = d.mul(two_nat, m);
        let pp = d.succ(mul2m);
        let pi = d.of_nat(pp);
        let mm = d.add(m, m);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        let fact_m = d.const_app(p.factorial, &[m]);
        let pow_m = d.ipow(neg_one, m);
        let inner = d.imul(pow_m, fact_m);
        let target = d.imul(fact_m, inner);
        let concl = imodeq(d, pi, target, neg_one);

        let prime_ty = prime_condition(d, pp);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime = d.kernel().fvar(prime_fv);

        let f_fn = factor_fn(d);
        let g_fn = shifted_fn(d, f_fn, m);
        let rho = reflect_fn(d, m);
        let gr_fn = compose(d, g_fn, rho);
        let h_fn = scaled_fn(d, neg_one);

        let prod_g = d.const_app(p.prod_range, &[g_fn, m]);
        let prod_gr = d.const_app(p.prod_range, &[gr_fn, m]);
        let prod_h = d.const_app(p.prod_range, &[h_fn, m]);
        let prod_f_mm = d.const_app(p.prod_range, &[f_fn, mm]);
        let prod_f_m = d.const_app(p.prod_range, &[f_fn, m]);

        let pos_pi = pos_of_nat_succ(d, mul2m);

        // --- the reversal ---------------------------------------------------
        let invol = reflect_involutive(d, m);
        let inj = injective_of_involutive_local(d, rho, invol, m);
        let maps = reflect_maps_into(d, m);
        let perm = d.const_app(p.prod_range_permute, &[g_fn, m, rho, inj, maps]);

        // --- the pointwise congruence, over the reflected upper half --------
        let pointwise = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_ty = d.lt(k, m);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let body = pointwise_modeq(d, m, k, hk);
            let with_hk = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, with_hk)
        };
        let mlt = d.const_app(
            p.mod_eq_prod_range_lt,
            &[pi, gr_fn, h_fn, m, pos_pi, pointwise],
        );

        // --- the scaled-index collapse --------------------------------------
        let scaled = d.const_app(
            p.prod_range_scaled_index_eq_pow_mul_factorial,
            &[neg_one, m],
        );

        // `ModEq p (prodRange G m) ((-1)^m · m!)`.
        let perm_back = d.isymm(prod_g, prod_gr, perm);
        let step_a = d.int_eq_rewrite(prod_gr, prod_g, perm_back, mlt, &|d, z| {
            imodeq(d, pi, z, prod_h)
        });
        let step_b = d.int_eq_rewrite(prod_h, inner, scaled, step_a, &|d, z| {
            imodeq(d, pi, prod_g, z)
        });

        // Multiply through by `m!` on the left.
        let lifted = d.const_app(
            p.mod_eq_mul_left,
            &[pi, prod_g, inner, fact_m, pos_pi, step_b],
        );
        let lower_times_g = d.imul(fact_m, prod_g);

        // --- Wilson, split at `m` -------------------------------------------
        let wil = d.const_app(p.wilson, &[pp, prime]);
        let half = two_mul_eq_add_self(d, m);
        let wil2 = d.nat_rewrite(mul2m, mm, half, wil, &|d, x| {
            let p = d.int();
            let f_fn = factor_fn(d);
            let lhs = d.const_app(p.prod_range, &[f_fn, x]);
            let one_i = d.ione();
            let neg_one = d.ineg(one_i);
            imodeq(d, pi, lhs, neg_one)
        });
        let split = d.const_app(p.prod_range_split, &[f_fn, m, m]);
        let split_rhs = d.imul(prod_f_m, prod_g);
        let wil3 = d.int_eq_rewrite(prod_f_mm, split_rhs, split, wil2, &|d, z| {
            let one_i = d.ione();
            let neg_one = d.ineg(one_i);
            imodeq(d, pi, z, neg_one)
        });

        let lifted_back = d.const_app(p.mod_eq_symm, &[pi, lower_times_g, target, lifted]);
        let body = d.const_app(
            p.mod_eq_trans,
            &[pi, target, lower_times_g, neg_one, lifted_back, wil3],
        );

        (stmt, d.lam_fv(prime_fv, prime_ty, body))
    })?;
    Ok(())
}

// ============================================================================
// `Int.firstSupplementaryLawResidue`
// ============================================================================

/// `Int.firstSupplementaryLawResidue :
///   ∀ m, (2 ≤ succ (mul 2 m) ∧ ∀ d, d ∣ succ (mul 2 m) → d = 1 ∨ d = succ (mul 2 m)) →
///     Nat.Even m →
///     IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one)`
///
/// The witness is `Int.factorial m` — supplied by
/// [`declare_wilson_half_split`], not extracted from any converse. `Nat.Even`
/// rather than `p mod 4 = 1` for the same reason `first_supplementary.rs`
/// takes `Nat.Odd`: `Nat.mod` is stuck at symbolic arguments, while `Even`'s
/// witness is an equation the sign lemma consumes directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_first_supplementary_law_residue(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.first_supplementary_law_residue, 1, &|d, v| {
        let m = v[0];
        let np = d.prelude();
        let two_nat = d.num(2);
        let mul2m = d.mul(two_nat, m);
        let pp = d.succ(mul2m);
        let pi = d.of_nat(pp);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        let prime_ty = prime_condition(d, pp);
        let even_ty = d.const_app(np.even, &[m]);
        let concl = is_quadratic_residue(d, pi, neg_one);
        let stmt = {
            let tail = d.arrow(even_ty, concl);
            d.arrow(prime_ty, tail)
        };

        let prime_fv = d.fresh_fvar();
        let prime = d.kernel().fvar(prime_fv);
        let even_fv = d.fresh_fvar();
        let even = d.kernel().fvar(even_fv);

        let fact_m = d.const_app(p.factorial, &[m]);
        let pow_m = d.ipow(neg_one, m);
        let inner = d.imul(pow_m, fact_m);
        let target = d.imul(fact_m, inner);

        let base = d.const_app(p.wilson_half_split, &[m, prime]);
        let sign = d.const_app(p.pow_neg_one_of_even, &[m, even]);
        let one_times = d.imul(one_i, fact_m);
        let s1 = d.int_eq_rewrite(pow_m, one_i, sign, base, &|d, z| {
            let scaled = d.imul(z, fact_m);
            let lhs = d.imul(fact_m, scaled);
            let one_i = d.ione();
            let neg_one = d.ineg(one_i);
            imodeq(d, pi, lhs, neg_one)
        });
        let _ = target;
        let one_mul = d.const_app(p.one_mul, &[fact_m]);
        let s2 = d.int_eq_rewrite(one_times, fact_m, one_mul, s1, &|d, z| {
            let lhs = d.imul(fact_m, z);
            let one_i = d.ione();
            let neg_one = d.ineg(one_i);
            imodeq(d, pi, lhs, neg_one)
        });

        let predicate = residue_predicate(d, pi, neg_one);
        let witness = int_exists_intro(d, predicate, fact_m, s2);

        let with_even = d.lam_fv(even_fv, even_ty, witness);
        (stmt, d.lam_fv(prime_fv, prime_ty, with_even))
    })?;
    Ok(())
}

/// Declare everything in this module.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_first_supplementary_residue_all(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    declare_wilson_half_split(d)?;
    declare_first_supplementary_law_residue(d)
}
