//! **The second supplementary law of quadratic reciprocity**, in its Legendre-
//! symbol (power-residue) form: for an odd prime `p = 2m+1`,
//!
//! ```text
//! 2^((p-1)/2) ≡  1  (mod p)   ⟺   p ≡ ±1 (mod 8)
//! 2^((p-1)/2) ≡ -1  (mod p)   ⟺   p ≡ ±3 (mod 8)
//! ```
//!
//! ## What is proved, and what is deliberately not
//!
//! [`declare_second_supplementary_law`] states exactly the displayed
//! dichotomy: `Int.secondSupplementaryLaw` classifies `2^m mod p` by `p mod 8`,
//! and because the four residue classes it names are exhaustive and mutually
//! exclusive, it gives BOTH directions of each line above.
//!
//! It does **not** claim the classical "`2` is a quadratic residue mod `p` iff
//! `p ≡ ±1 (mod 8)`" in the `IsQuadraticResidue` form. Half of that is
//! reachable and is [`declare_two_not_residue_of_pm_three_mod_eight`]: Euler's
//! criterion's `-1` detector (`Int.euler_criterion_neg_one_imp_not_residue`,
//! `qr_criterion.rs`) turns the `≡ -1` line into "`2` is NOT a residue". The
//! other half needs the CONVERSE of Euler's criterion (`a^((p-1)/2) ≡ 1 ⟹ a`
//! is a residue), which needs a primitive root or a root-counting argument over
//! a polynomial ring this kernel has no `List`/`Finset` to state —
//! `qr_criterion.rs`'s module doc records that gap and it is unchanged here.
//!
//! ## Route
//!
//! Three already-landed theorems, one new arithmetic fact, and nothing else:
//!
//! 1. `Int.gaussLemmaSignCount` (ADR-1130) — Gauss's lemma:
//!    `a^m ≡ (−1)^(gaussNegCount pp a m) [pp]` for `pp = 2m+1` prime and
//!    `gcd a pp = 1`.
//! 2. `Nat.gaussNegCountTwoClosedForm` — that count, at `a := 2`, is
//!    `sub m (div m 2)`.
//! 3. `Nat.half_ceil_parity` (`nat_prelude::half_ceil_parity`, ADR-1150) — the
//!    parity of `sub m (div m 2)` is decided by `m mod 4`, equivalently by
//!    `p mod 8`. This is the one new piece; the handoff from ADR-1130 called it
//!    "a `p mod 8` case split" and predicted no such split existed. What was
//!    actually needed is a DOUBLE even/odd split, which
//!    [`NatPrelude::even_or_odd`] already supports directly.
//! 4. [`declare_pow_neg_one_of_even`]/[`declare_pow_neg_one_of_odd`] turn that
//!    parity into the sign, by exposing `fibonacci.rs`'s already-proved
//!    `pow_neg_one_add_self`/`pow_neg_one_succ` rather than re-deriving them.
//!
//! Coprimality is **not** a hypothesis: `pp = succ (mul 2 m)` is odd by
//! construction, and `Nat.coprime_two_left` (`Iff (gcd 2 n = 1) (Odd n)`)
//! converts that directly. The only arithmetic needed for it is
//! `mul 2 m = add m m`, which is `mul_comm` plus one `zero_add` — `mul m 2`
//! reduces (`Nat.mul` recurses on its right argument, and `2` is a literal)
//! while `mul 2 m` does not, which is why the commutation comes first.
//!
//! [`NatPrelude::even_or_odd`]: crate::nat_prelude::NatPrelude::even_or_odd

use super::modeq::imodeq;
use super::ops::{IntDev, exists_elim};
use super::wilson::prime_condition;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::half_ceil_parity::components;

use super::fibonacci::{pow_neg_one_add_self, pow_neg_one_succ};

/// `fun k : Nat => Eq n (add k k)` — [`Nat.Even`]'s own witness predicate.
///
/// A local mirror of `nat_prelude::parity`'s `even_predicate`, which is
/// private to that module. Kept byte-identical so `Nat.Even n` and this
/// `Exists` are the same term, not merely definitionally equal.
///
/// [`Nat.Even`]: crate::nat_prelude::NatPrelude::even
fn even_predicate(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let body = d.eq(n, kk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k : Nat => Eq n (succ (add k k))` — [`Nat.Odd`]'s own witness
/// predicate; see [`even_predicate`].
///
/// [`Nat.Odd`]: crate::nat_prelude::NatPrelude::odd
fn odd_predicate(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let body = d.eq(n, skk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Int.pow_neg_one_of_even : ∀ (n : Nat), Nat.Even n → Eq Int (pow (neg one) n) one`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_pow_neg_one_of_even(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.pow_neg_one_of_even, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let pow_n = d.ipow(neg_one, n);

        let even_ty = d.const_app(p.nat.even, &[n]);
        let concl = d.ieq(pow_n, one_i);
        let stmt = d.arrow(even_ty, concl);

        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let kk = d.add(k, k);
            let hyp = d.eq(n, kk);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);

            let step_index = d.nat_eq_to_int(n, kk, hk, &|d, x| d.ipow(neg_one, x));
            let pow_kk = d.ipow(neg_one, kk);
            // `Eq Int (pow (neg one) (add k k)) (ofNat one)`; `Int.one` IS
            // `Int.ofNat 1` by definition, so the chain's `one_i` target is
            // accepted by delta alone.
            let step_value = pow_neg_one_add_self(d, k);
            let (_, proof) = d.ichain(pow_n, &[(pow_kk, step_index), (one_i, step_value)]);

            let inner = d.lam_fv(hk_fv, hyp, proof);
            d.lam_fv(k_fv, nat, inner)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let pred = even_predicate(d, n);
        let body = exists_elim(d, pred, concl, h, minor);
        let proof = d.lam_fv(h_fv, even_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.pow_neg_one_of_odd : ∀ (n : Nat), Nat.Odd n → Eq Int (pow (neg one) n) (neg one)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_pow_neg_one_of_odd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.pow_neg_one_of_odd, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let pow_n = d.ipow(neg_one, n);

        let odd_ty = d.const_app(p.nat.odd, &[n]);
        let concl = d.ieq(pow_n, neg_one);
        let stmt = d.arrow(odd_ty, concl);

        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let kk = d.add(k, k);
            let skk = d.succ(kk);
            let hyp = d.eq(n, skk);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);

            let step_index = d.nat_eq_to_int(n, skk, hk, &|d, x| d.ipow(neg_one, x));
            let pow_skk = d.ipow(neg_one, skk);
            // `pow (neg one) (succ K) = neg (pow (neg one) K)` at `K := k+k`.
            let step_peel = pow_neg_one_succ(d, kk);
            let pow_kk = d.ipow(neg_one, kk);
            let neg_pow_kk = d.ineg(pow_kk);
            // `pow (neg one) (k+k) = 1`, under `neg`.
            let inner_value = pow_neg_one_add_self(d, k);
            let step_value = d.icongr(pow_kk, one_i, inner_value, &|d, x| d.ineg(x));

            let (_, proof) = d.ichain(
                pow_n,
                &[
                    (pow_skk, step_index),
                    (neg_pow_kk, step_peel),
                    (neg_one, step_value),
                ],
            );

            let inner = d.lam_fv(hk_fv, hyp, proof);
            d.lam_fv(k_fv, nat, inner)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let pred = odd_predicate(d, n);
        let body = exists_elim(d, pred, concl, h, minor);
        let proof = d.lam_fv(h_fv, odd_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq Nat (mul 2 m) (add m m)`.
///
/// `mul 2 m` is stuck (`Nat.mul` recurses on its RIGHT argument and `m` is
/// symbolic); `mul m 2` is not, reducing by iota to `add (add zero m) m`. So
/// commute first, then discharge the `zero_add`.
fn two_mul_eq_add_self(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let np = d.prelude();
    let two = d.num(2);
    let start = d.mul(two, m);
    let commuted = d.mul(m, two);
    let step_comm = d.lemma(np.mul_comm, &[two, m]);

    let zero = d.zero();
    let zero_add_m = d.add(zero, m);
    let inner = d.lemma(np.zero_add, &[m]);
    let step_zero = d.congr(zero_add_m, m, inner, &|d, x| d.add(x, m));
    let mm = d.add(m, m);

    let (_, proof) = d.chain(start, &[(commuted, step_comm), (mm, step_zero)]);
    proof
}

/// `Eq Nat (gcd 2 (succ (mul 2 m))) 1` — the modulus is odd by construction.
fn two_coprime_to_odd_modulus(d: &mut IntDev<'_>, m: ExprId) -> ExprId {
    let np = d.prelude();
    let logic = np.logic;
    let nat = d.nat_ty();
    let uone = d.level_one();

    let two = d.num(2);
    let one_nat = d.num(1);
    let mul2m = d.mul(two, m);
    let pp = d.succ(mul2m);

    // `Odd pp` at witness `m`: `pp = succ (add m m)`.
    let mm = d.add(m, m);
    let s_mm = d.succ(mm);
    let base = two_mul_eq_add_self(d, m);
    let witness_eq = d.congr(mul2m, mm, base, &|d, x| d.succ(x));
    let _ = s_mm;
    let pred = odd_predicate(d, pp);
    let intro = d.kernel().const_(logic.exists_intro, vec![uone]);
    let odd_pp = d.apply(intro, &[nat, pred, m, witness_eq]);

    // `Iff (gcd 2 pp = 1) (Odd pp)`, backwards.
    let gcd_eq = {
        let g = d.gcd(two, pp);
        d.eq(g, one_nat)
    };
    let odd_ty = d.const_app(np.odd, &[pp]);
    let iff_proof = d.const_app(np.coprime_two_left, &[pp]);
    d.const_app(logic.iff_mpr, &[gcd_eq, odd_ty, iff_proof, odd_pp])
}

/// `Int.secondSupplementaryLaw` — see the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_second_supplementary_law(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let logic = p.logic;

    d.theorem(p.second_supplementary_law, 1, &|d, v| {
        let m = v[0];
        let np = d.prelude();
        let two_nat = d.num(2);
        let mul2m = d.mul(two_nat, m);
        let pp = d.succ(mul2m);
        let pp_int = d.of_nat(pp);
        let two_int = d.of_nat(two_nat);
        let pow_two_m = d.ipow(two_int, m);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        let [plus_classes, minus_classes, even_count, odd_count] = components(d, &np, m);

        let modeq_plus = imodeq(d, pp_int, pow_two_m, one_i);
        let modeq_minus = imodeq(d, pp_int, pow_two_m, neg_one);
        let left_conj = d.const_app(logic.and, &[plus_classes, modeq_plus]);
        let right_conj = d.const_app(logic.and, &[minus_classes, modeq_minus]);
        let target = d.const_app(logic.or, &[left_conj, right_conj]);

        let prime_ty = prime_condition(d, pp);
        let stmt = d.arrow(prime_ty, target);

        let prime_fv = d.fresh_fvar();
        let prime = d.kernel().fvar(prime_fv);

        // --- Gauss's lemma at `a := 2`, with coprimality supplied -----------
        let coprime = two_coprime_to_odd_modulus(d, m);
        let gauss = d.const_app(p.gauss_lemma_sign_count, &[m, two_nat, prime, coprime]);

        // --- rewrite the count to its closed form ---------------------------
        let count_name = d.const_app(np.gauss_neg_count, &[pp, two_nat, m]);
        let half = d.div(m, two_nat);
        let count = d.sub(m, half);
        let closed = d.lemma(np.gauss_neg_count_two_closed_form, &[m]);

        let pow_at_name = d.ipow(neg_one, count_name);
        let pow_at_count = d.ipow(neg_one, count);
        let index_eq = d.nat_eq_to_int(count_name, count, closed, &|d, x| d.ipow(neg_one, x));
        let motive_index = d.ieq_motive(pow_at_name, &|d, x| imodeq(d, pp_int, pow_two_m, x));
        let gauss_closed =
            d.itransport(pow_at_name, motive_index, gauss, pow_at_count, index_eq);

        // --- split on the parity of that count ------------------------------
        let parity = d.const_app(np.half_ceil_parity, &[m]);
        let plus_conj = d.const_app(logic.and, &[plus_classes, even_count]);
        let minus_conj = d.const_app(logic.and, &[minus_classes, odd_count]);

        let branch = |d: &mut IntDev<'_>, h: ExprId, is_even: bool| -> ExprId {
            let (classes, parity_ty, conj_ty, sign, sign_lemma) = if is_even {
                (
                    plus_classes,
                    even_count,
                    plus_conj,
                    one_i,
                    p.pow_neg_one_of_even,
                )
            } else {
                (
                    minus_classes,
                    odd_count,
                    minus_conj,
                    neg_one,
                    p.pow_neg_one_of_odd,
                )
            };
            let class_proof = d.const_app(logic.and_left, &[classes, parity_ty, h]);
            let parity_proof = d.const_app(logic.and_right, &[classes, parity_ty, h]);
            let _ = conj_ty;

            let sign_eq = d.const_app(sign_lemma, &[count, parity_proof]);
            let motive_sign = d.ieq_motive(pow_at_count, &|d, x| imodeq(d, pp_int, pow_two_m, x));
            let final_modeq =
                d.itransport(pow_at_count, motive_sign, gauss_closed, sign, sign_eq);

            let modeq_ty = if is_even { modeq_plus } else { modeq_minus };
            let conj = d.const_app(
                logic.and_intro,
                &[classes, modeq_ty, class_proof, final_modeq],
            );
            if is_even {
                d.const_app(logic.or_inl, &[left_conj, right_conj, conj])
            } else {
                d.const_app(logic.or_inr, &[left_conj, right_conj, conj])
            }
        };

        let body = d.or_elim(
            plus_conj,
            minus_conj,
            target,
            parity,
            &|d, h| branch(d, h, true),
            &|d, h| branch(d, h, false),
        );

        let proof = d.lam_fv(prime_fv, prime_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare everything in this module.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_second_supplementary_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_pow_neg_one_of_even(d)?;
    declare_pow_neg_one_of_odd(d)?;
    declare_second_supplementary_law(d)
}
