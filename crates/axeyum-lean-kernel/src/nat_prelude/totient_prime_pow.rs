//! `Nat.totient_mul_of_dvd` and `Nat.totient_prime_pow` — the totient at a
//! prime power, by counting, with **no factorization and no primality in the
//! counting step at all**.
//!
//! ## The one new counting result
//!
//! [`declare_totient_mul_of_dvd`] is
//!
//! ```text
//! Nat.totient_mul_of_dvd : ∀ m e, Dvd e m → Eq (totient (mul m e)) (mul (totient m) e)
//! ```
//!
//! and it is the whole content of this file. Note what it does **not** carry:
//! no primality, no positivity, no factorization. The hypothesis is `e ∣ m`
//! and nothing more, and it is genuinely load-bearing — the identity fails at
//! 493 non-dividing pairs with `1 ≤ m,e ≤ 25`, the smallest being `(m,e) =
//! (1,2)` where `φ(2) = 1` against `φ(1)·2 = 2`. Checked, with that control
//! asserted to fail, by `scripts/tests/check-totient-prime-power-numerics.py`.
//!
//! The proof is three existing lemmas and one small new one:
//!
//! 1. **The gcd bridge.** For `e ∣ m` the two coprimality predicates agree
//!    *everywhere*: `gcd k (m*e) = 1 ↔ gcd k m = 1`. Forward is the `mp` of
//!    the already-unconditional `Nat.coprime_mul_iff`; backward is its `mpr`
//!    fed by `Nat.coprime_of_dvd_right`, which turns `gcd k m = 1` into
//!    `gcd k e = 1` precisely because `e ∣ m`. This is
//!    [`declare_coprime_mul_iff_of_dvd`], and it is the ONLY place the
//!    hypothesis is spent.
//! 2. **Blocking.** With the predicate now `m`-periodic, `Nat.countRange_product`
//!    at block width `m` and block count `e` factors the count over
//!    `[0, m*e)` into `countRange S m * countRange (fun _ => true) e`. Its
//!    per-block hypothesis is discharged by `Nat.div_mod_block` (reading
//!    `mod (m*a + b) m = b` back) composed with `Nat.gcd_mod_left_eq_gcd`.
//!    No induction is written here — `countRange_product` already did it.
//! 3. **The block count.** [`declare_count_range_const_true`],
//!    `countRange (fun _ => true) n = n`, a three-line induction over
//!    `Nat.countRange_succ_of_true`. It did not exist.
//!
//! `countRange S m` is `totient m` **on the nose** — `S` is built by exactly
//! `totient.rs`'s own `totient_predicate` recipe — so nothing bridges the two.
//!
//! ## Why this route and not the Euler product
//!
//! The classical `φ(n) = n·∏(1−1/p)` needs the factorization to be UNIQUE, and
//! `factorization.rs` says in its own module doc that uniqueness "needs
//! multiset equality of the factor list, which needs a type this kernel does
//! not have, and is not attempted here". That is a real obstruction and it is
//! not worked around here — it is **routed around**: the prime power case
//! never mentions a factor multiset, because `p ∣ p^(j+1)` is immediate from
//! `pow`'s own ι-equation and `Nat.dvd_mul_left`. See
//! `docs/research/09-decisions/adr-0660-…` for the same argument applied to
//! the three remaining `ml430` totient mirrors.
//!
//! ## The prime power itself
//!
//! [`declare_totient_pow_succ_of_prime`] is the induction, in the form that
//! avoids `Nat.sub`'s truncation inside the inductive step:
//!
//! ```text
//! Nat.totient_pow_succ_of_prime :
//!   ∀ q j, Prime q → Eq (totient (pow q (succ j))) (mul (sub q 1) (pow q j))
//! ```
//!
//! Base `j = 0` is `Nat.totient_prime` after `one_mul`/`mul_one`; the step is
//! `totient_mul_of_dvd` at `m := pow q (succ j)`, `e := q` — legal because
//! `pow q (succ j)` ι-reduces to `mul (pow q j) q`, so `Nat.dvd_mul_left`
//! supplies `Dvd q (pow q (succ j))` with no arithmetic lemma — then the
//! induction hypothesis and one `mul_assoc`.
//!
//! **Primality enters in exactly one place: the base case**, through
//! `totient_prime`. The inductive step is primality-free. That is visible in
//! the numerics too: `φ(c^k) = c^k − c^(k−1)` fails at 42 composite `(c,k)`
//! pairs, the smallest being `c = 4, k = 1` (`φ(4) = 2`, not `3`), and the
//! failure is entirely a failure of the base case.
//!
//! [`declare_totient_prime_pow`] then converts to the subtractive form the
//! `ml430` mirror is stated in:
//!
//! ```text
//! Nat.totient_prime_pow :
//!   ∀ q j, Prime q → Eq (totient (pow q (succ j))) (sub (pow q (succ j)) (pow q j))
//! ```
//!
//! stated at `succ j` rather than with a `Lt 0 k` hypothesis, so the exponent
//! is syntactically a successor everywhere `pow`'s ι-equation is needed. The
//! conversion goes through the additive form and `Nat.add_sub_cancel_left`,
//! because the right-handed `add_sub_cancel` does not exist in this prelude.
//!
//! ## Magnitudes
//!
//! Every numeral this file forms is small on purpose: prelude numerals are
//! unary, and `pow` grows fast enough that a test at `2^10` would cost more
//! than the whole prelude build. The evaluation tests instantiate at `2^3 = 8`
//! and `3^2 = 9` and nothing larger.

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local term builders. Per this prelude's house style each file keeps its own
// copies rather than sharing a private module.
// ============================================================================

/// `countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `fun k => beq (gcd k modulus) 1` — built by exactly the recipe
/// `totient.rs`'s private `totient_predicate` uses, so `countRange` of it at
/// `modulus` is defeq `totient modulus` on the nose.
fn coprime_pred(d: &mut NatDev<'_>, modulus: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let g = d.gcd(k, modulus);
    let one = d.num(1);
    let body = d.beq(g, one);
    d.lam_fv(k_fv, nat, body)
}

/// `fun _ : Nat => Bool.true`.
fn const_true_pred(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let true_ = d.bool_true();
    d.kernel().lam(anon, nat, true_, BinderInfo::Default)
}

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)` — the `Bool`-codomain congruence
/// [`NatOps::congr`] does not provide (it is hardcoded to a `Nat` codomain).
fn nat_congr_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// Non-dependent `Or.rec` into a goal.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// The two conjuncts of primality, spelled inline exactly as `totient.rs`,
/// `fermat.rs` and `factorization.rs` spell them: `Le two x` and
/// `∀ c, dvd c x → Eq c one ∨ Eq c x`. This prelude has no `Prime` predicate.
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

/// `prime x → Lt zero x`, via `1 ≤ 2 ≤ x`.
fn prime_pos(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, prime_proof: ExprId) -> ExprId {
    let (two_le_ty, divisor_clause_ty) = prime_parts(d, p, x);
    let two_le = and_left(d, two_le_ty, divisor_clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    d.lemma(p.le_trans, &[one, two, x, one_le_two, two_le])
}

// ============================================================================
// `Nat.countRange_const_true`.
// ============================================================================

/// `Nat.countRange_const_true : ∀ n, Eq Nat (countRange (fun _ => true) n) n`.
///
/// The trivial companion `countRange` never had: counting a predicate that is
/// `true` everywhere over `[0,n)` gives `n`. Induction on `n`; the step is
/// `Nat.countRange_succ_of_true`, whose `f k = true` hypothesis is
/// `Eq.refl true` here because the predicate is a constant lambda.
///
/// Needed by [`declare_totient_mul_of_dvd`] to collapse the block-count
/// factor `countRange (fun _ => true) e` that `Nat.countRange_product` leaves
/// behind.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_const_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.count_range_const_true, 1, &|d, v| {
        let n = v[0];
        let t = const_true_pred(d);
        let lhs = count_range(d, &p, t, n);
        let stmt = d.eq(lhs, n);

        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let c = count_range(d, &p, t, x);
            d.eq(c, x)
        };
        let proof = d.induct(
            &motive,
            // `countRange t 0 = 0`.
            &|d| {
                let zero = d.zero();
                let c = count_range(d, &p, t, zero);
                let z = d.lemma(p.count_range_zero, &[t]);
                let _ = c;
                z
            },
            // `countRange t (succ j) = succ (countRange t j) = succ j`.
            &|d, j, ih| {
                let true_ = d.bool_true();
                let at_j = d.apply(t, &[j]);
                let is_true = d.bool_refl(true_);
                let _ = at_j;
                let step = d.lemma(p.count_range_succ_of_true, &[t, j, is_true]);
                let cj = count_range(d, &p, t, j);
                let succ_cj = d.succ(cj);
                let succ_j = d.succ(j);
                let bump = d.congr(cj, j, ih, &|d, x| d.succ(x));
                let lhs_j = {
                    let sj = d.succ(j);
                    count_range(d, &p, t, sj)
                };
                d.trans(lhs_j, succ_cj, succ_j, step, bump)
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_mul_iff_of_dvd` — the gcd bridge, and the ONLY consumer of the
// divisibility hypothesis.
// ============================================================================

/// `Nat.coprime_mul_iff_of_dvd : ∀ k m e, Dvd e m →
/// Iff (Eq (gcd k (mul m e)) 1) (Eq (gcd k m) 1)`.
///
/// When `e ∣ m`, multiplying the modulus by `e` does not change which
/// residues are coprime to it. Forward is `Nat.coprime_mul_iff`'s `mp`
/// projected to its left conjunct — that direction is unconditional and does
/// not use `e ∣ m` at all. Backward is its `mpr`, whose second conjunct
/// `gcd k e = 1` comes from `Nat.coprime_of_dvd_right` applied to `e ∣ m`;
/// that is where the whole hypothesis is spent.
///
/// The hypothesis is genuinely load-bearing: the `Iff` fails at 165
/// non-dividing pairs with `1 ≤ m,e ≤ 15`, asserted as a negative control by
/// check `3N` of `scripts/tests/check-totient-prime-power-numerics.py`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_coprime_mul_iff_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_iff_of_dvd, 3, &|d, v| {
        let (k, m, e) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let me = d.mul(m, e);
        let g_me = d.gcd(k, me);
        let g_m = d.gcd(k, m);
        let g_e = d.gcd(k, e);
        let left = d.eq(g_me, one);
        let right = d.eq(g_m, one);
        let eq_e = d.eq(g_e, one);
        let dvd_ty = d.dvd(e, m);
        let iff_ty = d.const_app(p.logic.iff, &[left, right]);
        let stmt = d.arrow(dvd_ty, iff_ty);

        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        let and_ty = d.const_app(p.logic.and, &[right, eq_e]);
        let base_iff = d.lemma(p.coprime_mul_iff, &[k, m, e]);
        let base_fwd = iff_forward(d, left, and_ty, base_iff);
        let base_rev = iff_reverse(d, left, and_ty, base_iff);

        // forward : `gcd k (m*e) = 1 → gcd k m = 1`, unconditional.
        let forward = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let conj = d.apply(base_fwd, &[h]);
            let body = and_left(d, right, eq_e, conj);
            d.lam_fv(h_fv, left, body)
        };

        // reverse : `gcd k m = 1 → gcd k (m*e) = 1`, and this is where `e ∣ m`
        // is spent — `coprime_of_dvd_right` shrinks the modulus from `m` to `e`.
        let reverse = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ke = d.lemma(p.coprime_of_dvd_right, &[k, e, m, hd, h]);
            let conj = d.const_app(p.logic.and_intro, &[right, eq_e, h, ke]);
            let body = d.apply(base_rev, &[conj]);
            d.lam_fv(h_fv, right, body)
        };

        let intro = d.const_app(p.logic.iff_intro, &[left, right, forward, reverse]);
        let proof = d.lam_fv(hd_fv, dvd_ty, intro);
        (stmt, proof)
    })?;
    Ok(())
}

/// `iff : Iff (Eq gl 1) (Eq gr 1) ⊢ Eq Bool (beq gl 1) (beq gr 1)`.
///
/// Decides `beq gr 1` with `bool_true_or_false` — two branches, `Bool` has two
/// constructors, so this is case analysis and not excluded middle — and moves
/// each branch across the `Iff`. The `false` branch goes through
/// `ne_of_beq_eq_false` and `beq_eq_false_of_ne`, contraposing the FORWARD
/// direction; the `true` branch through `eq_of_beq_eq_true` and
/// `beq_eq_true_of_eq`, using the REVERSE direction.
fn iff_to_beq_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    gl: ExprId,
    gr: ExprId,
    iff_proof: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let bl = d.beq(gl, one);
    let br = d.beq(gr, one);
    let goal = d.bool_eq(bl, br);

    let left = d.eq(gl, one);
    let right = d.eq(gr, one);
    let fwd = iff_forward(d, left, right, iff_proof);
    let rev = iff_reverse(d, left, right, iff_proof);

    let br_true_ty = d.bool_eq(br, true_);
    let br_false_ty = d.bool_eq(br, false_);

    let on_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let pr = d.lemma(p.eq_of_beq_eq_true, &[gr, one, h]);
        let pl = d.apply(rev, &[pr]);
        let hl = d.lemma(p.beq_eq_true_of_eq, &[gl, one, pl]);
        let flipped = d.bool_symm(br, true_, h);
        let body = d.bool_trans(bl, true_, br, hl, flipped);
        d.lam_fv(h_fv, br_true_ty, body)
    };

    let on_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ne_r = d.lemma(p.ne_of_beq_eq_false, &[gr, one, h]);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);
        let ne_l = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let r_proof = d.apply(fwd, &[a]);
            let absurd = d.apply(ne_r, &[r_proof]);
            d.lam_fv(a_fv, left, absurd)
        };
        let _ = false_prop;
        let hl = d.lemma(p.beq_eq_false_of_ne, &[gl, one, ne_l]);
        let flipped = d.bool_symm(br, false_, h);
        let body = d.bool_trans(bl, false_, br, hl, flipped);
        d.lam_fv(h_fv, br_false_ty, body)
    };

    let decided = bool_true_or_false(d, &p, br);
    or_elim(
        d,
        &p,
        br_true_ty,
        br_false_ty,
        goal,
        on_true,
        on_false,
        decided,
    )
}

// ============================================================================
// `Nat.totient_mul_of_dvd` — LEMMA B, the file's whole content.
// ============================================================================

/// `Nat.totient_mul_of_dvd : ∀ m e, Dvd e m →
/// Eq Nat (totient (mul m e)) (mul (totient m) e)`.
///
/// See the module doc. Three steps, none of them an induction written here:
/// `countRange_congr` across the gcd bridge, then `countRange_product` at
/// block width `m` and block count `e`, then `countRange_const_true` on the
/// block-count factor.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_totient_mul_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_mul_of_dvd, 2, &|d, v| {
        let (m, e) = (v[0], v[1]);
        let me = d.mul(m, e);
        let dvd_ty = d.dvd(e, m);
        let tot_me = d.const_app(p.totient, &[me]);
        let tot_m = d.const_app(p.totient, &[m]);
        let rhs = d.mul(tot_m, e);
        let target = d.eq(tot_me, rhs);
        let stmt = d.arrow(dvd_ty, target);

        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        let pp = coprime_pred(d, me);
        let ss = coprime_pred(d, m);
        let tt = const_true_pred(d);

        // --- step 1: the two predicates agree pointwise, everywhere --------
        let pointwise = {
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let iff_proof = {
                let base = d.lemma(p.coprime_mul_iff_of_dvd, &[i, m, e]);
                d.apply(base, &[hd])
            };
            let gl = d.gcd(i, me);
            let gr = d.gcd(i, m);
            let body = iff_to_beq_eq(d, &p, gl, gr, iff_proof);
            d.lam_fv(i_fv, nat, body)
        };
        let cr_pp = count_range(d, &p, pp, me);
        let cr_ss = count_range(d, &p, ss, me);
        let step1 = d.lemma(p.count_range_congr, &[pp, ss, me, pointwise]);

        // --- step 2: block the range into `e` blocks of width `m` ----------
        //
        // `countRange_product`'s per-block hypothesis lives at the index
        // `m*a + b`; `div_mod_block` reads `mod (m*a + b) m = b` back and
        // `gcd_mod_left_eq_gcd` turns that into the gcd equation.
        let per_block = {
            let nat = d.nat_ty();
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let lt_ty = d.lt(b, m);
            let lt_fv = d.fresh_fvar();
            let lt = d.kernel().fvar(lt_fv);
            let true_ = d.bool_true();
            let at_a = d.apply(tt, &[a]);
            let r_true_ty = d.bool_eq(at_a, true_);
            let r_fv = d.fresh_fvar();

            let ma = d.mul(m, a);
            let idx = d.add(ma, b);
            let blk = d.lemma(p.div_mod_block, &[m, a, b, lt]);
            let div_eq = {
                let q = d.div(idx, m);
                d.eq(q, a)
            };
            let mod_eq = {
                let r = d.modulo(idx, m);
                d.eq(r, b)
            };
            let hmod = and_right(d, div_eq, mod_eq, blk);

            let mod_idx = d.modulo(idx, m);
            let g_mod = d.gcd(mod_idx, m);
            let g_idx = d.gcd(idx, m);
            let g_b = d.gcd(b, m);
            // `gcd (mod idx m) m = gcd idx m`, run backwards.
            let inv = d.lemma(p.gcd_mod_left_eq_gcd, &[idx, m]);
            let back = d.symm(g_mod, g_idx, inv);
            let across = d.congr(mod_idx, b, hmod, &|d, x| d.gcd(x, m));
            let heq = d.trans(g_idx, g_mod, g_b, back, across);
            let bool_eq = nat_congr_bool(d, g_idx, g_b, heq, &|d, x| {
                let o = d.num(1);
                d.beq(x, o)
            });

            let with_r = d.lam_fv(r_fv, r_true_ty, bool_eq);
            let with_lt = d.lam_fv(lt_fv, lt_ty, with_r);
            let with_b = d.lam_fv(b_fv, nat, with_lt);
            d.lam_fv(a_fv, nat, with_b)
        };

        // The `R a = false` branch is vacuous: `R` is the constant `true`, so
        // the hypothesis is `Eq Bool true false`.
        let no_dead_block = {
            let nat = d.nat_ty();
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let lt_ty = d.lt(b, m);
            let lt_fv = d.fresh_fvar();
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let at_a = d.apply(tt, &[a]);
            let r_false_ty = d.bool_eq(at_a, false_);
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);

            let ma = d.mul(m, a);
            let idx = d.add(ma, b);
            let g_idx = d.gcd(idx, m);
            let one = d.num(1);
            let lhs = d.beq(g_idx, one);
            let goal = d.bool_eq(lhs, false_);
            let flipped = d.bool_symm(true_, false_, r);
            let body = d.false_true_elim(goal, flipped);

            let with_r = d.lam_fv(r_fv, r_false_ty, body);
            let with_lt = d.lam_fv(lt_fv, lt_ty, with_r);
            let with_b = d.lam_fv(b_fv, nat, with_lt);
            d.lam_fv(a_fv, nat, with_b)
        };

        let step2 = d.lemma(
            p.count_range_product,
            &[ss, tt, ss, m, e, per_block, no_dead_block],
        );
        let cr_ss_m = count_range(d, &p, ss, m);
        let cr_tt_e = count_range(d, &p, tt, e);
        let product = d.mul(cr_ss_m, cr_tt_e);

        // --- step 3: the block-count factor collapses ----------------------
        let const_true = d.lemma(p.count_range_const_true, &[e]);
        let step3 = d.congr(cr_tt_e, e, const_true, &|d, x| d.mul(cr_ss_m, x));
        let final_rhs = d.mul(cr_ss_m, e);

        let t12 = d.trans(cr_pp, cr_ss, product, step1, step2);
        let body = d.trans(cr_pp, product, final_rhs, t12, step3);
        let proof = d.lam_fv(hd_fv, dvd_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// The prime power.
// ============================================================================

/// `Nat.totient_pow_succ_of_prime : ∀ q j, Prime q →
/// Eq Nat (totient (pow q (succ j))) (mul (sub q 1) (pow q j))`.
///
/// The induction, in the multiplicative form that keeps `Nat.sub`'s
/// truncation out of the inductive step (it appears only in the constant
/// factor `q - 1`, which is never decremented again).
///
/// Base `j = 0`: `pow q (succ zero)` ι-reduces to `mul (pow q zero) q` and
/// `pow q zero` to `1`, so the goal is `totient (mul 1 q) = mul (q-1) 1` —
/// `one_mul`, then `Nat.totient_prime`, then `mul_one` backwards.
///
/// Step: `pow q (succ (succ j))` ι-reduces to `mul (pow q (succ j)) q`, so
/// [`declare_totient_mul_of_dvd`] applies at `m := pow q (succ j)`, `e := q`.
/// Its `Dvd q (pow q (succ j))` obligation is `Nat.dvd_mul_left q (pow q j)`
/// — `pow q (succ j)` is *definitionally* `mul (pow q j) q`, so no arithmetic
/// lemma is needed. The induction hypothesis and one `mul_assoc` finish it.
///
/// **Primality is used in the base case only.** The step is primality-free,
/// which is why the composite counter-examples in check `5N` of
/// `scripts/tests/check-totient-prime-power-numerics.py` are all failures of
/// the base case (`φ(4) = 2`, not `4 - 1`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_totient_pow_succ_of_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_pow_succ_of_prime, 2, &|d, v| {
        let (q, j) = (v[0], v[1]);
        let one = d.num(1);
        let qm1 = d.sub(q, one);
        let prime_hyp = prime_ty(d, &p, q);

        let goal = |d: &mut NatDev<'_>, x: ExprId| {
            let sx = d.succ(x);
            let px = d.const_app(p.pow, &[q, sx]);
            let lhs = d.const_app(p.totient, &[px]);
            let base = d.const_app(p.pow, &[q, x]);
            let rhs = d.mul(qm1, base);
            d.eq(lhs, rhs)
        };
        let target = goal(d, j);
        let stmt = d.arrow(prime_hyp, target);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let body = d.induct(
            &goal,
            // `totient (pow q 1) = mul (q-1) (pow q 0)`.
            &|d| {
                let zero = d.zero();
                let szero = d.succ(zero);
                let p1 = d.const_app(p.pow, &[q, szero]);
                let p0 = d.const_app(p.pow, &[q, zero]);
                let lhs = d.const_app(p.totient, &[p1]);
                let tot_q = d.const_app(p.totient, &[q]);
                let rhs = d.mul(qm1, p0);

                // `pow q 1 ≡ mul (pow q 0) q ≡ mul 1 q`, and `one_mul` closes
                // it to `q`.
                let om = d.lemma(p.one_mul, &[q]);
                let mul_1_q = {
                    let o = d.num(1);
                    d.mul(o, q)
                };
                let s1 = d.congr(mul_1_q, q, om, &|d, x| d.const_app(p.totient, &[x]));
                let s2 = d.lemma(p.totient_prime, &[q, h]);
                let mo = d.lemma(p.mul_one, &[qm1]);
                let mul_qm1_1 = {
                    let o = d.num(1);
                    d.mul(qm1, o)
                };
                let s3 = d.symm(mul_qm1_1, qm1, mo);
                let t12 = d.trans(lhs, tot_q, qm1, s1, s2);
                d.trans(lhs, qm1, rhs, t12, s3)
            },
            // `totient (pow q (succ (succ j))) = mul (q-1) (pow q (succ j))`.
            &|d, i, ih| {
                let si = d.succ(i);
                let ssi = d.succ(si);
                let base = d.const_app(p.pow, &[q, i]);
                let pow_si = d.const_app(p.pow, &[q, si]);
                let pow_ssi = d.const_app(p.pow, &[q, ssi]);
                let lhs = d.const_app(p.totient, &[pow_ssi]);
                let tot_si = d.const_app(p.totient, &[pow_si]);

                // `Dvd q (pow q (succ i))`: `pow q (succ i) ≡ mul (pow q i) q`.
                let dvd = d.lemma(p.dvd_mul_left, &[q, base]);
                let lemma_b = {
                    let applied = d.lemma(p.totient_mul_of_dvd, &[pow_si, q]);
                    d.apply(applied, &[dvd])
                };
                let mid = d.mul(tot_si, q);
                // `mul (totient (pow q (succ i))) q = mul (mul (q-1) (pow q i)) q`.
                let inner = d.mul(qm1, base);
                let across = d.congr(tot_si, inner, ih, &|d, x| d.mul(x, q));
                let assoc_lhs = d.mul(inner, q);
                let assoc = d.lemma(p.mul_assoc, &[qm1, base, q]);
                let assoc_rhs = {
                    let bq = d.mul(base, q);
                    d.mul(qm1, bq)
                };

                let t1 = d.trans(lhs, mid, assoc_lhs, lemma_b, across);
                d.trans(lhs, assoc_lhs, assoc_rhs, t1, assoc)
            },
            j,
        );
        let proof = d.lam_fv(h_fv, prime_hyp, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.totient_prime_pow : ∀ q j, Prime q →
/// Eq Nat (totient (pow q (succ j))) (sub (pow q (succ j)) (pow q j))`.
///
/// The subtractive form the `ml430` mirror is stated in, from
/// [`declare_totient_pow_succ_of_prime`]'s multiplicative one. Stated at
/// `succ j` rather than with a `Lt 0 k` hypothesis so that `pow`'s ι-equation
/// fires syntactically.
///
/// The conversion needs `q = succ (pred q)` (from `2 ≤ q`) so that
/// `mul (pow q j) q` ι-reduces to `add (mul (pow q j) (pred q)) (pow q j)`,
/// and `sub q 1 = pred q` (`sub_succ` then `sub_zero`). Then
/// `Nat.add_sub_cancel_left` strips the trailing `pow q j`. It is
/// `add_sub_cancel_LEFT`, so an `add_comm` is needed first — the right-handed
/// `add_sub_cancel` does not exist in this prelude.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_totient_prime_pow(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_prime_pow, 2, &|d, v| {
        let (q, j) = (v[0], v[1]);
        let one = d.num(1);
        let sj = d.succ(j);
        let pow_sj = d.const_app(p.pow, &[q, sj]);
        let pow_j = d.const_app(p.pow, &[q, j]);
        let lhs = d.const_app(p.totient, &[pow_sj]);
        let rhs = d.sub(pow_sj, pow_j);
        let prime_hyp = prime_ty(d, &p, q);
        let stmt = d.arrow(prime_hyp, d.eq(lhs, rhs));

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let qm1 = d.sub(q, one);
        let mult = {
            let applied = d.lemma(p.totient_pow_succ_of_prime, &[q, j]);
            d.apply(applied, &[h])
        };
        let mult_rhs = d.mul(qm1, pow_j);

        // `q = succ (pred q)`, from `2 ≤ q`.
        let pos = prime_pos(d, &p, q, h);
        let q_eq = {
            let base = d.lemma(p.succ_pred_of_pos, &[q]);
            d.apply(base, &[pos])
        };
        let r = d.pred(q);
        let sr = d.succ(r);

        // `sub q 1 = pred q`: `sub q (succ zero) = pred (sub q zero) = pred q`.
        let qm1_is_r = {
            let zero = d.zero();
            let s1 = d.lemma(p.sub_succ, &[q, zero]);
            let sub_q_zero = d.sub(q, zero);
            let pred_sub = d.pred(sub_q_zero);
            let s0 = d.lemma(p.sub_zero, &[q]);
            let s2 = d.congr(sub_q_zero, q, s0, &|d, x| d.pred(x));
            d.trans(qm1, pred_sub, r, s1, s2)
        };

        // `mul (q-1) (pow q j) = mul (pred q) (pow q j) = mul (pow q j) (pred q)`.
        let r_pow = d.mul(r, pow_j);
        let s_a = d.congr(qm1, r, qm1_is_r, &|d, x| d.mul(x, pow_j));
        let pow_r = d.mul(pow_j, r);
        let s_b = d.lemma(p.mul_comm, &[r, pow_j]);

        // `add (mul (pow q j) (pred q)) (pow q j)` is `mul (pow q j) (succ (pred q))`
        // by ι, and that is `mul (pow q j) q` after transporting `q = succ (pred q)`
        // backwards — which is `pow q (succ j)` by ι again.
        let sum = d.add(pow_r, pow_j);
        let flipped_sum = d.add(pow_j, pow_r);
        let comm = d.lemma(p.add_comm, &[pow_r, pow_j]);
        let cancel = d.lemma(p.add_sub_cancel_left, &[pow_j, pow_r]);

        // `sub (pow q (succ j)) (pow q j) = sub (add (pow q j) (pow q j * pred q)) (pow q j)`
        // — the transport that turns `pow q (succ j)` into the shape
        // `add_sub_cancel_left` consumes.
        let pow_sj_is_sum = {
            // `mul (pow q j) q = mul (pow q j) (succ (pred q))` — ι gives
            // `add (mul (pow q j) (pred q)) (pow q j)`.
            let across = d.congr(q, sr, q_eq, &|d, x| d.mul(pow_j, x));
            let mul_pow_sr = d.mul(pow_j, sr);
            let _ = mul_pow_sr;
            // `pow q (succ j)` is definitionally `mul (pow q j) q`.
            let to_sum = d.trans(pow_sj, mul_pow_sr, sum, across, d.refl(sum));
            let _ = to_sum;
            across
        };
        let mul_pow_sr = d.mul(pow_j, sr);

        // Assemble the right-hand side backwards:
        //   sub (pow q (succ j)) (pow q j)
        //     = sub (add (pow q j) (mul (pow q j) (pred q))) (pow q j)   [comm]
        //     = mul (pow q j) (pred q)                                   [cancel]
        let rhs_step1 = d.congr(pow_sj, mul_pow_sr, pow_sj_is_sum, &|d, x| d.sub(x, pow_j));
        let sub_sum = d.sub(sum, pow_j);
        let rhs_step2 = d.congr(sum, flipped_sum, comm, &|d, x| d.sub(x, pow_j));
        let sub_flipped = d.sub(flipped_sum, pow_j);

        // lhs -> mul (q-1) (pow q j) -> mul (pred q) (pow q j) -> mul (pow q j) (pred q)
        let c1 = d.trans(lhs, mult_rhs, r_pow, mult, s_a);
        let c2 = d.trans(lhs, r_pow, pow_r, c1, s_b);

        // rhs -> sub_sum -> sub_flipped -> pow_r, then run it backwards.
        let r1 = d.trans(rhs, sub_sum, sub_flipped, rhs_step1, rhs_step2);
        let r2 = d.trans(rhs, sub_flipped, pow_r, r1, cancel);
        let r_back = d.symm(rhs, pow_r, r2);

        let body = d.trans(lhs, pow_r, rhs, c2, r_back);
        let proof = d.lam_fv(h_fv, prime_hyp, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare everything in this file, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_totient_prime_pow_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_count_range_const_true(d, p)?;
    declare_coprime_mul_iff_of_dvd(d, p)?;
    declare_totient_mul_of_dvd(d, p)?;
    declare_totient_pow_succ_of_prime(d, p)?;
    declare_totient_prime_pow(d, p)?;
    Ok(())
}
