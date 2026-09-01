//! `int-prime-dvd` lane: three `ml430` mirrors about a `Nat`-prime dividing
//! an `Int` product.
//!
//! - [`declare_prime_dvd_mul_prime`]: `Int.Prime.dvd_mul'`
//!   (`F:ml430-int-prime-dvd-mul-23b73e69`) — `↑p ∣ m*n → ↑p ∣ m ∨ ↑p ∣ n`,
//!   built by applying `gcd::declare_euclid_lemma`'s `Int.euclid_lemma`
//!   directly at `pr := ofNat p`. `Int.euclid_lemma`'s primality hypothesis
//!   is stated on `natAbs pr`, and `natAbs (ofNat p) ≡ p` by `rfl`
//!   (`nat_abs.rs`'s own doc comment: `Int.natAbs (ofNat n) ≡ n`), so the
//!   `Nat.Prime p` hypothesis this mirror states is *definitionally* the one
//!   `euclid_lemma` consumes — no transport needed, a bare application.
//! - [`declare_prime_dvd_mul`]: `Int.Prime.dvd_mul`
//!   (`F:ml430-int-prime-dvd-mul-90351ba0`) — the same statement with each
//!   disjunct dropped from `Int.dvd` to `Nat.dvd` via `natAbs`, using
//!   `gcd::declare_nat_abs_dvd_nat_abs_of_dvd` (`a ∣ b → natAbs a ∣ natAbs
//!   b`) on each branch of the `Or` `euclid_lemma` returns.
//! - [`declare_not_prime_of_int_mul`]: `Int.not_prime_of_int_mul`
//!   (`F:ml430-int-not-prime-of-int-mul-e3060f5d`) — if neither factor's
//!   magnitude is `1`, the product (cast to `Int` from a `Nat` `c`) is not
//!   prime. Reduces to a `Nat` fact about `x := natAbs a`, `y := natAbs b`:
//!   `x ≠ 1 → y ≠ 1 → ¬prime_condition(x*y)`, proved by case-splitting `x`
//!   via `Nat.zero_or_succ`. At `x = 0`: `x*y = 0` (`Nat.zero_mul`), and
//!   `Nat.prime_ne_zero` applied at `0` gives `Not (Eq 0 0)`, contradicted by
//!   `Eq.refl 0`. At `x = succ k` (so `1 ≤ x`): `x` itself is the
//!   discriminating divisor for `Nat.not_prime_of_dvd_of_ne` — `x ∣ x*y`
//!   (`Nat.dvd_mul`), `x ≠ 1` (given), and `x ≠ x*y` because `x = x*y`
//!   together with `x*1 = x` (`Nat.mul_one`) and `1 ≤ x`
//!   (`Nat.mul_left_cancel_of_pos`) would force `y = 1`, contradicting the
//!   other hypothesis. The Nat-level fact is then transported to `c` along
//!   `natAbs(a*b) = natAbs(ofNat c) ≡ c` (via `gcd::declare_nat_abs_mul` and
//!   `IntDev::int_eq_rewrite` on the hypothesis `a*b = ofNat c`).
//!
//! No `Nat` declaration is added anywhere in this file — every `Nat`-level
//! fact used (`zero_or_succ`, `zero_mul`, `mul_one`,
//! `mul_left_cancel_of_pos`, `dvd_mul`, `prime_ne_zero`,
//! `not_prime_of_dvd_of_ne`) already existed in `nat_prelude`, per the
//! `int-prime-dvd` lane's boundary with the sibling `nat-prime-factorial-lcm`
//! lane.

use super::dvd::idvd;
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.natAbs a`, local per-module convention (matches every other
/// `int_prelude` module rather than importing a shared helper).
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let name = d.int().nat_abs;
    d.const_app(name, &[a])
}

/// `fun n => 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n` — this development's
/// inline primality convention (no `Prime` name exists over either carrier),
/// applied at a `Nat`-typed `n` (unlike `gcd.rs`'s `euclid_lemma`, which
/// states it on `natAbs pr` for an `Int`-typed `pr`).
fn prime_condition_nat(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let divisor_clause = |d: &mut IntDev<'_>| -> ExprId {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hyp = d.dvd(x, n);
        let one_nat = d.num(1);
        let is_one = d.eq(x, one_nat);
        let is_self = d.eq(x, n);
        let disjunction = d.or(is_one, is_self);
        let inner = d.arrow(hyp, disjunction);
        let nat = d.nat_ty();
        d.pi_fv(x_fv, nat, inner)
    };
    let two = d.num(2);
    let two_le = d.le(two, n);
    let clause = divisor_clause(d);
    d.and(two_le, clause)
}

/// `Int.prime_dvd_mul' : ∀ (m n : Int) (p : Nat), (2 ≤ p ∧ ∀ d, d ∣ p → d = 1
/// ∨ d = p) → ofNat p ∣ m*n → ofNat p ∣ m ∨ ofNat p ∣ n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_prime_dvd_mul_prime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let name = p.prime_dvd_mul_prime;
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let p_fv = d.fresh_fvar();
    let pvar = d.kernel().fvar(p_fv);

    let prime_ty = prime_condition_nat(d, pvar);
    let of_p = d.of_nat(pvar);
    let mn = d.imul(m, n);
    let divides_product = idvd(d, of_p, mn);
    let divides_m = idvd(d, of_p, m);
    let divides_n = idvd(d, of_p, n);
    let conclusion = d.or(divides_m, divides_n);

    let stmt_body = {
        let inner = d.arrow(divides_product, conclusion);
        d.arrow(prime_ty, inner)
    };
    let stmt = {
        let s1 = d.pi_fv(p_fv, nat, stmt_body);
        let s2 = d.pi_fv(n_fv, int_ty, s1);
        d.pi_fv(m_fv, int_ty, s2)
    };

    let prime_hyp_fv = d.fresh_fvar();
    let prime_hyp = d.kernel().fvar(prime_hyp_fv);
    let prod_hyp_fv = d.fresh_fvar();
    let prod_hyp = d.kernel().fvar(prod_hyp_fv);

    let euclid_const = d.kernel().const_(p.euclid_lemma, vec![]);
    let applied = d.apply(euclid_const, &[of_p, m, n, prime_hyp, prod_hyp]);

    let value_body = {
        let inner = d.lam_fv(prod_hyp_fv, divides_product, applied);
        d.lam_fv(prime_hyp_fv, prime_ty, inner)
    };
    let value = {
        let v1 = d.lam_fv(p_fv, nat, value_body);
        let v2 = d.lam_fv(n_fv, int_ty, v1);
        d.lam_fv(m_fv, int_ty, v2)
    };

    d.declare_theorem(name, stmt, value)?;
    Ok(())
}

/// `Int.prime_dvd_mul : ∀ (m n : Int) (p : Nat), (2 ≤ p ∧ ∀ d, d ∣ p → d = 1
/// ∨ d = p) → ofNat p ∣ m*n → p ∣ natAbs m ∨ p ∣ natAbs n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_prime_dvd_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let name = p.prime_dvd_mul;
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let p_fv = d.fresh_fvar();
    let pvar = d.kernel().fvar(p_fv);

    let prime_ty = prime_condition_nat(d, pvar);
    let of_p = d.of_nat(pvar);
    let mn = d.imul(m, n);
    let divides_product = idvd(d, of_p, mn);

    let big_m = nat_abs(d, m);
    let big_n = nat_abs(d, n);
    let divides_m_nat = d.dvd(pvar, big_m);
    let divides_n_nat = d.dvd(pvar, big_n);
    let conclusion = d.or(divides_m_nat, divides_n_nat);

    let stmt_body = {
        let inner = d.arrow(divides_product, conclusion);
        d.arrow(prime_ty, inner)
    };
    let stmt = {
        let s1 = d.pi_fv(p_fv, nat, stmt_body);
        let s2 = d.pi_fv(n_fv, int_ty, s1);
        d.pi_fv(m_fv, int_ty, s2)
    };

    let prime_hyp_fv = d.fresh_fvar();
    let prime_hyp = d.kernel().fvar(prime_hyp_fv);
    let prod_hyp_fv = d.fresh_fvar();
    let prod_hyp = d.kernel().fvar(prod_hyp_fv);

    let divides_m_int = idvd(d, of_p, m);
    let divides_n_int = idvd(d, of_p, n);
    let euclid_const = d.kernel().const_(p.euclid_lemma, vec![]);
    let euclid_result = d.apply(euclid_const, &[of_p, m, n, prime_hyp, prod_hyp]);

    let on_left = &|d: &mut IntDev<'_>, hm: ExprId| -> ExprId {
        let bridged = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_p, m, hm]);
        d.or_inl(divides_m_nat, divides_n_nat, bridged)
    };
    let on_right = &|d: &mut IntDev<'_>, hn: ExprId| -> ExprId {
        let bridged = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[of_p, n, hn]);
        d.or_inr(divides_m_nat, divides_n_nat, bridged)
    };
    let result = d.or_elim(
        divides_m_int,
        divides_n_int,
        conclusion,
        euclid_result,
        on_left,
        on_right,
    );

    let value_body = {
        let inner = d.lam_fv(prod_hyp_fv, divides_product, result);
        d.lam_fv(prime_hyp_fv, prime_ty, inner)
    };
    let value = {
        let v1 = d.lam_fv(p_fv, nat, value_body);
        let v2 = d.lam_fv(n_fv, int_ty, v1);
        d.lam_fv(m_fv, int_ty, v2)
    };

    d.declare_theorem(name, stmt, value)?;
    Ok(())
}

/// `Not (prime_condition_nat (mul x y))`, given `x_ne1 : Not (Eq x one)` and
/// `y_ne1 : Not (Eq y one)`.
///
/// Case-splits on `x` via `Nat.zero_or_succ`. Uses only pre-existing `Nat`
/// declarations — see the module doc.
fn not_prime_of_ne_one_ne_one(
    d: &mut IntDev<'_>,
    x: ExprId,
    y: ExprId,
    x_ne1: ExprId,
    y_ne1: ExprId,
) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let one = d.num(1);
    let zero = d.zero();
    let mul_xy = d.mul(x, y);
    let pc_mul_xy = prime_condition_nat(d, mul_xy);

    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    let false_ty = d.false_ty();

    // `x = 0 ∨ ∃ pred, x = succ pred`
    let disjunction = d.lemma(p.nat.zero_or_succ, &[x]);
    let eq_x_zero = d.eq(x, zero);
    let predicate = {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let succ_pred = d.succ(pred);
        let body = d.eq(x, succ_pred);
        d.lam_fv(pred_fv, nat, body)
    };
    let exists_right = {
        let one_lv = d.level_one();
        let exists_const = d.kernel().const_(p.logic.exists_, vec![one_lv]);
        d.apply(exists_const, &[nat, predicate])
    };

    let on_left = &|d: &mut IntDev<'_>, h0: ExprId| -> ExprId {
        // h0 : Eq x zero
        let mul_zero_y = d.mul(zero, y);
        let step1 = d.congr(x, zero, h0, &|d, t| d.mul(t, y));
        let step2 = d.lemma(p.nat.zero_mul, &[y]);
        let eq_mul_zero = d.trans(mul_xy, mul_zero_y, zero, step1, step2);

        let motive_pc = d.eq_motive(mul_xy, &|d, v| prime_condition_nat(d, v));
        let pc_at_zero = d.transport(mul_xy, motive_pc, hp, zero, eq_mul_zero);
        let ne_zero_fn = d.lemma(p.nat.prime_ne_zero, &[zero]);
        let not_eq = d.apply(ne_zero_fn, &[pc_at_zero]);
        let refl_zero = d.refl(zero);
        d.apply(not_eq, &[refl_zero])
    };

    let on_right = &|d: &mut IntDev<'_>, h_succ: ExprId| -> ExprId {
        let minor = {
            let pred_fv = d.fresh_fvar();
            let pred = d.kernel().fvar(pred_fv);
            let succ_pred = d.succ(pred);
            let heq_ty = d.eq(x, succ_pred);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);

            // `Le one x`, from `zero_lt_succ pred : Le one (succ pred)`
            // transported along `succ_pred = x`.
            let one_le_succ_pred = d.zero_lt_succ(pred);
            let symm_heq = d.symm(x, succ_pred, heq);
            let motive_le = d.eq_motive(succ_pred, &|d, v| d.le(one, v));
            let one_le_x = d.transport(succ_pred, motive_le, one_le_succ_pred, x, symm_heq);

            // Assume `x = x*y`, derive `y = 1`, contradict `y_ne1`.
            let eq_x_mul_xy_ty = d.eq(x, mul_xy);
            let heq2_fv = d.fresh_fvar();
            let heq2 = d.kernel().fvar(heq2_fv);
            let ne_x_mul_xy = {
                let x_mul_one = d.mul(x, one);
                let mul_one_eq_x = d.lemma(p.nat.mul_one, &[x]);
                let eq_x1_xy = d.trans(x_mul_one, x, mul_xy, mul_one_eq_x, heq2);
                let cancel = d.lemma(p.nat.mul_left_cancel_of_pos, &[x, one, y, one_le_x, eq_x1_xy]);
                let y_eq_1 = d.symm(one, y, cancel);
                let false2 = d.apply(y_ne1, &[y_eq_1]);
                d.lam_fv(heq2_fv, eq_x_mul_xy_ty, false2)
            };

            let x_dvd_mul_xy = d.lemma(p.nat.dvd_mul, &[x, y]);
            let not_prime_mul_xy = d.lemma(
                p.nat.not_prime_of_dvd_of_ne,
                &[x, mul_xy, x_dvd_mul_xy, x_ne1, ne_x_mul_xy],
            );
            let false_final = d.apply(not_prime_mul_xy, &[hp]);

            let with_heq = d.lam_fv(heq_fv, heq_ty, false_final);
            d.lam_fv(pred_fv, nat, with_heq)
        };
        super::ops::exists_elim(d, predicate, false_ty, h_succ, minor)
    };

    let result = d.or_elim(eq_x_zero, exists_right, false_ty, disjunction, on_left, on_right);
    d.lam_fv(hp_fv, pc_mul_xy, result)
}

/// `Int.not_prime_of_int_mul : ∀ (a b : Int) (c : Nat), natAbs a ≠ 1 →
/// natAbs b ≠ 1 → a*b = ofNat c → ¬(2 ≤ c ∧ ∀ d, d ∣ c → d = 1 ∨ d = c)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_not_prime_of_int_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let name = p.not_prime_of_int_mul;
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let one_nat = d.num(1);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let big_a = nat_abs(d, a);
    let big_b = nat_abs(d, b);
    let a_ne1_ty = {
        let e = d.eq(big_a, one_nat);
        d.not(e)
    };
    let b_ne1_ty = {
        let e = d.eq(big_b, one_nat);
        d.not(e)
    };
    let ab = d.imul(a, b);
    let of_c = d.of_nat(c);
    let eq_ty = d.ieq(ab, of_c);
    let pc_c = prime_condition_nat(d, c);
    let concl = d.not(pc_c);

    let stmt_body = {
        let s1 = d.arrow(eq_ty, concl);
        let s2 = d.arrow(b_ne1_ty, s1);
        d.arrow(a_ne1_ty, s2)
    };
    let stmt = {
        let s1 = d.pi_fv(c_fv, nat, stmt_body);
        let s2 = d.pi_fv(b_fv, int_ty, s1);
        d.pi_fv(a_fv, int_ty, s2)
    };

    let a_ne1_fv = d.fresh_fvar();
    let a_ne1 = d.kernel().fvar(a_ne1_fv);
    let b_ne1_fv = d.fresh_fvar();
    let b_ne1 = d.kernel().fvar(b_ne1_fv);
    let eq_fv = d.fresh_fvar();
    let eq_hyp = d.kernel().fvar(eq_fv);

    let not_prime_mul = not_prime_of_ne_one_ne_one(d, big_a, big_b, a_ne1, b_ne1);

    // Eq Nat (mul big_a big_b) c.
    let eq_mul_c = {
        let mul_big = d.mul(big_a, big_b);
        let natabs_ab = nat_abs(d, ab);
        let nat_abs_mul_eq = d.lemma(p.nat_abs_mul, &[a, b]); // Eq (natAbs ab) (mul big_a big_b)
        let step1 = d.symm(natabs_ab, mul_big, nat_abs_mul_eq); // Eq (mul big_a big_b) (natAbs ab)

        let proof_at_ab = d.refl(natabs_ab);
        let motive_natabs = |d: &mut IntDev<'_>, t: ExprId| {
            let nt = nat_abs(d, t);
            d.eq(natabs_ab, nt)
        };
        let eq_natabs_ab_c = d.int_eq_rewrite(ab, of_c, eq_hyp, proof_at_ab, &motive_natabs);
        d.trans(mul_big, natabs_ab, c, step1, eq_natabs_ab_c)
    };

    let mul_big = d.mul(big_a, big_b);
    let motive_not_pc = d.eq_motive(mul_big, &|d, v| {
        let pcv = prime_condition_nat(d, v);
        d.not(pcv)
    });
    let final_not_prime = d.transport(mul_big, motive_not_pc, not_prime_mul, c, eq_mul_c);

    let value_body = {
        let inner = d.lam_fv(eq_fv, eq_ty, final_not_prime);
        let with_b = d.lam_fv(b_ne1_fv, b_ne1_ty, inner);
        d.lam_fv(a_ne1_fv, a_ne1_ty, with_b)
    };
    let value = {
        let v1 = d.lam_fv(c_fv, nat, value_body);
        let v2 = d.lam_fv(b_fv, int_ty, v1);
        d.lam_fv(a_fv, int_ty, v2)
    };

    d.declare_theorem(name, stmt, value)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.gcd_ne_one_iff_gcd_mul_right_ne_one` — needs one classical step
// (deciding `Eq Nat _ _`), derived from `Nat.beq`'s soundness/completeness,
// never assumed. Local copies of `bool_true_or_false`/`nat_decidable_equality`
// (the same construction `int_prelude::decide` builds privately for
// `Int.eq_em`) and of the `iff_trans`/`Not`-transport combinators every
// `Iff`-shaped module in this crate keeps its own copy of, per this
// repository's documented "local copy" convention
// (`nat_prelude/dvd_add_iff_left.rs`, `gcd_dvd_mirrors.rs`,
// `gcd_mul_right_mirrors.rs`).
// ---------------------------------------------------------------------------

/// `Or (Eq Bool c Bool.true) (Eq Bool c Bool.false)` for any Bool-valued `c`.
fn bool_true_or_false(d: &mut IntDev<'_>, c: ExprId) -> ExprId {
    let p = d.int();
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let is_true = d.bool_eq(x, true_);
        let is_false = d.bool_eq(x, false_);
        let body = d.or(is_true, is_false);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let is_true = d.bool_eq(true_, true_);
        let is_false = d.bool_eq(true_, false_);
        let refl_true = d.bool_refl(true_);
        d.or_inl(is_true, is_false, refl_true)
    };
    let case_false = {
        let is_true = d.bool_eq(false_, true_);
        let is_false = d.bool_eq(false_, false_);
        let refl_false = d.bool_refl(false_);
        d.or_inr(is_true, is_false, refl_false)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, c])
}

/// `Or (Eq Nat m n) (Not (Eq Nat m n))` — decidable `Nat` equality, from
/// `Nat.beq`'s already-proved soundness and completeness. This is *not*
/// propositional excluded middle: it is derived per-pair from `Nat.beq`
/// exactly as `int_prelude::decide::declare_decidable_equality` derives
/// `Int.eq_em`, never assumed.
fn nat_decidable_equality(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let scrutinee = d.beq(m, n);
    let true_value = d.bool_true();
    let false_value = d.bool_false();
    let is_true = d.bool_eq(scrutinee, true_value);
    let is_false = d.bool_eq(scrutinee, false_value);
    let equal = d.eq(m, n);
    let distinct = d.not(equal);
    let goal = d.or(equal, distinct);
    let decision = bool_true_or_false(d, scrutinee);

    d.or_elim(
        is_true,
        is_false,
        goal,
        decision,
        &|d, holds| {
            let sound = d.int().nat.eq_of_beq_eq_true;
            let witness = d.const_app(sound, &[m, n, holds]);
            d.or_inl(equal, distinct, witness)
        },
        &|d, fails| {
            let fv = d.fresh_fvar();
            let assumed = d.kernel().fvar(fv);
            let complete = d.int().nat.beq_eq_true_of_eq;
            let forced = d.const_app(complete, &[m, n, assumed]);
            let reversed = d.bool_symm(scrutinee, false_value, fails);
            let clash = d.bool_trans(false_value, scrutinee, true_value, reversed, forced);
            let false_ty = d.false_ty();
            let contradiction = d.false_true_elim(false_ty, clash);
            let refutation = d.lam_fv(fv, equal, contradiction);
            d.or_inr(equal, distinct, refutation)
        },
    )
}

/// `h : Iff a b ⊢ Iff (Not a) (Not b)` — purely intuitionistic, no
/// decidability needed.
fn not_iff(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let logic = d.int().logic;
    let not_a = d.not(a);
    let not_b = d.not(b);
    let mp = {
        let na_fv = d.fresh_fvar();
        let na = d.kernel().fvar(na_fv);
        let b_fv = d.fresh_fvar();
        let bv = d.kernel().fvar(b_fv);
        let mpr_ab = d.const_app(logic.iff_mpr, &[a, b, h]);
        let a_from_b = d.apply(mpr_ab, &[bv]);
        let false_ = d.apply(na, &[a_from_b]);
        let inner = d.lam_fv(b_fv, b, false_);
        d.lam_fv(na_fv, not_a, inner)
    };
    let mpr = {
        let nb_fv = d.fresh_fvar();
        let nb = d.kernel().fvar(nb_fv);
        let a_fv = d.fresh_fvar();
        let av = d.kernel().fvar(a_fv);
        let mp_ab = d.const_app(logic.iff_mp, &[a, b, h]);
        let b_from_a = d.apply(mp_ab, &[av]);
        let false_ = d.apply(nb, &[b_from_a]);
        let inner = d.lam_fv(a_fv, a, false_);
        d.lam_fv(nb_fv, not_b, inner)
    };
    d.const_app(logic.iff_intro, &[not_a, not_b, mp, mpr])
}

/// `h1 : Iff a b, h2 : Iff b c ⊢ Iff a c`.
fn iff_trans(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
    let logic = d.int().logic;
    let mp = {
        let a_fv = d.fresh_fvar();
        let av = d.kernel().fvar(a_fv);
        let h1_mp = d.const_app(logic.iff_mp, &[a, b, h1]);
        let b_from_a = d.apply(h1_mp, &[av]);
        let h2_mp = d.const_app(logic.iff_mp, &[b, c, h2]);
        let c_from_b = d.apply(h2_mp, &[b_from_a]);
        d.lam_fv(a_fv, a, c_from_b)
    };
    let mpr = {
        let c_fv = d.fresh_fvar();
        let cv = d.kernel().fvar(c_fv);
        let h2_mpr = d.const_app(logic.iff_mpr, &[b, c, h2]);
        let b_from_c = d.apply(h2_mpr, &[cv]);
        let h1_mpr = d.const_app(logic.iff_mpr, &[a, b, h1]);
        let a_from_b = d.apply(h1_mpr, &[b_from_c]);
        d.lam_fv(c_fv, c, a_from_b)
    };
    d.const_app(logic.iff_intro, &[a, c, mp, mpr])
}

/// `Iff (Not (And q1 q2)) (Or (Not q1) (Not q2))`, given `decision : Or q1
/// (Not q1)`.
///
/// `mpr` (`Or (Not q1) (Not q2) → Not (And q1 q2)`) is purely intuitionistic;
/// `mp` needs `decision` — the one classical step this whole theorem uses.
fn not_and_iff_or_not(d: &mut IntDev<'_>, q1: ExprId, q2: ExprId, decision: ExprId) -> ExprId {
    let logic = d.int().logic;
    let and_ty = d.and(q1, q2);
    let not_and_ty = d.not(and_ty);
    let not_q1 = d.not(q1);
    let not_q2 = d.not(q2);
    let or_ty = d.or(not_q1, not_q2);

    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = {
            let on_left = &|d: &mut IntDev<'_>, hq1: ExprId| -> ExprId {
                let and_intro = d.int().logic.and_intro;
                let nq2 = {
                    let q2_fv = d.fresh_fvar();
                    let q2v = d.kernel().fvar(q2_fv);
                    let and_proof = d.const_app(and_intro, &[q1, q2, hq1, q2v]);
                    let false_ = d.apply(h, &[and_proof]);
                    d.lam_fv(q2_fv, q2, false_)
                };
                d.or_inr(not_q1, not_q2, nq2)
            };
            let on_right = &|d: &mut IntDev<'_>, hnq1: ExprId| -> ExprId {
                d.or_inl(not_q1, not_q2, hnq1)
            };
            d.or_elim(q1, not_q1, or_ty, decision, on_left, on_right)
        };
        d.lam_fv(h_fv, not_and_ty, body)
    };
    let mpr = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = {
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let inner = {
                let on_left = &|d: &mut IntDev<'_>, nq1: ExprId| -> ExprId {
                    let q1_proof = d.and_left(q1, q2, hand);
                    d.apply(nq1, &[q1_proof])
                };
                let on_right = &|d: &mut IntDev<'_>, nq2: ExprId| -> ExprId {
                    let q2_proof = d.and_right(q1, q2, hand);
                    d.apply(nq2, &[q2_proof])
                };
                let false_ty = d.false_ty();
                d.or_elim(not_q1, not_q2, false_ty, h, on_left, on_right)
            };
            d.lam_fv(hand_fv, and_ty, inner)
        };
        d.lam_fv(h_fv, or_ty, body)
    };
    d.const_app(logic.iff_intro, &[not_and_ty, or_ty, mp, mpr])
}

/// `Int.gcd_ne_one_iff_gcd_mul_right_ne_one : ∀ (a : Int) (m n : Nat), Iff
/// (Not (Eq (gcd a (ofNat m * ofNat n)) one)) (Or (Not (Eq (gcd a (ofNat m))
/// one)) (Not (Eq (gcd a (ofNat n)) one)))`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_gcd_ne_one_iff_gcd_mul_right_ne_one(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    let name = p.gcd_ne_one_iff_gcd_mul_right_ne_one;
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let one = d.num(1);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let of_m = d.of_nat(m);
    let of_n = d.of_nat(n);
    let mn_int = d.imul(of_m, of_n);

    let gcd_a_mn = d.const_app(p.gcd, &[a, mn_int]);
    let gcd_a_m = d.const_app(p.gcd, &[a, of_m]);
    let gcd_a_n = d.const_app(p.gcd, &[a, of_n]);

    let lhs_ty = {
        let e = d.eq(gcd_a_mn, one);
        d.not(e)
    };
    let rhs1 = {
        let e = d.eq(gcd_a_m, one);
        d.not(e)
    };
    let rhs2 = {
        let e = d.eq(gcd_a_n, one);
        d.not(e)
    };
    let rhs_ty = d.or(rhs1, rhs2);

    let stmt_body = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    let stmt = {
        let s1 = d.pi_fv(n_fv, nat, stmt_body);
        let s2 = d.pi_fv(m_fv, nat, s1);
        d.pi_fv(a_fv, int_ty, s2)
    };

    // Proof, built at Nat from `x := natAbs a`; the whole thing typechecks
    // against the `Int.gcd`-stated `stmt` above by `rfl` (`Int.gcd a b`
    // unfolds to `Nat.gcd (natAbs a) (natAbs b)`, and `natAbs (ofNat k)`
    // unfolds to `k`).
    let x = nat_abs(d, a);
    let mul_mn = d.mul(m, n);
    let gcd_x_mn = d.gcd(x, mul_mn);
    let p_ty = d.eq(gcd_x_mn, one);
    let gcd_x_m = d.gcd(x, m);
    let gcd_x_n = d.gcd(x, n);
    let q1 = d.eq(gcd_x_m, one);
    let q2 = d.eq(gcd_x_n, one);
    let q_ty = d.and(q1, q2);

    let base_iff = d.lemma(p.nat.coprime_mul_iff, &[x, m, n]);
    let not_p_iff_not_q = not_iff(d, p_ty, q_ty, base_iff);

    let decision = nat_decidable_equality(d, gcd_x_m, one);
    let not_q_iff_or = not_and_iff_or_not(d, q1, q2, decision);

    let not_p_ty = d.not(p_ty);
    let not_q_ty = d.not(q_ty);
    let not_q1 = d.not(q1);
    let not_q2 = d.not(q2);
    let or_not_ty = d.or(not_q1, not_q2);

    let final_iff = iff_trans(d, not_p_ty, not_q_ty, or_not_ty, not_p_iff_not_q, not_q_iff_or);

    let value_body = final_iff;
    let value = {
        let v1 = d.lam_fv(n_fv, nat, value_body);
        let v2 = d.lam_fv(m_fv, nat, v1);
        d.lam_fv(a_fv, int_ty, v2)
    };

    d.declare_theorem(name, stmt, value)?;
    Ok(())
}
