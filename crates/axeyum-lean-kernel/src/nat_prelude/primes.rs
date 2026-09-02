//! Primality over `Nat`: the **least divisor `≥ 2`** construction and the
//! theorem it exists for — every `m ≥ 2` has a prime divisor.
//!
//! This is the second of the two ingredients `F:nat-exists-prime-gt` (Euclid's
//! theorem) was missing; the first, `dvd_factorial_of_le`, is in
//! [`super::divisibility`].
//!
//! Primality is spelled **inline** as `2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`,
//! matching `F:nat-euclid-lemma` and `F:nat-exists-prime-gt`, because the
//! prelude has no `Prime` predicate and a fact is only closed by the statement
//! it actually makes.
//!
//! ## Why there is no well-founded recursion here
//!
//! The obvious route is strong induction on `m` through `lt_well_founded`:
//! either `m` is prime, or it splits and the induction hypothesis applies to a
//! proper divisor. That route needs to *decide* primality of `m`, which is a
//! bounded `∀` — and deciding a bounded `∀` constructively is itself a bounded
//! search. So the search is done directly, by ordinary `Nat.rec` on the bound,
//! and it returns the **least** divisor `≥ 2` rather than any divisor. Least is
//! what makes primality free: a proper divisor of the least one would be a
//! smaller divisor of `m`.
//!
//! Nothing here is classical. `dvd d m` is decided at each step by reducing
//! `Nat.beq (Nat.mod m d) 0`, whose two branches are separated by the checked
//! `div_mod_remainder_eq_zero_iff_dvd`.

use super::NatPrelude;
use super::finite::{ne_of_lt, ne_symm, pos_implies_succ_pred};
use super::helpers::{
    and_left, and_right, iff_forward, iff_reverse, transport_dvd_left, transport_dvd_right,
};
use super::ops::{
    NatDev, NatOps, bool_true_or_false, cases_lt_bound_absurd, cases_lt_or_ge,
    two_divisor_dichotomy, two_mul_eq_add_self,
};
use super::steps::absurd;
use super::steps::dvd_elim;
use super::steps::or_cases;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `∀ e, 2 ≤ e → e < x → ¬ (e ∣ m)` — the minimality side condition carried by
/// the least-divisor search.
pub(super) fn min_condition(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let lower = d.le(two, e);
    let strict = d.lt(e, x);
    let divides = d.dvd(e, m);
    let not_divides = d.const_app(p.logic.not, &[divides]);
    let inner = d.arrow(strict, not_divides);
    let body = d.arrow(lower, inner);
    d.pi_fv(e_fv, nat, body)
}

/// `fun x => 2 ≤ x ∧ (x ∣ m ∧ ∀ e, 2 ≤ e → e < x → ¬ (e ∣ m))`.
fn least_predicate(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let two = d.num(2);
    let lower = d.le(two, x);
    let divides = d.dvd(x, m);
    let minimal = min_condition(d, p, m, x);
    let tail = d.const_app(p.logic.and, &[divides, minimal]);
    let body = d.const_app(p.logic.and, &[lower, tail]);
    d.lam_fv(x_fv, nat, body)
}

/// `∃ x, 2 ≤ x ∧ (x ∣ m ∧ ∀ e, 2 ≤ e → e < x → ¬ (e ∣ m))`.
fn least_found(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = least_predicate(d, p, m);
    let exists = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(exists, &[nat, predicate])
}

/// `∀ c, 2 ≤ c → c ≤ k → ¬ (c ∣ m)` — nothing in `[2, k]` divides `m`.
fn none_up_to(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let lower = d.le(two, c);
    let upper = d.le(c, k);
    let divides = d.dvd(c, m);
    let not_divides = d.const_app(p.logic.not, &[divides]);
    let inner = d.arrow(upper, not_divides);
    let body = d.arrow(lower, inner);
    d.pi_fv(c_fv, nat, body)
}

/// The search's disjunction at bound `k`: either the least divisor `≥ 2` has
/// already been found, or nothing in `[2, k]` divides `m`.
fn search_claim(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, k: ExprId) -> ExprId {
    let found = least_found(d, p, m);
    let none = none_up_to(d, p, m, k);
    d.const_app(p.logic.or, &[found, none])
}

/// `2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x` — primality, spelled inline.
pub(super) fn prime_condition(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let unit = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hypothesis = d.dvd(c, x);
    let trivial = d.eq(c, unit);
    let whole = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
    let body = d.arrow(hypothesis, disjunction);
    let divisors = d.pi_fv(c_fv, nat, body);
    d.const_app(p.logic.and, &[lower, divisors])
}

/// `fun x => (2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x) ∧ x ∣ m`.
fn prime_divisor_predicate(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let prime = prime_condition(d, p, x);
    let divides = d.dvd(x, m);
    let body = d.const_app(p.logic.and, &[prime, divides]);
    d.lam_fv(x_fv, nat, body)
}

/// `le_of_dvd`, `two_le_succ_or_eq_one`, `least_divisor_search`, and
/// `exists_prime_dvd`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_primes(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();

    // le_of_dvd : ∀ a n, 1 ≤ n → a ∣ n → a ≤ n
    //
    // A divisor of a POSITIVE number is bounded by it. `a ∣ n` gives `n = a*q`;
    // `n` positive forces `q` positive (`one_le_right_of_mul`), so
    // `a = a*1 ≤ a*q = n` by left monotonicity of multiplication. The
    // positivity hypothesis is not decoration: `2 ∣ 0` and `0` is not `≥ 2`.
    d.theorem(p.le_of_dvd, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let unit = d.num(1);
        let positive_ty = d.le(unit, n);
        let divides_ty = d.dvd(a, n);
        let conclusion = d.le(a, n);
        let stmt = {
            let inner = d.arrow(divides_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);

        let predicate = d.dvd_predicate(a, n);
        let anon = d.anon_name();
        let motive = d
            .kernel()
            .lam(anon, divides_ty, conclusion, BinderInfo::Default);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let product = d.mul(a, q);
            let equation_fv = d.fresh_fvar();
            let equation_ty = d.eq(n, product);
            let equation = d.kernel().fvar(equation_fv);

            // 1 ≤ n, transported along n = a*q, gives 1 ≤ a*q, hence 1 ≤ q.
            let product_positive = {
                let motive = d.eq_motive(n, &|d, x| {
                    let unit = d.num(1);
                    d.le(unit, x)
                });
                d.transport(n, motive, positive, product, equation)
            };
            let q_positive = d.lemma(p.one_le_right_of_mul, &[a, q, product_positive]);

            // a*1 ≤ a*q, then rewrite a*1 to a and a*q back to n.
            let scaled = d.lemma(p.mul_le_mul_left, &[a, unit, q, q_positive]);
            let a_times_one = d.mul(a, unit);
            let collapse = d.lemma(p.mul_one, &[a]);
            let bounded_by_product = {
                let motive = d.eq_motive(a_times_one, &|d, x| d.le(x, product));
                d.transport(a_times_one, motive, scaled, a, collapse)
            };
            let reversed = d.symm(n, product, equation);
            let body = {
                let motive = d.eq_motive(product, &|d, x| d.le(a, x));
                d.transport(product, motive, bounded_by_product, n, reversed)
            };
            let with_equation = d.lam_fv(equation_fv, equation_ty, body);
            d.lam_fv(q_fv, nat, with_equation)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(exists_rec, &[nat, predicate, motive, minor, divides]);
        let with_divides = d.lam_fv(divides_fv, divides_ty, body);
        let proof = d.lam_fv(positive_fv, positive_ty, with_divides);
        (stmt, proof)
    })?;

    // two_le_succ_or_eq_one : ∀ j, 2 ≤ succ j ∨ succ j = 1
    //
    // The only successor below 2 is 1. Case analysis on `j` alone — the
    // induction hypothesis is unused — which is exactly the dichotomy the
    // divisor search needs before it may offer `succ j` as a witness.
    d.theorem(p.two_le_succ_or_eq_one, 1, &|d, v| {
        let j = v[0];
        let sj = d.succ(j);
        let two = d.num(2);
        let unit = d.num(1);
        let big_ty = d.le(two, sj);
        let small_ty = d.eq(sj, unit);
        let stmt = d.const_app(p.logic.or, &[big_ty, small_ty]);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let sx = d.succ(x);
            let two = d.num(2);
            let unit = d.num(1);
            let big = d.le(two, sx);
            let small = d.eq(sx, unit);
            d.const_app(p.logic.or, &[big, small])
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let szero = d.succ(zero);
            let two = d.num(2);
            let unit = d.num(1);
            let big = d.le(two, szero);
            let small = d.eq(szero, unit);
            let proof = d.refl(szero);
            d.const_app(p.logic.or_inr, &[big, small, proof])
        };
        let at_succ = |d: &mut NatDev<'_>, i: ExprId, _ih: ExprId| {
            let si = d.succ(i);
            let ssi = d.succ(si);
            let zero = d.zero();
            let unit = d.num(1);
            let two = d.num(2);
            let big = d.le(two, ssi);
            let small = d.eq(ssi, unit);
            // 0 ≤ i, so 1 ≤ succ i, so 2 ≤ succ (succ i).
            let base = d.lemma(p.zero_le, &[i]);
            let stepped = d.lemma(p.le_succ_succ, &[zero, i, base]);
            let proof = d.lemma(p.le_succ_succ, &[unit, si, stepped]);
            d.const_app(p.logic.or_inl, &[big, small, proof])
        };
        let proof = d.induct(&claim, &at_zero, &at_succ, j);
        (stmt, proof)
    })?;

    // least_divisor_search :
    //   ∀ k m, (∃ x, 2 ≤ x ∧ (x ∣ m ∧ ∀ e, 2 ≤ e → e < x → ¬ (e ∣ m)))
    //          ∨ (∀ c, 2 ≤ c → c ≤ k → ¬ (c ∣ m))
    //
    // Ordinary `Nat.rec` on the bound `k`. The left disjunct carries NO bound on
    // the witness, so once found it is simply carried forward — the right
    // disjunct is the only half that grows with `k`.
    //
    //   zero      nothing is both ≥ 2 and ≤ 0.
    //   succ j    the induction hypothesis at `j` either already found the least
    //             divisor (carry it) or ruled out all of `[2, j]`. In the second
    //             case `two_le_succ_or_eq_one` first asks whether `succ j` is
    //             even a candidate; if `succ j = 1` the range `[2, succ j]` is
    //             still empty. Otherwise `succ j ∣ m` is DECIDED by reducing
    //             `beq (mod m (succ j)) 0`, the two branches separated by
    //             `div_mod_remainder_eq_zero_iff_dvd` applied to `div_mod_exec`:
    //               * divides — `succ j` is the witness, and its minimality is
    //                 precisely the right disjunct at `j`, since `e < succ j` is
    //                 `succ e ≤ succ j`;
    //               * does not — a `c` in `[2, succ j]` is either `< succ j`
    //                 (the hypothesis at `j` applies) or equal to `succ j` (the
    //                 branch's own non-divisibility, transported).
    d.theorem(p.least_divisor_search, 2, &|d, v| {
        let (k, m) = (v[0], v[1]);
        let stmt = search_claim(d, &p, m, k);

        let claim = |d: &mut NatDev<'_>, x: ExprId| search_claim(d, &p, m, x);

        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let found = least_found(d, &p, m);
            let none = none_up_to(d, &p, m, zero);
            let two = d.num(2);
            let unit = d.num(1);

            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let lower_ty = d.le(two, c);
            let lower_fv = d.fresh_fvar();
            let lower = d.kernel().fvar(lower_fv);
            let upper_ty = d.le(c, zero);
            let upper_fv = d.fresh_fvar();
            let upper = d.kernel().fvar(upper_fv);

            let two_le_zero = d.lemma(p.le_trans, &[two, c, zero, lower, upper]);
            let contradiction = d.lemma(p.not_succ_le_zero, &[unit, two_le_zero]);
            let goal = {
                let divides = d.dvd(c, m);
                d.const_app(p.logic.not, &[divides])
            };
            let body = absurd(d, goal, contradiction);
            let with_upper = d.lam_fv(upper_fv, upper_ty, body);
            let with_lower = d.lam_fv(lower_fv, lower_ty, with_upper);
            let none_proof = d.lam_fv(c_fv, nat, with_lower);
            d.const_app(p.logic.or_inr, &[found, none, none_proof])
        };

        let at_succ = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| {
            let sj = d.succ(j);
            let zero = d.zero();
            let two = d.num(2);
            let unit = d.num(1);
            let target = search_claim(d, &p, m, sj);
            let found = least_found(d, &p, m);
            let none_j = none_up_to(d, &p, m, j);
            let none_sj = none_up_to(d, &p, m, sj);

            // Already found at `j`: carry the witness unchanged.
            let carry = {
                let found_fv = d.fresh_fvar();
                let witness = d.kernel().fvar(found_fv);
                let body = d.const_app(p.logic.or_inl, &[found, none_sj, witness]);
                d.lam_fv(found_fv, found, body)
            };

            // Nothing in `[2, j]`: extend the range to `succ j`.
            let extend = {
                let none_fv = d.fresh_fvar();
                let none = d.kernel().fvar(none_fv);

                let big_ty = d.le(two, sj);
                let small_ty = d.eq(sj, unit);
                let dichotomy = d.lemma(p.two_le_succ_or_eq_one, &[j]);

                // `succ j = 1`: `[2, succ j]` is still empty.
                let degenerate = {
                    let small_fv = d.fresh_fvar();
                    let small = d.kernel().fvar(small_fv);
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let lower_ty = d.le(two, c);
                    let lower_fv = d.fresh_fvar();
                    let lower = d.kernel().fvar(lower_fv);
                    let upper_ty = d.le(c, sj);
                    let upper_fv = d.fresh_fvar();
                    let upper = d.kernel().fvar(upper_fv);

                    let upper_one = {
                        let motive = d.eq_motive(sj, &|d, x| d.le(c, x));
                        d.transport(sj, motive, upper, unit, small)
                    };
                    let two_le_one = d.lemma(p.le_trans, &[two, c, unit, lower, upper_one]);
                    let one_le_zero = d.lemma(p.le_of_succ_le_succ, &[unit, zero, two_le_one]);
                    let contradiction = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
                    let goal = {
                        let divides = d.dvd(c, m);
                        d.const_app(p.logic.not, &[divides])
                    };
                    let body = absurd(d, goal, contradiction);
                    let with_upper = d.lam_fv(upper_fv, upper_ty, body);
                    let with_lower = d.lam_fv(lower_fv, lower_ty, with_upper);
                    let none_proof = d.lam_fv(c_fv, nat, with_lower);
                    let injected = d.const_app(p.logic.or_inr, &[found, none_sj, none_proof]);
                    d.lam_fv(small_fv, small_ty, injected)
                };

                // `2 ≤ succ j`: decide `succ j ∣ m` by reduction.
                let candidate = {
                    let big_fv = d.fresh_fvar();
                    let big = d.kernel().fvar(big_fv);

                    let remainder = d.modulo(m, sj);
                    let quotient = d.div(m, sj);
                    let condition = d.beq(remainder, zero);
                    let exec = d.lemma(p.div_mod_exec, &[j, m]);
                    let specification = d.lemma(
                        p.div_mod_remainder_eq_zero_iff_dvd,
                        &[sj, m, quotient, remainder, exec],
                    );
                    let remainder_zero_ty = d.eq(remainder, zero);
                    let divides_ty = d.dvd(sj, m);
                    let forward = iff_forward(d, remainder_zero_ty, divides_ty, specification);
                    let reverse = iff_reverse(d, remainder_zero_ty, divides_ty, specification);

                    // `succ j` divides: it is the least such divisor.
                    let divides_branch = {
                        let witness_fv = d.fresh_fvar();
                        let witness = d.kernel().fvar(witness_fv);
                        let true_value = d.bool_true();
                        let witness_ty = d.bool_eq(condition, true_value);
                        let remainder_zero =
                            d.lemma(p.eq_of_beq_eq_true, &[remainder, zero, witness]);
                        let divides = d.apply(forward, &[remainder_zero]);

                        let minimal = {
                            let e_fv = d.fresh_fvar();
                            let e = d.kernel().fvar(e_fv);
                            let lower_ty = d.le(two, e);
                            let lower_fv = d.fresh_fvar();
                            let lower = d.kernel().fvar(lower_fv);
                            let strict_ty = d.lt(e, sj);
                            let strict_fv = d.fresh_fvar();
                            let strict = d.kernel().fvar(strict_fv);
                            // `e < succ j` IS `succ e ≤ succ j`.
                            let bounded = d.lemma(p.le_of_succ_le_succ, &[e, j, strict]);
                            let body = d.apply(none, &[e, lower, bounded]);
                            let with_strict = d.lam_fv(strict_fv, strict_ty, body);
                            let with_lower = d.lam_fv(lower_fv, lower_ty, with_strict);
                            d.lam_fv(e_fv, nat, with_lower)
                        };

                        let minimal_ty = min_condition(d, &p, m, sj);
                        let tail_ty = d.const_app(p.logic.and, &[divides_ty, minimal_ty]);
                        let tail = d.const_app(
                            p.logic.and_intro,
                            &[divides_ty, minimal_ty, divides, minimal],
                        );
                        let pair = d.const_app(p.logic.and_intro, &[big_ty, tail_ty, big, tail]);
                        let predicate = least_predicate(d, &p, m);
                        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                        let existential = d.apply(intro, &[nat, predicate, sj, pair]);
                        let injected = d.const_app(p.logic.or_inl, &[found, none_sj, existential]);
                        d.lam_fv(witness_fv, witness_ty, injected)
                    };

                    // `succ j` does not divide: the empty range extends.
                    let refutes_branch = {
                        let witness_fv = d.fresh_fvar();
                        let witness = d.kernel().fvar(witness_fv);
                        let false_value = d.bool_false();
                        let witness_ty = d.bool_eq(condition, false_value);

                        let not_divides = {
                            let assumed_fv = d.fresh_fvar();
                            let assumed = d.kernel().fvar(assumed_fv);
                            let remainder_zero = d.apply(reverse, &[assumed]);
                            let true_value = d.bool_true();
                            let holds =
                                d.lemma(p.beq_eq_true_of_eq, &[remainder, zero, remainder_zero]);
                            let flipped = d.bool_symm(condition, false_value, witness);
                            let impossible =
                                d.bool_trans(false_value, condition, true_value, flipped, holds);
                            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                            let body = d.false_true_elim(false_ty, impossible);
                            d.lam_fv(assumed_fv, divides_ty, body)
                        };

                        let c_fv = d.fresh_fvar();
                        let c = d.kernel().fvar(c_fv);
                        let lower_ty = d.le(two, c);
                        let lower_fv = d.fresh_fvar();
                        let lower = d.kernel().fvar(lower_fv);
                        let upper_ty = d.le(c, sj);
                        let upper_fv = d.fresh_fvar();
                        let upper = d.kernel().fvar(upper_fv);

                        let goal = {
                            let divides = d.dvd(c, m);
                            d.const_app(p.logic.not, &[divides])
                        };
                        let strict_ty = d.lt(c, sj);
                        let equal_ty = d.eq(c, sj);
                        let split = d.lemma(p.lt_or_eq_of_le, &[c, sj, upper]);
                        let strict_minor = {
                            let strict_fv = d.fresh_fvar();
                            let strict = d.kernel().fvar(strict_fv);
                            let bounded = d.lemma(p.le_of_succ_le_succ, &[c, j, strict]);
                            let body = d.apply(none, &[c, lower, bounded]);
                            d.lam_fv(strict_fv, strict_ty, body)
                        };
                        let equal_minor = {
                            let equal_fv = d.fresh_fvar();
                            let equal = d.kernel().fvar(equal_fv);
                            // The transport replaces `succ j` by `c`, so it needs
                            // the equation the other way round.
                            let reversed = d.symm(c, sj, equal);
                            let motive = d.eq_motive(sj, &|d, x| {
                                let divides = d.dvd(x, m);
                                d.const_app(p.logic.not, &[divides])
                            });
                            let body = d.transport(sj, motive, not_divides, c, reversed);
                            d.lam_fv(equal_fv, equal_ty, body)
                        };
                        let body = or_cases(
                            d,
                            strict_ty,
                            equal_ty,
                            goal,
                            strict_minor,
                            equal_minor,
                            split,
                        );
                        let with_upper = d.lam_fv(upper_fv, upper_ty, body);
                        let with_lower = d.lam_fv(lower_fv, lower_ty, with_upper);
                        let none_proof = d.lam_fv(c_fv, nat, with_lower);
                        let injected = d.const_app(p.logic.or_inr, &[found, none_sj, none_proof]);
                        d.lam_fv(witness_fv, witness_ty, injected)
                    };

                    // `Bool.rec` on the branch condition, with the condition's own
                    // reflexivity supplying the equation each branch consumes.
                    let bool_ty = d.bool_ty();
                    let motive = {
                        let selector_fv = d.fresh_fvar();
                        let selector = d.kernel().fvar(selector_fv);
                        let equation = d.bool_eq(condition, selector);
                        let body = d.arrow(equation, target);
                        d.lam_fv(selector_fv, bool_ty, body)
                    };
                    let level = d.kernel().level_zero();
                    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level]);
                    let selected = d.apply(
                        bool_rec,
                        &[motive, refutes_branch, divides_branch, condition],
                    );
                    let reflexivity = d.bool_refl(condition);
                    let body = d.apply(selected, &[reflexivity]);
                    d.lam_fv(big_fv, big_ty, body)
                };

                let body = or_cases(
                    d, big_ty, small_ty, target, candidate, degenerate, dichotomy,
                );
                d.lam_fv(none_fv, none_j, body)
            };

            or_cases(d, found, none_j, target, carry, extend, ih)
        };

        let proof = d.induct(&claim, &at_zero, &at_succ, k);
        (stmt, proof)
    })?;

    // exists_prime_dvd :
    //   ∀ m, 2 ≤ m → ∃ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) ∧ p ∣ m
    //
    // The second of the two ingredients `F:nat-exists-prime-gt` needs. Run the
    // search at bound `m` itself: its right disjunct claims nothing in `[2, m]`
    // divides `m`, which `dvd_refl` and `le_refl` refute outright, so the left
    // disjunct always fires and hands over the LEAST divisor `d ≥ 2`.
    //
    // That `d` is prime for free. A divisor `c` of `d` is positive
    // (`one_le_of_dvd_pos`, using `1 ≤ d`) and divides `m` (`dvd_trans`), so
    // either `c = 1`, or `2 ≤ c` — and then `c ≤ d` (`le_of_dvd`) leaves only
    // `c < d`, which minimality refutes, or `c = d`.
    d.theorem(p.exists_prime_dvd, 1, &|d, v| {
        let m = v[0];
        let two = d.num(2);
        let unit = d.num(1);
        let zero = d.zero();
        let lower_ty = d.le(two, m);
        let predicate = prime_divisor_predicate(d, &p, m);
        let target = {
            let exists = d.kernel().const_(p.logic.exists_, vec![one]);
            d.apply(exists, &[nat, predicate])
        };
        let stmt = d.arrow(lower_ty, target);

        let lower_fv = d.fresh_fvar();
        let lower = d.kernel().fvar(lower_fv);

        let found = least_found(d, &p, m);
        let none = none_up_to(d, &p, m, m);
        let search = d.lemma(p.least_divisor_search, &[m, m]);

        // The right disjunct is self-refuting at `k = m`: `m ∣ m` and `m ≤ m`.
        let exhausted = {
            let none_fv = d.fresh_fvar();
            let none_proof = d.kernel().fvar(none_fv);
            let reflexive = d.lemma(p.le_refl, &[m]);
            let divides = d.lemma(p.dvd_refl, &[m]);
            let contradiction = d.apply(none_proof, &[m, lower, reflexive, divides]);
            let body = absurd(d, target, contradiction);
            d.lam_fv(none_fv, none, body)
        };

        let harvest = {
            let witness_fv = d.fresh_fvar();
            let witness = d.kernel().fvar(witness_fv);
            let least_pred = least_predicate(d, &p, m);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, found, target, BinderInfo::Default);
            let minor = {
                let divisor_fv = d.fresh_fvar();
                let divisor = d.kernel().fvar(divisor_fv);
                let bundle_fv = d.fresh_fvar();
                let bundle = d.kernel().fvar(bundle_fv);

                let lower_divisor_ty = d.le(two, divisor);
                let divides_ty = d.dvd(divisor, m);
                let minimal_ty = min_condition(d, &p, m, divisor);
                let tail_ty = d.const_app(p.logic.and, &[divides_ty, minimal_ty]);
                let bundle_ty = d.const_app(p.logic.and, &[lower_divisor_ty, tail_ty]);

                let lower_divisor = and_left(d, lower_divisor_ty, tail_ty, bundle);
                let tail = and_right(d, lower_divisor_ty, tail_ty, bundle);
                let divides = and_left(d, divides_ty, minimal_ty, tail);
                let minimal = and_right(d, divides_ty, minimal_ty, tail);

                // 1 ≤ 2 ≤ divisor.
                let one_le_two = {
                    let base = d.lemma(p.zero_le, &[unit]);
                    d.lemma(p.le_succ_succ, &[zero, unit, base])
                };
                let positive =
                    d.lemma(p.le_trans, &[unit, two, divisor, one_le_two, lower_divisor]);

                let divisors = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let hypothesis_ty = d.dvd(c, divisor);
                    let hypothesis_fv = d.fresh_fvar();
                    let hypothesis = d.kernel().fvar(hypothesis_fv);
                    let trivial_ty = d.eq(c, unit);
                    let whole_ty = d.eq(c, divisor);
                    let goal = d.const_app(p.logic.or, &[trivial_ty, whole_ty]);

                    let c_positive =
                        d.lemma(p.one_le_of_dvd_pos, &[c, divisor, positive, hypothesis]);
                    let c_divides_m = d.lemma(p.dvd_trans, &[c, divisor, m, hypothesis, divides]);

                    let strict_ty = d.lt(unit, c);
                    let equal_ty = d.eq(unit, c);
                    let split = d.lemma(p.lt_or_eq_of_le, &[unit, c, c_positive]);

                    // 1 < c, i.e. 2 ≤ c: minimality forces c = divisor.
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let bounded = d.lemma(p.le_of_dvd, &[c, divisor, positive, hypothesis]);
                        let inner_strict_ty = d.lt(c, divisor);
                        let inner_equal_ty = d.eq(c, divisor);
                        let inner_split = d.lemma(p.lt_or_eq_of_le, &[c, divisor, bounded]);
                        let below_minor = {
                            let below_fv = d.fresh_fvar();
                            let below = d.kernel().fvar(below_fv);
                            let contradiction = d.apply(minimal, &[c, strict, below, c_divides_m]);
                            let body = absurd(d, goal, contradiction);
                            d.lam_fv(below_fv, inner_strict_ty, body)
                        };
                        let equal_minor = {
                            let equal_fv = d.fresh_fvar();
                            let equal = d.kernel().fvar(equal_fv);
                            let body = d.const_app(p.logic.or_inr, &[trivial_ty, whole_ty, equal]);
                            d.lam_fv(equal_fv, inner_equal_ty, body)
                        };
                        let body = or_cases(
                            d,
                            inner_strict_ty,
                            inner_equal_ty,
                            goal,
                            below_minor,
                            equal_minor,
                            inner_split,
                        );
                        d.lam_fv(strict_fv, strict_ty, body)
                    };

                    // 1 = c, so c = 1 — note the orientation.
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let oriented = d.symm(unit, c, equal);
                        let body = d.const_app(p.logic.or_inl, &[trivial_ty, whole_ty, oriented]);
                        d.lam_fv(equal_fv, equal_ty, body)
                    };

                    let body = or_cases(
                        d,
                        strict_ty,
                        equal_ty,
                        goal,
                        strict_minor,
                        equal_minor,
                        split,
                    );
                    let with_hypothesis = d.lam_fv(hypothesis_fv, hypothesis_ty, body);
                    d.lam_fv(c_fv, nat, with_hypothesis)
                };

                let prime_ty = prime_condition(d, &p, divisor);
                let divisors_ty = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let hypothesis = d.dvd(c, divisor);
                    let trivial = d.eq(c, unit);
                    let whole = d.eq(c, divisor);
                    let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
                    let body = d.arrow(hypothesis, disjunction);
                    d.pi_fv(c_fv, nat, body)
                };
                let prime = d.const_app(
                    p.logic.and_intro,
                    &[lower_divisor_ty, divisors_ty, lower_divisor, divisors],
                );
                let pair = d.const_app(p.logic.and_intro, &[prime_ty, divides_ty, prime, divides]);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, predicate, divisor, pair]);
                let with_bundle = d.lam_fv(bundle_fv, bundle_ty, body);
                d.lam_fv(divisor_fv, nat, with_bundle)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(exists_rec, &[nat, least_pred, motive, minor, witness]);
            d.lam_fv(witness_fv, found, body)
        };

        let selected = or_cases(d, found, none, target, harvest, exhausted, search);
        let proof = d.lam_fv(lower_fv, lower_ty, selected);
        (stmt, proof)
    })?;

    Ok(())
}

/// The two components of [`prime_condition`], so an `And` over it can be split.
pub(super) fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let unit = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hypothesis = d.dvd(c, x);
    let trivial = d.eq(c, unit);
    let whole = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
    let body = d.arrow(hypothesis, disjunction);
    (lower, d.pi_fv(c_fv, nat, body))
}

/// `one_le_factorial : ∀ n, 1 ≤ n!` and `exists_prime_gt` — Euclid's theorem.
///
/// Closes ledger fact `F:nat-exists-prime-gt`. Both dependencies were settled
/// first: `dvd_factorial_of_le` (a number divisible by everything up to `n`) and
/// `exists_prime_dvd` (every `m ≥ 2` has a prime divisor).
///
/// The argument is Euclid's, done entirely over ℕ with no subtraction. Take
/// `m = n! + 1`, which is `≥ 2` because `1 ≤ n!`, and let `q` be a prime
/// dividing it. If `q ≤ n` then `q ∣ n!` by `dvd_factorial_of_le`, and since
/// `q ∣ n! + 1`, `dvd_add_right_cancel_of_pos` gives `q ∣ 1` — refuted by
/// `not_dvd_one_of_two_le`. So `n ≤ q`, and the `n = q` case falls to the same
/// contradiction after transporting `n ≤ n` along the equality, leaving `n < q`.
pub(super) fn declare_euclid(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.one_le_factorial, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let unit = d.num(1);
            let value = d.factorial(x);
            d.le(unit, value)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            // `factorial zero ≡ 1`, and `1 ≤ 1 + 0 ≡ 1`.
            &|d| {
                let unit = d.num(1);
                let zero = d.zero();
                d.lemma(p.le_add_right, &[unit, zero])
            },
            // `factorial (succ j) ≡ factorial j * succ j`, and both factors are
            // at least one — the second because `0 ≤ j`.
            &|d, j, ih| {
                let value = d.factorial(j);
                let successor = d.succ(j);
                let zero = d.zero();
                let base = d.lemma(p.zero_le, &[j]);
                let positive = d.lemma(p.le_succ_succ, &[zero, j, base]);
                d.lemma(p.one_le_mul, &[value, successor, ih, positive])
            },
            n,
        );
        (stmt, proof)
    })?;

    d.theorem(p.exists_prime_gt, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let level = d.level_one();
        let unit = d.num(1);
        let two = d.num(2);
        let value = d.factorial(n);
        let bound = d.add(value, unit);

        let goal_predicate = |d: &mut NatDev<'_>| {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let strict = d.lt(n, q);
            let prime = prime_condition(d, &p, q);
            let body = d.const_app(p.logic.and, &[strict, prime]);
            let nat = d.nat_ty();
            d.lam_fv(q_fv, nat, body)
        };
        let predicate = goal_predicate(d);
        let stmt = {
            let exists = d.kernel().const_(p.logic.exists_, vec![level]);
            d.apply(exists, &[nat, predicate])
        };

        // `2 ≤ n! + 1`, since `1 ≤ n!` and `1 + 1` computes to `2`.
        let one_le_value = d.lemma(p.one_le_factorial, &[n]);
        let two_le_bound = d.lemma(p.add_le_add_right, &[unit, unit, value, one_le_value]);
        let source = d.lemma(p.exists_prime_dvd, &[bound, two_le_bound]);
        let source_predicate = prime_divisor_predicate(d, &p, bound);

        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let prime_ty = prime_condition(d, &p, q);
            let divides_ty = d.dvd(q, bound);
            let prime_proof = and_left(d, prime_ty, divides_ty, h);
            let divides = and_right(d, prime_ty, divides_ty, h);
            let (lower_ty, _) = prime_parts(d, &p, q);
            let (_, divisors_ty) = prime_parts(d, &p, q);
            let two_le_q = and_left(d, lower_ty, divisors_ty, prime_proof);

            // `1 ≤ q` from `2 ≤ q`, via `1 ≤ 1 + 1 ≡ 2`.
            let one_le_two = d.lemma(p.le_add_right, &[unit, unit]);
            let one_le_q = d.lemma(p.le_trans, &[unit, two, q, one_le_two, two_le_q]);

            // `q ≤ n` is impossible: it would make `q` divide both `n!` and
            // `n! + 1`, hence `1`.
            let refute = |d: &mut NatDev<'_>, q_le_n: ExprId| {
                let divides_factorial = d.lemma(p.dvd_factorial_of_le, &[q, n, one_le_q, q_le_n]);
                let divides_one = d.lemma(
                    p.dvd_add_right_cancel_of_pos,
                    &[q, value, unit, one_le_q, divides_factorial, divides],
                );
                let refuted = d.lemma(p.not_dvd_one_of_two_le, &[q, two_le_q]);
                let contradiction = d.apply(refuted, &[divides_one]);
                absurd(d, stmt, contradiction)
            };

            let conclude = |d: &mut NatDev<'_>, strict_proof: ExprId| {
                let strict = d.lt(n, q);
                let prime = prime_condition(d, &p, q);
                let pair = d.const_app(
                    p.logic.and_intro,
                    &[strict, prime, strict_proof, prime_proof],
                );
                let intro = d.kernel().const_(p.logic.exists_intro, vec![level]);
                let predicate = goal_predicate(d);
                d.apply(intro, &[nat, predicate, q, pair])
            };

            let n_le_q_ty = d.le(n, q);
            let q_le_n_ty = d.le(q, n);
            let split = d.lemma(p.le_total, &[n, q]);

            let forward = {
                let le_fv = d.fresh_fvar();
                let le_proof = d.kernel().fvar(le_fv);
                let sharpen = d.lemma(p.lt_or_eq_of_le, &[n, q, le_proof]);
                let strict_ty = d.lt(n, q);
                let equal_ty = d.eq(n, q);
                let strict_branch = {
                    let s_fv = d.fresh_fvar();
                    let s = d.kernel().fvar(s_fv);
                    let body = conclude(d, s);
                    d.lam_fv(s_fv, strict_ty, body)
                };
                let equal_branch = {
                    let e_fv = d.fresh_fvar();
                    let e = d.kernel().fvar(e_fv);
                    // `n = q` gives `q ≤ n` by transporting `n ≤ n`.
                    let zero = d.zero();
                    let reflexive = d.lemma(p.le_add_right, &[n, zero]);
                    let motive = d.eq_motive(n, &|d, x| d.le(x, n));
                    let q_le_n = d.transport(n, motive, reflexive, q, e);
                    let body = refute(d, q_le_n);
                    d.lam_fv(e_fv, equal_ty, body)
                };
                let body = or_cases(
                    d,
                    strict_ty,
                    equal_ty,
                    stmt,
                    strict_branch,
                    equal_branch,
                    sharpen,
                );
                d.lam_fv(le_fv, n_le_q_ty, body)
            };
            let backward = {
                let le_fv = d.fresh_fvar();
                let le_proof = d.kernel().fvar(le_fv);
                let body = refute(d, le_proof);
                d.lam_fv(le_fv, q_le_n_ty, body)
            };

            let body = or_cases(d, n_le_q_ty, q_le_n_ty, stmt, forward, backward, split);
            let hypothesis_ty = {
                let prime = prime_condition(d, &p, q);
                let divides = d.dvd(q, bound);
                d.const_app(p.logic.and, &[prime, divides])
            };
            let with_h = d.lam_fv(h_fv, hypothesis_ty, body);
            d.lam_fv(q_fv, nat, with_h)
        };

        // `Exists.rec`'s motive binds the SOURCE existential, not the goal. Binding
        // `stmt` here is a TypeMismatch whose rendered `expected` is the source
        // predicate applied — which is what named the error.
        let motive = {
            let anon = d.anon_name();
            let exists = d.kernel().const_(p.logic.exists_, vec![level]);
            let source_ty = d.apply(exists, &[nat, source_predicate]);
            d.kernel().lam(anon, source_ty, stmt, BinderInfo::Default)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level]);
        let proof = d.apply(exists_rec, &[nat, source_predicate, motive, minor, source]);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.coprime_of_lt_prime :
/// ∀ p a, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → 0 < a → a < p → gcd a p = 1`.
///
/// Every nonzero residue below a prime is invertible modulo it — the fact
/// that makes ℤ/p a field. `Coprime` has no separate name over `Nat` in this
/// prelude, matching `coprime_of_bezout_one`'s own convention: it is spelled
/// `gcd a p = 1` directly.
///
/// Route: `g := gcd a p` divides `p` (`gcd_dvd_right`), so primality's
/// divisor clause forces `g = 1 ∨ g = p`. The `g = 1` branch is the goal
/// directly. The `g = p` branch transports `g ∣ a` (`gcd_dvd_left`) along
/// `g = p` into `p ∣ a`, which with `0 < a` (defeq `1 ≤ a`, `Nat.lt`
/// unfolding to `Nat.le` composed with `succ`) gives `p ≤ a` via
/// `le_of_dvd` — contradicting `a < p` through `lt_of_le_of_lt` and
/// `lt_irrefl`, so that branch is vacuous (`False.rec`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_coprime_of_lt_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_of_lt_prime, 2, &|d, v| {
        let (p_var, a_var) = (v[0], v[1]);
        let zero = d.zero();
        let one = d.num(1);

        let prime_ty = prime_condition(d, &p, p_var);
        let pos_ty = d.lt(zero, a_var);
        let ub_ty = d.lt(a_var, p_var);

        let common = d.gcd(a_var, p_var);
        let concl = d.eq(common, one);

        let stmt = {
            let inner = d.arrow(ub_ty, concl);
            let with_pos = d.arrow(pos_ty, inner);
            d.arrow(prime_ty, with_pos)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let pos_fv = d.fresh_fvar();
        let pos_hyp = d.kernel().fvar(pos_fv);
        let ub_fv = d.fresh_fvar();
        let ub_hyp = d.kernel().fvar(ub_fv);

        let two_le = {
            let two = d.num(2);
            d.le(two, p_var)
        };
        let clause = {
            // Rebuilt to match `prime_condition`'s own inner shape exactly.
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hyp = d.dvd(x, p_var);
            let is_one = d.eq(x, one);
            let is_p = d.eq(x, p_var);
            let disjunction = d.const_app(p.logic.or, &[is_one, is_p]);
            let inner = d.arrow(hyp, disjunction);
            let nat = d.nat_ty();
            d.pi_fv(x_fv, nat, inner)
        };
        let clause_proof = and_right(d, two_le, clause, prime_hyp);

        let dvd_g_p = d.lemma(p.gcd_dvd_right, &[a_var, p_var]);
        let disj = d.apply(clause_proof, &[common, dvd_g_p]);

        let is_one_ty = d.eq(common, one);
        let is_p_ty = d.eq(common, p_var);

        let on_one = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, is_one_ty, h)
        };

        let on_p = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let dvd_g_a = d.lemma(p.gcd_dvd_left, &[a_var, p_var]);
            let motive = d.eq_motive(common, &|d, x| d.dvd(x, a_var));
            let dvd_p_a = d.transport(common, motive, dvd_g_a, p_var, h);

            let p_le_a = d.lemma(p.le_of_dvd, &[p_var, a_var, pos_hyp, dvd_p_a]);
            let contra = d.lemma(p.lt_of_le_of_lt, &[p_var, a_var, p_var, p_le_a, ub_hyp]);
            let false_pf = d.lemma(p.lt_irrefl, &[p_var, contra]);
            let body = absurd(d, concl, false_pf);
            d.lam_fv(h_fv, is_p_ty, body)
        };

        let proof_body = or_cases(d, is_one_ty, is_p_ty, concl, on_one, on_p, disj);

        let with_ub = d.lam_fv(ub_fv, ub_ty, proof_body);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let proof = d.lam_fv(prime_fv, prime_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_of_dvd_left` / `Nat.coprime_of_dvd_right`: coprimality
// descends along a divisor on either side of `gcd`.
// ============================================================================

/// `Nat.coprime_of_dvd_left : ∀ a1 a2 b, dvd a1 a2 → Eq (gcd a2 b) one → Eq
/// (gcd a1 b) one` and `Nat.coprime_of_dvd_right : ∀ a b1 b2, dvd b1 b2 →
/// Eq (gcd a b2) one → Eq (gcd a b1) one`.
///
/// See the field doc comments on [`NatPrelude::coprime_of_dvd_left`] and
/// [`NatPrelude::coprime_of_dvd_right`] for the route: `gcd a1 b` (resp.
/// `gcd a b1`) divides both the shrunk argument and the shared one, hence
/// divides the shrunk `gcd`'s witness of `1` via `dvd_gcd` +
/// `eq_one_of_dvd_one`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.coprime_of_dvd_left, 3, &|d, v| {
        let (a1, a2, b) = (v[0], v[1], v[2]);
        let one = d.num(1);

        let dvd_ty = d.dvd(a1, a2);
        let gcd_a2b = d.gcd(a2, b);
        let cop_ty = d.eq(gcd_a2b, one);
        let gcd_a1b = d.gcd(a1, b);
        let concl = d.eq(gcd_a1b, one);

        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);
        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);

        let g_dvd_a1 = d.lemma(p.gcd_dvd_left, &[a1, b]);
        let g_dvd_a2 = d.lemma(p.dvd_trans, &[gcd_a1b, a1, a2, g_dvd_a1, dvd_hyp]);
        let g_dvd_b = d.lemma(p.gcd_dvd_right, &[a1, b]);
        let g_dvd_gcd = d.lemma(p.dvd_gcd, &[gcd_a1b, a2, b, g_dvd_a2, g_dvd_b]);
        let dvd_g_1 = transport_dvd_right(d, gcd_a1b, gcd_a2b, one, cop_hyp, g_dvd_gcd);
        let g_eq_1 = d.lemma(p.eq_one_of_dvd_one, &[gcd_a1b, dvd_g_1]);

        let body = d.lam_fv(cop_fv, cop_ty, g_eq_1);
        let proof = d.lam_fv(dvd_fv, dvd_ty, body);
        let inner = d.arrow(cop_ty, concl);
        let stmt = d.arrow(dvd_ty, inner);
        (stmt, proof)
    })?;

    d.theorem(p.coprime_of_dvd_right, 3, &|d, v| {
        let (a, b1, b2) = (v[0], v[1], v[2]);
        let one = d.num(1);

        let dvd_ty = d.dvd(b1, b2);
        let gcd_ab2 = d.gcd(a, b2);
        let cop_ty = d.eq(gcd_ab2, one);
        let gcd_ab1 = d.gcd(a, b1);
        let concl = d.eq(gcd_ab1, one);

        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);
        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);

        let g_dvd_a = d.lemma(p.gcd_dvd_left, &[a, b1]);
        let g_dvd_b1 = d.lemma(p.gcd_dvd_right, &[a, b1]);
        let g_dvd_b2 = d.lemma(p.dvd_trans, &[gcd_ab1, b1, b2, g_dvd_b1, dvd_hyp]);
        let g_dvd_gcd = d.lemma(p.dvd_gcd, &[gcd_ab1, a, b2, g_dvd_a, g_dvd_b2]);
        let dvd_g_1 = transport_dvd_right(d, gcd_ab1, gcd_ab2, one, cop_hyp, g_dvd_gcd);
        let g_eq_1 = d.lemma(p.eq_one_of_dvd_one, &[gcd_ab1, dvd_g_1]);

        let body = d.lam_fv(cop_fv, cop_ty, g_eq_1);
        let proof = d.lam_fv(dvd_fv, dvd_ty, body);
        let inner = d.arrow(cop_ty, concl);
        let stmt = d.arrow(dvd_ty, inner);
        (stmt, proof)
    })?;

    Ok(())
}

// ============================================================================
// `Nat.Coprime.of_dvd : ∀ a1 a2 b1 b2, dvd a1 a2 → dvd b1 b2 → Coprime a2 b2
// → Coprime a1 b1` — a two-step composition of `coprime_of_dvd_right` then
// `coprime_of_dvd_left`.
// ============================================================================

/// See [`NatPrelude::coprime_of_dvd`] for the route: shrink the right side
/// from `b2` to `b1` first (`coprime_of_dvd_right`, keeping `a2` fixed), then
/// shrink the left side from `a2` to `a1` (`coprime_of_dvd_left`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_of_dvd_both(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_of_dvd, 4, &|d, v| {
        let (a1, a2, b1, b2) = (v[0], v[1], v[2], v[3]);
        let one = d.num(1);

        let dvd_a_ty = d.dvd(a1, a2);
        let dvd_b_ty = d.dvd(b1, b2);
        let gcd_a2b2 = d.gcd(a2, b2);
        let cop_ty = d.eq(gcd_a2b2, one);
        let gcd_a1b1 = d.gcd(a1, b1);
        let concl = d.eq(gcd_a1b1, one);

        let dvd_a_fv = d.fresh_fvar();
        let dvd_a_hyp = d.kernel().fvar(dvd_a_fv);
        let dvd_b_fv = d.fresh_fvar();
        let dvd_b_hyp = d.kernel().fvar(dvd_b_fv);
        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);

        // Coprime a2 b2 -> Coprime a2 b1, shrinking the right side via `b1 | b2`.
        let step1 = d.lemma(p.coprime_of_dvd_right, &[a2, b1, b2, dvd_b_hyp, cop_hyp]);
        // Coprime a2 b1 -> Coprime a1 b1, shrinking the left side via `a1 | a2`.
        let step2 = d.lemma(p.coprime_of_dvd_left, &[a1, a2, b1, dvd_a_hyp, step1]);

        let body = d.lam_fv(cop_fv, cop_ty, step2);
        let with_b = d.lam_fv(dvd_b_fv, dvd_b_ty, body);
        let proof = d.lam_fv(dvd_a_fv, dvd_a_ty, with_b);
        let inner2 = d.arrow(cop_ty, concl);
        let inner1 = d.arrow(dvd_b_ty, inner2);
        let stmt = d.arrow(dvd_a_ty, inner1);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_dvd_iff_not_coprime : ∀ p n, prime_condition p → Iff (dvd p n)
// (Not (Eq (gcd p n) one))`.
// ============================================================================

/// See [`NatPrelude::prime_dvd_iff_not_coprime`] for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_iff_not_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_iff_not_coprime, 2, &|d, v| {
        let (p_var, n_var) = (v[0], v[1]);
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let nat = d.nat_ty();

        let prime_ty = prime_condition(d, &p, p_var);

        // Rebuilt to match `prime_condition`'s own inner shape exactly.
        let two_le = d.le(two, p_var);
        let clause = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hyp = d.dvd(x, p_var);
            let is_one = d.eq(x, one);
            let is_p = d.eq(x, p_var);
            let disjunction = d.const_app(p.logic.or, &[is_one, is_p]);
            let inner = d.arrow(hyp, disjunction);
            d.pi_fv(x_fv, nat, inner)
        };

        let dvd_ty = d.dvd(p_var, n_var);
        let gcd_pn = d.gcd(p_var, n_var);
        let cop_ty = d.eq(gcd_pn, one);
        let not_cop_ty = d.const_app(p.logic.not, &[cop_ty]);
        let iff_target = d.const_app(p.logic.iff, &[dvd_ty, not_cop_ty]);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = and_left(d, two_le, clause, prime_hyp);
        let clause_proof = and_right(d, two_le, clause, prime_hyp);

        // Forward: dvd p n -> Not (gcd p n = 1).
        let mp = {
            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);
            let cop_fv = d.fresh_fvar();
            let cop_hyp = d.kernel().fvar(cop_fv);

            let dvd_p_p = d.lemma(p.dvd_refl, &[p_var]);
            let dvd_p_gcd = d.lemma(p.dvd_gcd, &[p_var, p_var, n_var, dvd_p_p, dvd_hyp]);
            let dvd_p_1 = transport_dvd_right(d, p_var, gcd_pn, one, cop_hyp, dvd_p_gcd);
            let one_le_one = d.lemma(p.le_refl_thm, &[one]);
            let p_le_1 = d.lemma(p.le_of_dvd, &[p_var, one, one_le_one, dvd_p_1]);
            let two_le_1 = d.lemma(p.le_trans, &[two, p_var, one, two_le_p, p_le_1]);
            let one_le_zero = d.lemma(p.le_of_succ_le_succ, &[one, zero, two_le_1]);
            let false_pf = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
            let not_cop_proof = d.lam_fv(cop_fv, cop_ty, false_pf);
            d.lam_fv(dvd_fv, dvd_ty, not_cop_proof)
        };

        // Reverse: Not (gcd p n = 1) -> dvd p n.
        let mpr = {
            let notcop_fv = d.fresh_fvar();
            let notcop_hyp = d.kernel().fvar(notcop_fv);

            let dvd_gcd_p = d.lemma(p.gcd_dvd_left, &[p_var, n_var]);
            let disj = d.apply(clause_proof, &[gcd_pn, dvd_gcd_p]);

            let is_one_ty = d.eq(gcd_pn, one);
            let is_p_ty = d.eq(gcd_pn, p_var);

            let on_one = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let false_pf = d.apply(notcop_hyp, &[h]);
                let body = absurd(d, dvd_ty, false_pf);
                d.lam_fv(h_fv, is_one_ty, body)
            };
            let on_p = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let dvd_gcd_n = d.lemma(p.gcd_dvd_right, &[p_var, n_var]);
                let result = transport_dvd_left(d, gcd_pn, p_var, h, n_var, dvd_gcd_n);
                d.lam_fv(h_fv, is_p_ty, result)
            };
            let case_result = or_cases(d, is_one_ty, is_p_ty, dvd_ty, on_one, on_p, disj);
            d.lam_fv(notcop_fv, not_cop_ty, case_result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_ty, not_cop_ty, mp, mpr]);
        let stmt = d.arrow(prime_ty, iff_target);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_add_self_right : ∀ m n, Iff (Eq (gcd m (add n m)) one) (Eq
// (gcd m n) one)`.
// ============================================================================

/// See [`NatPrelude::coprime_add_self_right`] for the route: `gcd m (n+m) =
/// gcd m n` by `dvd_antisymm`, then the `Iff` follows from that one equation
/// by substitution.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_add_self_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_add_self_right, 2, &|d, v| {
        let (m_var, n_var) = (v[0], v[1]);
        let one = d.num(1);

        let sum = d.add(n_var, m_var);
        let swapped_sum = d.add(m_var, n_var);
        let g1 = d.gcd(m_var, sum);
        let g2 = d.gcd(m_var, n_var);

        // g1 | m, g1 | (n+m); reorder to (m+n) to match `dvd_add_iff_right`,
        // cancel the shared `m` to get g1 | n, so g1 | gcd m n = g2.
        let g1_dvd_m = d.lemma(p.gcd_dvd_left, &[m_var, sum]);
        let g1_dvd_sum = d.lemma(p.gcd_dvd_right, &[m_var, sum]);
        let comm_eq = d.lemma(p.add_comm, &[n_var, m_var]);
        let g1_dvd_swapped = transport_dvd_right(d, g1, sum, swapped_sum, comm_eq, g1_dvd_sum);
        let dvd_g1_n_ty = d.dvd(g1, n_var);
        let dvd_g1_swapped_ty = d.dvd(g1, swapped_sum);
        let iff_add = d.lemma(p.dvd_add_iff_right, &[g1, m_var, n_var, g1_dvd_m]);
        let mpr_fn = iff_reverse(d, dvd_g1_n_ty, dvd_g1_swapped_ty, iff_add);
        let g1_dvd_n = d.apply(mpr_fn, &[g1_dvd_swapped]);
        let g1_dvd_g2 = d.lemma(p.dvd_gcd, &[g1, m_var, n_var, g1_dvd_m, g1_dvd_n]);

        // g2 | m, g2 | n, so g2 | (n+m) directly (already the right order),
        // hence g2 | gcd m (n+m) = g1.
        let g2_dvd_m = d.lemma(p.gcd_dvd_left, &[m_var, n_var]);
        let g2_dvd_n = d.lemma(p.gcd_dvd_right, &[m_var, n_var]);
        let g2_dvd_sum = d.lemma(p.dvd_add, &[g2, n_var, m_var, g2_dvd_n, g2_dvd_m]);
        let g2_dvd_g1 = d.lemma(p.dvd_gcd, &[g2, m_var, sum, g2_dvd_m, g2_dvd_sum]);

        let heq = d.lemma(p.dvd_antisymm, &[g1, g2, g1_dvd_g2, g2_dvd_g1]);

        let cop1_ty = d.eq(g1, one);
        let cop2_ty = d.eq(g2, one);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let symm_heq = d.symm(g1, g2, heq);
            let (_e, g2_eq_1) = d.chain(g2, &[(g1, symm_heq), (one, h)]);
            d.lam_fv(h_fv, cop1_ty, g2_eq_1)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let (_e, g1_eq_1) = d.chain(g1, &[(g2, heq), (one, h)]);
            d.lam_fv(h_fv, cop2_ty, g1_eq_1)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[cop1_ty, cop2_ty, mp, mpr]);
        let stmt = d.const_app(p.logic.iff, &[cop1_ty, cop2_ty]);
        (stmt, iff_proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_self_add_right : ∀ m n, Iff (Eq (gcd m (add m n)) one) (Eq
// (gcd m n) one)`.
// ============================================================================

/// See [`NatPrelude::coprime_self_add_right`] for the route: instantiate
/// [`declare_coprime_add_self_right`]'s `Iff (gcd m (n+m) = 1) (gcd m n = 1)`
/// and transport its left side along `add_comm m n : m+n = n+m` to reach `gcd
/// m (m+n) = 1` instead — the only difference from `coprime_add_self_right`
/// is which side of the sum `m` lands on.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_self_add_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_self_add_right, 2, &|d, v| {
        let (m_var, n_var) = (v[0], v[1]);
        let one = d.num(1);

        let sum_nm = d.add(n_var, m_var);
        let sum_mn = d.add(m_var, n_var);
        let g_nm = d.gcd(m_var, sum_nm);
        let g_mn = d.gcd(m_var, sum_mn);
        let g_n = d.gcd(m_var, n_var);

        // gcd m (m+n) = gcd m (n+m), via `add_comm` congr'd through `gcd m _`.
        let comm = d.lemma(p.add_comm, &[m_var, n_var]);
        let congr_g = d.congr(sum_mn, sum_nm, comm, &|d, x| d.gcd(m_var, x));

        let existing = d.lemma(p.coprime_add_self_right, &[m_var, n_var]);

        let a_ty = d.eq(g_mn, one);
        let b_ty = d.eq(g_nm, one);
        let c_ty = d.eq(g_n, one);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive_b = d.eq_motive(g_mn, &|d, x| d.eq(x, one));
            let b_from_a = d.transport(g_mn, motive_b, h, g_nm, congr_g);
            let existing_mp = iff_forward(d, b_ty, c_ty, existing);
            let c_from_b = d.apply(existing_mp, &[b_from_a]);
            d.lam_fv(h_fv, a_ty, c_from_b)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let existing_mpr = iff_reverse(d, b_ty, c_ty, existing);
            let b_from_c = d.apply(existing_mpr, &[h]);
            let sym_congr = d.symm(g_mn, g_nm, congr_g);
            let motive_a = d.eq_motive(g_nm, &|d, x| d.eq(x, one));
            let a_from_b = d.transport(g_nm, motive_a, b_from_c, g_mn, sym_congr);
            d.lam_fv(h_fv, c_ty, a_from_b)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[a_ty, c_ty, mp, mpr]);
        let stmt = d.const_app(p.logic.iff, &[a_ty, c_ty]);
        (stmt, iff_proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Coprime.symmetric : ∀ a b, Eq (gcd a b) one → Eq (gcd b a) one`.
// ============================================================================

/// See [`NatPrelude::coprime_symmetric`] for the route: `gcd a b` and
/// `gcd b a` divide each other (`gcd_dvd_left`/`gcd_dvd_right` on both
/// orderings, combined via `dvd_gcd`), so `dvd_antisymm` gives `gcd a b = gcd
/// b a`, and the hypothesis transports along it.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_symmetric(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_symmetric, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let one = d.num(1);
        let gab = d.gcd(a, b);
        let gba = d.gcd(b, a);
        let cop_ab = d.eq(gab, one);
        let cop_ba = d.eq(gba, one);
        let stmt = d.arrow(cop_ab, cop_ba);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let gab_dvd_a = d.lemma(p.gcd_dvd_left, &[a, b]);
        let gab_dvd_b = d.lemma(p.gcd_dvd_right, &[a, b]);
        let gab_dvd_gba = d.lemma(p.dvd_gcd, &[gab, b, a, gab_dvd_b, gab_dvd_a]);

        let gba_dvd_b = d.lemma(p.gcd_dvd_left, &[b, a]);
        let gba_dvd_a = d.lemma(p.gcd_dvd_right, &[b, a]);
        let gba_dvd_gab = d.lemma(p.dvd_gcd, &[gba, a, b, gba_dvd_a, gba_dvd_b]);

        let heq = d.lemma(p.dvd_antisymm, &[gab, gba, gab_dvd_gba, gba_dvd_gab]);
        let sym_heq = d.symm(gab, gba, heq);
        let result = d.trans(gba, gab, one, sym_heq, h);

        let proof = d.lam_fv(h_fv, cop_ab, result);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.not_coprime_zero_zero : Not (Eq (gcd zero zero) one)`.
// ============================================================================

/// See [`NatPrelude::not_coprime_zero_zero`] for the route: `gcd 0 0 = 0`
/// (`gcd_zero_left`), so a hypothesis `gcd 0 0 = 1` chains to `0 = 1`
/// (`d.chain`), whose `symm` is `Eq (succ zero) zero` — refuted directly by
/// `succ_ne_zero`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_not_coprime_zero_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.not_coprime_zero_zero, 0, &|d, _v| {
        let zero = d.zero();
        let one = d.num(1);
        let gcd00 = d.gcd(zero, zero);
        let cop_ty = d.eq(gcd00, one);
        let not_cop_ty = d.const_app(p.logic.not, &[cop_ty]);

        let gcd_eq = d.lemma(p.gcd_zero_left, &[zero]); // Eq gcd00 zero
        let symm_gcd = d.symm(gcd00, zero, gcd_eq); // Eq zero gcd00

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv); // h : Eq gcd00 one
        let (_, zero_eq_one) = d.chain(zero, &[(gcd00, symm_gcd), (one, h)]);
        let one_eq_zero = d.symm(zero, one, zero_eq_one); // Eq one zero = Eq (succ zero) zero
        let false_pf = d.lemma(p.succ_ne_zero, &[zero, one_eq_zero]);
        let mp = d.lam_fv(h_fv, cop_ty, false_pf);
        (not_cop_ty, mp)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_one_left_iff : ∀ n, Iff (Eq (gcd one n) one) True` and
// `Nat.coprime_one_right_iff : ∀ n, Iff (Eq (gcd n one) one) True`.
// ============================================================================

/// See [`NatPrelude::coprime_one_left_iff`] and
/// [`NatPrelude::coprime_one_right_iff`] for the route: `gcd 1 n` (resp.
/// `gcd n 1`) divides `1` directly (`gcd_dvd_left`/`gcd_dvd_right`), so
/// `eq_one_of_dvd_one` gives the equation unconditionally and the `Iff` with
/// `True` is immediate (`True.intro` forward, the equation itself backward).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_one_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.coprime_one_left_iff, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let gcd1n = d.gcd(one, n);
        let cop_ty = d.eq(gcd1n, one);
        let true_ty = d.kernel().const_(p.logic.true_, vec![]);

        let dvd_one = d.lemma(p.gcd_dvd_left, &[one, n]); // dvd gcd1n one
        let eq_one = d.lemma(p.eq_one_of_dvd_one, &[gcd1n, dvd_one]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
            d.lam_fv(h_fv, cop_ty, true_intro)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, true_ty, eq_one)
        };
        let stmt = d.const_app(p.logic.iff, &[cop_ty, true_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[cop_ty, true_ty, mp, mpr]);
        (stmt, proof)
    })?;

    d.theorem(p.coprime_one_right_iff, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let gcdn1 = d.gcd(n, one);
        let cop_ty = d.eq(gcdn1, one);
        let true_ty = d.kernel().const_(p.logic.true_, vec![]);

        let dvd_one = d.lemma(p.gcd_dvd_right, &[n, one]); // dvd gcdn1 one
        let eq_one = d.lemma(p.eq_one_of_dvd_one, &[gcdn1, dvd_one]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
            d.lam_fv(h_fv, cop_ty, true_intro)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            d.lam_fv(h_fv, true_ty, eq_one)
        };
        let stmt = d.const_app(p.logic.iff, &[cop_ty, true_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[cop_ty, true_ty, mp, mpr]);
        (stmt, proof)
    })?;

    Ok(())
}

// ============================================================================
// `Nat.coprime_add_self_left : ∀ m n, Iff (Eq (gcd (add m n) n) one) (Eq (gcd
// m n) one)`.
// ============================================================================

/// See [`NatPrelude::coprime_add_self_left`] for the route: swap both sides
/// of [`declare_coprime_add_self_right`]'s `Iff (gcd n (m+n) = 1) (gcd n m =
/// 1)` (instantiated at `(n, m)`) through [`declare_coprime_symmetric`] on
/// each end — `gcd (m+n) n` swaps to `gcd n (m+n)`, and `gcd n m` swaps to
/// `gcd m n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_add_self_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_add_self_left, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let one = d.num(1);
        let sum_mn = d.add(m, n); // m + n
        let g1 = d.gcd(sum_mn, n); // gcd (m+n) n         <- goal LHS
        let g2 = d.gcd(m, n); // gcd m n                  <- goal RHS
        let gn_sum = d.gcd(n, sum_mn); // gcd n (m+n)
        let gn_m = d.gcd(n, m); // gcd n m

        // Iff (Eq (gcd n (add m n)) one) (Eq (gcd n m) one)
        let existing = d.lemma(p.coprime_add_self_right, &[n, m]);

        let cop1_ty = d.eq(g1, one);
        let cop2_ty = d.eq(g2, one);
        let mid_a_ty = d.eq(gn_sum, one);
        let mid_b_ty = d.eq(gn_m, one);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let step1 = d.lemma(p.coprime_symmetric, &[sum_mn, n, h]); // gn_sum = 1
            let step2_fn = iff_forward(d, mid_a_ty, mid_b_ty, existing);
            let step2 = d.apply(step2_fn, &[step1]); // gn_m = 1
            let step3 = d.lemma(p.coprime_symmetric, &[n, m, step2]); // g2 = 1
            d.lam_fv(h_fv, cop1_ty, step3)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let step1 = d.lemma(p.coprime_symmetric, &[m, n, h]); // gn_m = 1
            let step2_fn = iff_reverse(d, mid_a_ty, mid_b_ty, existing);
            let step2 = d.apply(step2_fn, &[step1]); // gn_sum = 1
            let step3 = d.lemma(p.coprime_symmetric, &[n, sum_mn, step2]); // g1 = 1
            d.lam_fv(h_fv, cop2_ty, step3)
        };

        let stmt = d.const_app(p.logic.iff, &[cop1_ty, cop2_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[cop1_ty, cop2_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_self_add_left : ∀ m n, Iff (Eq (gcd (add m n) m) one) (Eq (gcd
// n m) one)`.
// ============================================================================

/// See [`NatPrelude::coprime_self_add_left`] for the route: instantiate
/// [`declare_coprime_add_self_left`]'s `Iff (gcd (n+m) m = 1) (gcd n m = 1)`
/// at `(n, m)` and transport its left side along `add_comm m n : m+n = n+m`
/// to reach `gcd (m+n) m = 1` instead — the same congruence-transport shape
/// [`declare_coprime_self_add_right`] uses over
/// [`declare_coprime_add_self_right`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_self_add_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_self_add_left, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let one = d.num(1);

        let sum_mn = d.add(m, n); // m + n
        let sum_nm = d.add(n, m); // n + m
        let g_mn = d.gcd(sum_mn, m); // gcd (m+n) m      <- goal LHS
        let g_nm = d.gcd(sum_nm, m); // gcd (n+m) m
        let g_n = d.gcd(n, m); // gcd n m                <- goal RHS

        // gcd (m+n) m = gcd (n+m) m, via `add_comm` congr'd through `gcd _ m`.
        let comm = d.lemma(p.add_comm, &[m, n]); // Eq (add m n) (add n m)
        let congr_g = d.congr(sum_mn, sum_nm, comm, &|d, x| d.gcd(x, m));

        // Iff (Eq (gcd (add n m) m) one) (Eq (gcd n m) one)
        let existing = d.lemma(p.coprime_add_self_left, &[n, m]);

        let a_ty = d.eq(g_mn, one);
        let b_ty = d.eq(g_nm, one);
        let c_ty = d.eq(g_n, one);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive_b = d.eq_motive(g_mn, &|d, x| d.eq(x, one));
            let b_from_a = d.transport(g_mn, motive_b, h, g_nm, congr_g);
            let existing_mp = iff_forward(d, b_ty, c_ty, existing);
            let c_from_b = d.apply(existing_mp, &[b_from_a]);
            d.lam_fv(h_fv, a_ty, c_from_b)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let existing_mpr = iff_reverse(d, b_ty, c_ty, existing);
            let b_from_c = d.apply(existing_mpr, &[h]);
            let sym_congr = d.symm(g_mn, g_nm, congr_g);
            let motive_a = d.eq_motive(g_nm, &|d, x| d.eq(x, one));
            let a_from_b = d.transport(g_nm, motive_a, b_from_c, g_mn, sym_congr);
            d.lam_fv(h_fv, c_ty, a_from_b)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[a_ty, c_ty, mp, mpr]);
        let stmt = d.const_app(p.logic.iff, &[a_ty, c_ty]);
        (stmt, iff_proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.dvd_lcm_of_dvd_left : ∀ a b c, dvd a b → dvd a (lcm b c)` and
// `Nat.dvd_lcm_of_dvd_right : ∀ a b c, dvd a b → dvd a (lcm c b)`.
// ============================================================================

/// See [`NatPrelude::dvd_lcm_of_dvd_left`] and
/// [`NatPrelude::dvd_lcm_of_dvd_right`] for the route: `dvd_trans` through
/// `dvd_lcm_left`/`dvd_lcm_right` (declared in `nat_prelude/lcm.rs`, read
/// here through the shared `NatPrelude` fields, not edited).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_lcm_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.dvd_lcm_of_dvd_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let dvd_ab_ty = d.dvd(a, b);
        let lcm_bc = d.const_app(p.lcm, &[b, c]);
        let concl_ty = d.dvd(a, lcm_bc);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dvd_b_lcm = d.lemma(p.dvd_lcm_left, &[b, c]); // dvd b (lcm b c)
        let proof_body = d.lemma(p.dvd_trans, &[a, b, lcm_bc, h, dvd_b_lcm]);
        let proof = d.lam_fv(h_fv, dvd_ab_ty, proof_body);
        let stmt = d.arrow(dvd_ab_ty, concl_ty);
        (stmt, proof)
    })?;

    d.theorem(p.dvd_lcm_of_dvd_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let dvd_ab_ty = d.dvd(a, b);
        let lcm_cb = d.const_app(p.lcm, &[c, b]);
        let concl_ty = d.dvd(a, lcm_cb);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dvd_b_lcm = d.lemma(p.dvd_lcm_right, &[c, b]); // dvd b (lcm c b)
        let proof_body = d.lemma(p.dvd_trans, &[a, b, lcm_cb, h, dvd_b_lcm]);
        let proof = d.lam_fv(h_fv, dvd_ab_ty, proof_body);
        let stmt = d.arrow(dvd_ab_ty, concl_ty);
        (stmt, proof)
    })?;

    Ok(())
}

// ============================================================================
// `Nat.dvd_of_lcm_left_dvd : ∀ a b c, dvd (lcm a b) c → dvd b c` and
// `Nat.dvd_of_lcm_right_dvd : ∀ a b c, dvd (lcm a b) c → dvd a c`.
// ============================================================================

/// See [`NatPrelude::dvd_of_lcm_left_dvd`] and
/// [`NatPrelude::dvd_of_lcm_right_dvd`] for the route: `dvd_trans` through
/// `dvd_lcm_right`/`dvd_lcm_left` (`b ∣ lcm a b`, resp. `a ∣ lcm a b`),
/// composed with the hypothesis `lcm a b ∣ c`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_of_lcm_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.dvd_of_lcm_left_dvd, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let lcm_ab = d.const_app(p.lcm, &[a, b]);
        let hyp_ty = d.dvd(lcm_ab, c);
        let concl_ty = d.dvd(b, c);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dvd_b_lcm = d.lemma(p.dvd_lcm_right, &[a, b]); // dvd b (lcm a b)
        let proof_body = d.lemma(p.dvd_trans, &[b, lcm_ab, c, dvd_b_lcm, h]);
        let proof = d.lam_fv(h_fv, hyp_ty, proof_body);
        let stmt = d.arrow(hyp_ty, concl_ty);
        (stmt, proof)
    })?;

    d.theorem(p.dvd_of_lcm_right_dvd, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let lcm_ab = d.const_app(p.lcm, &[a, b]);
        let hyp_ty = d.dvd(lcm_ab, c);
        let concl_ty = d.dvd(a, c);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dvd_a_lcm = d.lemma(p.dvd_lcm_left, &[a, b]); // dvd a (lcm a b)
        let proof_body = d.lemma(p.dvd_trans, &[a, lcm_ab, c, dvd_a_lcm, h]);
        let proof = d.lam_fv(h_fv, hyp_ty, proof_body);
        let stmt = d.arrow(hyp_ty, concl_ty);
        (stmt, proof)
    })?;

    Ok(())
}

// ============================================================================
// `Nat.coprime_or_dvd_of_prime : ∀ p, prime_condition p → ∀ i, Or (Eq (gcd p
// i) one) (dvd p i)`.
// ============================================================================

/// See [`NatPrelude::coprime_or_dvd_of_prime`] for the route: decide
/// `beq (gcd p i) one` via [`bool_true_or_false`](super::ops::bool_true_or_false) — the `true` branch gives
/// `Coprime p i` directly (`eq_of_beq_eq_true`); the `false` branch gives
/// `Not (Coprime p i)` (`ne_of_beq_eq_false`), which `prime_dvd_iff_not_coprime`
/// converts to `dvd p i`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_or_dvd_of_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_or_dvd_of_prime, 2, &|d, v| {
        let (p_var, i_var) = (v[0], v[1]);
        let one = d.num(1);

        let prime_ty = prime_condition(d, &p, p_var);
        let gcd_pi = d.gcd(p_var, i_var);
        let coprime_ty = d.eq(gcd_pi, one);
        let dvd_ty = d.dvd(p_var, i_var);
        let disj_ty = d.const_app(p.logic.or, &[coprime_ty, dvd_ty]);
        let stmt = d.arrow(prime_ty, disj_ty);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let beq_gi = d.beq(gcd_pi, one);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let true_ty = d.bool_eq(beq_gi, true_);
        let false_ty = d.bool_eq(beq_gi, false_);
        let cases = bool_true_or_false(d, &p, beq_gi);

        let true_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq_derived = d.lemma(p.eq_of_beq_eq_true, &[gcd_pi, one, h]);
            let inl = d.const_app(p.logic.or_inl, &[coprime_ty, dvd_ty, eq_derived]);
            d.lam_fv(h_fv, true_ty, inl)
        };
        let false_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ne_derived = d.lemma(p.ne_of_beq_eq_false, &[gcd_pi, one, h]);
            let iff_pf = d.lemma(p.prime_dvd_iff_not_coprime, &[p_var, i_var, prime_hyp]);
            let not_cop_ty = d.const_app(p.logic.not, &[coprime_ty]);
            let mpr_fn = iff_reverse(d, dvd_ty, not_cop_ty, iff_pf);
            let dvd_derived = d.apply(mpr_fn, &[ne_derived]);
            let inr = d.const_app(p.logic.or_inr, &[coprime_ty, dvd_ty, dvd_derived]);
            d.lam_fv(h_fv, false_ty, inr)
        };

        let motive_or = {
            let or_ty = d.const_app(p.logic.or, &[true_ty, false_ty]);
            let anon = d.anon_name();
            d.kernel().lam(anon, or_ty, disj_ty, BinderInfo::Default)
        };
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let body = d.apply(
            or_rec,
            &[
                true_ty,
                false_ty,
                motive_or,
                true_branch,
                false_branch,
                cases,
            ],
        );

        let proof = d.lam_fv(prime_fv, prime_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_primes : ∀ p q, prime_condition p → prime_condition q →
// Iff (Eq (gcd p q) one) (Not (Eq p q))`.
// ============================================================================

/// `prime p → 0 < p`, mirroring `fermat.rs`'s private `prime_pos` exactly
/// (same construction, so the `ExprId`s intern identically) since that helper
/// is `fn`-private to its own file.
fn prime_pos_local(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, prime_proof: ExprId) -> ExprId {
    let (two_le_ty, divisor_clause_ty) = prime_parts(d, p, x);
    let two_le = and_left(d, two_le_ty, divisor_clause_ty, prime_proof);
    let one = d.num(1);
    let two = d.num(2);
    let one_le_two = d.lemma(p.le_succ, &[one]);
    d.lemma(p.le_trans, &[one, two, x, one_le_two, two_le])
}

/// `Nat.coprime_primes : ∀ p q, prime_condition p → prime_condition q →
/// Iff (Eq (gcd p q) one) (Not (Eq p q))`.
///
/// See [`NatPrelude::coprime_primes`] for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_primes(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_primes, 2, &|d, v| {
        let (p_var, q_var) = (v[0], v[1]);
        let one = d.num(1);

        let prime_p_ty = prime_condition(d, &p, p_var);
        let prime_q_ty = prime_condition(d, &p, q_var);

        let gcd_pq = d.gcd(p_var, q_var);
        let coprime_ty = d.eq(gcd_pq, one);
        let eq_pq_ty = d.eq(p_var, q_var);
        let ne_ty = d.const_app(p.logic.not, &[eq_pq_ty]);
        let iff_target = d.const_app(p.logic.iff, &[coprime_ty, ne_ty]);
        let stmt_inner = d.arrow(prime_q_ty, iff_target);
        let stmt = d.arrow(prime_p_ty, stmt_inner);

        let prime_p_fv = d.fresh_fvar();
        let prime_p_hyp = d.kernel().fvar(prime_p_fv);
        let prime_q_fv = d.fresh_fvar();
        let prime_q_hyp = d.kernel().fvar(prime_q_fv);

        // mp : coprime p q -> p != q
        let mp = {
            let cop_fv = d.fresh_fvar();
            let cop_hyp = d.kernel().fvar(cop_fv);
            let eq_fv = d.fresh_fvar();
            let eq_hyp = d.kernel().fvar(eq_fv);

            let dvd_p_p = d.lemma(p.dvd_refl, &[p_var]);
            let dvd_p_q = transport_dvd_right(d, p_var, p_var, q_var, eq_hyp, dvd_p_p);
            let iff_pf = d.lemma(p.prime_dvd_iff_not_coprime, &[p_var, q_var, prime_p_hyp]);
            let dvd_ty = d.dvd(p_var, q_var);
            let not_cop_ty = d.const_app(p.logic.not, &[coprime_ty]);
            let mp_fn = iff_forward(d, dvd_ty, not_cop_ty, iff_pf);
            let not_cop = d.apply(mp_fn, &[dvd_p_q]);
            let false_pf = d.apply(not_cop, &[cop_hyp]);
            let inner = d.lam_fv(eq_fv, eq_pq_ty, false_pf);
            d.lam_fv(cop_fv, coprime_ty, inner)
        };

        // mpr : p != q -> coprime p q
        let mpr = {
            let ne_fv = d.fresh_fvar();
            let ne_hyp = d.kernel().fvar(ne_fv);

            let disj = d.lemma(p.coprime_or_dvd_of_prime, &[p_var, q_var, prime_p_hyp]);
            let dvd_ty = d.dvd(p_var, q_var);

            let on_coprime = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                d.lam_fv(h_fv, coprime_ty, h)
            };
            let on_dvd = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let (lower_q, divisors_q) = prime_parts(d, &p, q_var);
                let clause_q = and_right(d, lower_q, divisors_q, prime_q_hyp);
                let disj2 = d.apply(clause_q, &[p_var, h]);

                let is_one_ty = d.eq(p_var, one);
                let is_q_ty = d.eq(p_var, q_var);

                let on_one = {
                    let h1_fv = d.fresh_fvar();
                    let h1 = d.kernel().fvar(h1_fv);
                    let result = refute_eq_one_against_prime_lower_bound(
                        d,
                        &p,
                        p_var,
                        prime_p_hyp,
                        h1,
                        coprime_ty,
                    );
                    d.lam_fv(h1_fv, is_one_ty, result)
                };
                let on_q = {
                    let hq_fv = d.fresh_fvar();
                    let hq = d.kernel().fvar(hq_fv);
                    let false_pf = d.apply(ne_hyp, &[hq]);
                    let result = absurd(d, coprime_ty, false_pf);
                    d.lam_fv(hq_fv, is_q_ty, result)
                };
                let case_result = or_cases(d, is_one_ty, is_q_ty, coprime_ty, on_one, on_q, disj2);
                d.lam_fv(h_fv, dvd_ty, case_result)
            };
            let case_result = or_cases(d, coprime_ty, dvd_ty, coprime_ty, on_coprime, on_dvd, disj);
            d.lam_fv(ne_fv, ne_ty, case_result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[coprime_ty, ne_ty, mp, mpr]);
        let proof_inner = d.lam_fv(prime_q_fv, prime_q_ty, iff_proof);
        let proof = d.lam_fv(prime_p_fv, prime_p_ty, proof_inner);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.not_prime_of_dvd_of_ne : ∀ m n, dvd m n → Not (Eq m one) → Not (Eq m
// n) → Not (prime_condition n)`.
// ============================================================================

/// `Nat.not_prime_of_dvd_of_ne : ∀ m n, dvd m n → Not (Eq m one) → Not (Eq m
/// n) → Not (prime_condition n)`.
///
/// See [`NatPrelude::not_prime_of_dvd_of_ne`] for the route: `n`'s own
/// divisor clause applied to `m` gives `m = 1 ∨ m = n`, and either disjunct
/// contradicts one of the two hypotheses directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_not_prime_of_dvd_of_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.not_prime_of_dvd_of_ne, 2, &|d, v| {
        let (m_var, n_var) = (v[0], v[1]);
        let one = d.num(1);

        let dvd_ty = d.dvd(m_var, n_var);
        let eq_m_one_ty = d.eq(m_var, one);
        let ne1_ty = d.const_app(p.logic.not, &[eq_m_one_ty]);
        let eq_m_n_ty = d.eq(m_var, n_var);
        let nen_ty = d.const_app(p.logic.not, &[eq_m_n_ty]);
        let prime_n_ty = prime_condition(d, &p, n_var);
        let concl = d.const_app(p.logic.not, &[prime_n_ty]);
        let stmt_inner2 = d.arrow(nen_ty, concl);
        let stmt_inner1 = d.arrow(ne1_ty, stmt_inner2);
        let stmt = d.arrow(dvd_ty, stmt_inner1);

        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);
        let ne1_fv = d.fresh_fvar();
        let ne1_hyp = d.kernel().fvar(ne1_fv);
        let nen_fv = d.fresh_fvar();
        let nen_hyp = d.kernel().fvar(nen_fv);
        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let (lower_n, divisors_n) = prime_parts(d, &p, n_var);
        let clause_n = and_right(d, lower_n, divisors_n, prime_hyp);
        let disj = d.apply(clause_n, &[m_var, dvd_hyp]);

        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let on_one = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let false_pf = d.apply(ne1_hyp, &[h]);
            d.lam_fv(h_fv, eq_m_one_ty, false_pf)
        };
        let on_n = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let false_pf = d.apply(nen_hyp, &[h]);
            d.lam_fv(h_fv, eq_m_n_ty, false_pf)
        };
        let case_result = or_cases(d, eq_m_one_ty, eq_m_n_ty, false_ty, on_one, on_n, disj);
        let body = d.lam_fv(prime_fv, prime_n_ty, case_result);

        let proof_inner2 = d.lam_fv(nen_fv, nen_ty, body);
        let proof_inner1 = d.lam_fv(ne1_fv, ne1_ty, proof_inner2);
        let proof = d.lam_fv(dvd_fv, dvd_ty, proof_inner1);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Prime.five_le_of_ne_two_of_ne_three : ∀ p, prime_condition p → Not
// (Eq p two) → Not (Eq p three) → Le five p`.
// ============================================================================

/// The `p = 0` sub-branch: `0`'s equality contradicts the primality
/// hypothesis's own lower bound `2 ≤ p` — the same route as
/// [`refute_eq_one_against_prime_lower_bound`], landing on `Le (succ one)
/// zero` (i.e. `Le 2 0`) rather than `Le one zero`.
fn refute_eq_zero_against_prime_lower_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_var: ExprId,
    prime_hyp: ExprId,
    h0: ExprId,
    goal: ExprId,
) -> ExprId {
    let zero = d.zero();
    let one = d.num(1);
    let (lower_ty, divisors_ty) = prime_parts(d, p, p_var);
    let two_le_p = and_left(d, lower_ty, divisors_ty, prime_hyp);
    let motive = d.eq_motive(p_var, &|d, x| {
        let two = d.num(2);
        d.le(two, x)
    });
    let two_le_zero = d.transport(p_var, motive, two_le_p, zero, h0);
    let false_pf = d.lemma(p.not_succ_le_zero, &[one, two_le_zero]);
    absurd(d, goal, false_pf)
}

/// The `p = 4` sub-branch: `4` is composite (`4 = 2*2`), refuted via
/// `not_prime_of_dvd_of_ne` at `(m, n) = (2, 4)` — `dvd_mul 2 2 : dvd 2 (mul
/// 2 2)` is defeq `dvd 2 4`; `2 ≠ 1` and `2 ≠ 4` both come from
/// `finite::ne_of_lt` off a cheap `Le`/`Lt` fact (`Le 2 2` defeq `Lt 1 2`,
/// `le_add_right 3 1` defeq `Lt 2 4`). The resulting `Not (prime_condition
/// 4)` is applied to `prime_hyp` transported along `h4 : Eq p_var 4`.
fn refute_eq_four_against_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_var: ExprId,
    prime_hyp: ExprId,
    h4: ExprId,
    goal: ExprId,
) -> ExprId {
    let two = d.num(2);
    let four = d.num(4);
    let one = d.num(1);
    let three = d.num(3);

    let dvd_2_4 = d.lemma(p.dvd_mul, &[two, two]); // dvd 2 (mul 2 2), defeq dvd 2 4

    let lt_1_2 = d.lemma(p.le_refl, &[two]); // Le 2 2, defeq Lt 1 2
    let ne_1_2 = ne_of_lt(d, p, one, two, lt_1_2); // Not (Eq 1 2)
    let ne_2_1 = ne_symm(d, one, two, ne_1_2); // Not (Eq 2 1)

    let lt_2_4 = d.lemma(p.le_add_right, &[three, one]); // Le 3 (add 3 1), defeq Lt 2 4
    let ne_2_4 = ne_of_lt(d, p, two, four, lt_2_4); // Not (Eq 2 4)

    let not_prime_4 = d.lemma(
        p.not_prime_of_dvd_of_ne,
        &[two, four, dvd_2_4, ne_2_1, ne_2_4],
    );

    let motive4 = d.eq_motive(p_var, &|d, x| prime_condition(d, p, x));
    let prime_4 = d.transport(p_var, motive4, prime_hyp, four, h4);
    let false_pf = d.apply(not_prime_4, &[prime_4]);
    absurd(d, goal, false_pf)
}

/// `Nat.Prime.five_le_of_ne_two_of_ne_three` — see
/// [`NatPrelude::five_le_of_ne_two_of_ne_three`] for the route: split at
/// `Nat.lt_or_ge p 5` ([`cases_lt_or_ge`]); the `Le 5 p` side is the
/// hypothesis itself, and the `Lt p 5` side is the 5-way case split
/// ([`cases_lt_bound_absurd`]) to `p ∈ {0,1,2,3,4}` this fact's whole
/// difficulty is — `p = 0, 1` contradict the primality lower bound, `p = 2,
/// 3` contradict the two `Not` hypotheses directly, and `p = 4` is refuted
/// as composite.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_five_le_of_ne_two_of_ne_three(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.five_le_of_ne_two_of_ne_three, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let three = d.num(3);
        let five = d.num(5);

        let prime_ty = prime_condition(d, &p, p_var);
        let eq2_ty = d.eq(p_var, two);
        let ne2_ty = d.const_app(p.logic.not, &[eq2_ty]);
        let eq3_ty = d.eq(p_var, three);
        let ne3_ty = d.const_app(p.logic.not, &[eq3_ty]);
        let concl = d.le(five, p_var);

        let stmt = {
            let inner2 = d.arrow(ne3_ty, concl);
            let inner1 = d.arrow(ne2_ty, inner2);
            d.arrow(prime_ty, inner1)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let ne2_fv = d.fresh_fvar();
        let ne2_hyp = d.kernel().fvar(ne2_fv);
        let ne3_fv = d.fresh_fvar();
        let ne3_hyp = d.kernel().fvar(ne3_fv);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let five = d.num(5);
            d.le(five, x)
        };

        let small = |d: &mut NatDev<'_>, p_var: ExprId, lt_p_5: ExprId| -> ExprId {
            let goal = motive(d, p_var);

            let b0: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId =
                &|d, h| refute_eq_zero_against_prime_lower_bound(d, &p, p_var, prime_hyp, h, goal);
            let b1: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId =
                &|d, h| refute_eq_one_against_prime_lower_bound(d, &p, p_var, prime_hyp, h, goal);
            let b2: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId = &|d, h| {
                let false_pf = d.apply(ne2_hyp, &[h]);
                absurd(d, goal, false_pf)
            };
            let b3: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId = &|d, h| {
                let false_pf = d.apply(ne3_hyp, &[h]);
                absurd(d, goal, false_pf)
            };
            let b4: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId =
                &|d, h| refute_eq_four_against_prime(d, &p, p_var, prime_hyp, h, goal);

            let branches: [&dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId; 5] = [b0, b1, b2, b3, b4];
            cases_lt_bound_absurd(d, &p, p_var, 5, lt_p_5, goal, &branches)
        };
        let big = |_d: &mut NatDev<'_>, _p_var: ExprId, le_5_p: ExprId| -> ExprId { le_5_p };

        let five_thresh = d.num(5);
        let body = cases_lt_or_ge(d, &p, p_var, five_thresh, &motive, &small, &big);

        let value = {
            let inner2 = d.lam_fv(ne3_fv, ne3_ty, body);
            let inner1 = d.lam_fv(ne2_fv, ne2_ty, inner2);
            d.lam_fv(prime_fv, prime_ty, inner1)
        };
        (stmt, value)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Prime.pred_pos : ∀ p, prime_condition p → Lt zero (pred p)` and
// `Nat.succ_pred_prime : ∀ p, prime_condition p → Eq (succ (pred p)) p`.
// ============================================================================

/// `Nat.Prime.pred_pos : ∀ p, prime_condition p → Lt zero (pred p)`.
///
/// See [`NatPrelude::prime_pred_pos`] for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_pred_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_pred_pos, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let zero = d.zero();

        let prime_ty = prime_condition(d, &p, p_var);
        let pred_p = d.pred(p_var);
        let concl = d.lt(zero, pred_p);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let two_le_p = and_left(d, lower_ty, divisors_ty, prime_hyp);
        let zero_lt_p = prime_pos_local(d, &p, p_var, prime_hyp);
        let succ_pred_fn = pos_implies_succ_pred(d, &p, p_var);
        let eq_p_succ_pred = d.apply(succ_pred_fn, &[zero_lt_p]);

        let succ_pred_p = d.succ(pred_p);
        let two = d.num(2);
        let two_le_succ_pred = {
            let motive = d.eq_motive(p_var, &|d, x| d.le(two, x));
            d.transport(p_var, motive, two_le_p, succ_pred_p, eq_p_succ_pred)
        };
        let one_le_pred = d.lemma(p.le_of_succ_le_succ, &[one, pred_p, two_le_succ_pred]);

        let proof = d.lam_fv(prime_fv, prime_ty, one_le_pred);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.succ_pred_prime : ∀ p, prime_condition p → Eq (succ (pred p)) p`.
///
/// See [`NatPrelude::succ_pred_prime`] for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_succ_pred_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.succ_pred_prime, 1, &|d, v| {
        let p_var = v[0];
        let pred_p = d.pred(p_var);
        let succ_pred_p = d.succ(pred_p);

        let prime_ty = prime_condition(d, &p, p_var);
        let concl = d.eq(succ_pred_p, p_var);
        let stmt = d.arrow(prime_ty, concl);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let zero_lt_p = prime_pos_local(d, &p, p_var, prime_hyp);
        let succ_pred_fn = pos_implies_succ_pred(d, &p, p_var);
        let eq_p_succ_pred = d.apply(succ_pred_fn, &[zero_lt_p]);
        let eq_succ_pred_p = d.symm(p_var, succ_pred_p, eq_p_succ_pred);

        let proof = d.lam_fv(prime_fv, prime_ty, eq_succ_pred_p);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Prime.dvd_mul_of_dvd_ne : ∀ p1 p2 n, Not (Eq p1 p2) → prime_condition
// p1 → prime_condition p2 → dvd p1 n → dvd p2 n → dvd (mul p1 p2) n`.
// ============================================================================

/// `Nat.Prime.dvd_mul_of_dvd_ne : ∀ p1 p2 n, Not (Eq p1 p2) → prime_condition
/// p1 → prime_condition p2 → dvd p1 n → dvd p2 n → dvd (mul p1 p2) n`.
///
/// See [`NatPrelude::prime_dvd_mul_of_dvd_ne`] for the route:
/// [`coprime_primes`](NatPrelude::coprime_primes)'s `mpr` turns `p1 ≠ p2`
/// into `Coprime p1 p2`, then `coprime_mul_dvd` (`crt.rs`) combines the two
/// divisibility hypotheses. Declared after `declare_crt`, which is where
/// `coprime_mul_dvd` is proved.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_mul_of_dvd_ne(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_mul_of_dvd_ne, 3, &|d, v| {
        let (p1_var, p2_var, n_var) = (v[0], v[1], v[2]);
        let one = d.num(1);

        let eq_p1p2_ty = d.eq(p1_var, p2_var);
        let ne_ty = d.const_app(p.logic.not, &[eq_p1p2_ty]);
        let prime1_ty = prime_condition(d, &p, p1_var);
        let prime2_ty = prime_condition(d, &p, p2_var);
        let dvd1_ty = d.dvd(p1_var, n_var);
        let dvd2_ty = d.dvd(p2_var, n_var);
        let mul_p1p2 = d.mul(p1_var, p2_var);
        let concl = d.dvd(mul_p1p2, n_var);
        let stmt_inner4 = d.arrow(dvd2_ty, concl);
        let stmt_inner3 = d.arrow(dvd1_ty, stmt_inner4);
        let stmt_inner2 = d.arrow(prime2_ty, stmt_inner3);
        let stmt_inner1 = d.arrow(prime1_ty, stmt_inner2);
        let stmt = d.arrow(ne_ty, stmt_inner1);

        let ne_fv = d.fresh_fvar();
        let ne_hyp = d.kernel().fvar(ne_fv);
        let prime1_fv = d.fresh_fvar();
        let prime1_hyp = d.kernel().fvar(prime1_fv);
        let prime2_fv = d.fresh_fvar();
        let prime2_hyp = d.kernel().fvar(prime2_fv);
        let dvd1_fv = d.fresh_fvar();
        let dvd1_hyp = d.kernel().fvar(dvd1_fv);
        let dvd2_fv = d.fresh_fvar();
        let dvd2_hyp = d.kernel().fvar(dvd2_fv);

        let iff_pf = d.lemma(p.coprime_primes, &[p1_var, p2_var, prime1_hyp, prime2_hyp]);
        let gcd_p1p2 = d.gcd(p1_var, p2_var);
        let coprime_ty = d.eq(gcd_p1p2, one);
        let mpr_fn = iff_reverse(d, coprime_ty, ne_ty, iff_pf);
        let coprime_pf = d.apply(mpr_fn, &[ne_hyp]);

        let result = d.lemma(
            p.coprime_mul_dvd,
            &[p1_var, p2_var, n_var, coprime_pf, dvd1_hyp, dvd2_hyp],
        );

        let proof_inner4 = d.lam_fv(dvd2_fv, dvd2_ty, result);
        let proof_inner3 = d.lam_fv(dvd1_fv, dvd1_ty, proof_inner4);
        let proof_inner2 = d.lam_fv(prime2_fv, prime2_ty, proof_inner3);
        let proof_inner1 = d.lam_fv(prime1_fv, prime1_ty, proof_inner2);
        let proof = d.lam_fv(ne_fv, ne_ty, proof_inner1);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_two_left`/`Nat.coprime_two_right`/`Nat.Coprime.odd_of_left`/
// `Nat.Coprime.odd_of_right` — coprimality with `2` is exactly oddness.
// ============================================================================

/// `fun k : Nat => Eq n (add k k)` — rebuilt to match `parity.rs`'s private
/// `even_predicate` exactly (that helper is `fn`-private to its own file, so
/// `Even n`'s witness proofs here are built against an independently
/// constructed but structurally identical predicate; the same technique this
/// file already uses for `prime_condition`'s inner clause, e.g. in
/// [`declare_coprime_of_lt_prime`] and [`declare_prime_dvd_iff_not_coprime`]).
fn even_predicate_local(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let body = d.eq(n, kk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `dvd 2 n -> Even n`: eliminate the divisor witness `q` (`n = mul 2 q`,
/// `dvd_predicate`'s own witness shape) into the doubling witness `Even`
/// wants (`n = add q q`), bridged by [`two_mul_eq_add_self`](super::ops::two_mul_eq_add_self).
fn even_of_dvd_two(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, hdvd: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let two = d.num(2);

    let dvd_pred = d.dvd_predicate(two, n);
    let even_pred = even_predicate_local(d, n);
    let even_ty = d.lemma(p.even, &[n]);
    let dvd_ty = d.dvd(two, n);

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);
        let mul_two_q = d.mul(two, q);
        let hq_ty = d.eq(n, mul_two_q);

        let mul_eq_add = two_mul_eq_add_self(d, &p, q);
        let qq = d.add(q, q);
        let n_eq_qq = d.trans(n, mul_two_q, qq, hq, mul_eq_add);

        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let ev_proof = d.apply(intro, &[nat, even_pred, q, n_eq_qq]);
        let inner = d.lam_fv(hq_fv, hq_ty, ev_proof);
        d.lam_fv(q_fv, nat, inner)
    };
    let motive = d.kernel().lam(anon, dvd_ty, even_ty, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, dvd_pred, motive, minor, hdvd])
}

/// `Even n -> dvd 2 n`: eliminate the doubling witness `k` (`n = add k k`)
/// into the divisor witness `dvd`'s predicate wants (`n = mul 2 k`), bridged
/// by [`two_mul_eq_add_self`](super::ops::two_mul_eq_add_self).
fn dvd_two_of_even(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, heven: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let two = d.num(2);

    let even_pred = even_predicate_local(d, n);
    let dvd_pred = d.dvd_predicate(two, n);
    let even_ty = d.lemma(p.even, &[n]);
    let dvd_ty = d.dvd(two, n);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let kk = d.add(k, k);
        let hk_ty = d.eq(n, kk);

        let mul_eq_add = two_mul_eq_add_self(d, &p, k);
        let mul_two_k = d.mul(two, k);
        let add_eq_mul = d.symm(mul_two_k, kk, mul_eq_add);
        let n_eq_mul = d.trans(n, kk, mul_two_k, hk, add_eq_mul);

        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let dv_proof = d.apply(intro, &[nat, dvd_pred, k, n_eq_mul]);
        let inner = d.lam_fv(hk_fv, hk_ty, dv_proof);
        d.lam_fv(k_fv, nat, inner)
    };
    let motive = d.kernel().lam(anon, even_ty, dvd_ty, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, even_pred, motive, minor, heven])
}

/// `prime_condition(2)`: `2 ≤ 2` by `le_refl`, and its only divisors are `1`
/// and `2` — mirrors `irrational.rs`'s private `two_divisor_dichotomy` /
/// `perfect.rs`'s private `divisors_of_two`, a third copy since both are
/// `fn`-private to their own files. The divisor clause is rebuilt separately
/// (fresh `x_fv`, matching [`declare_coprime_of_lt_prime`]'s own "rebuilt to
/// match `prime_condition`'s inner shape exactly" clause) so the value's own
/// binder choice cannot matter — the kernel checks the value against this
/// type up to alpha-equivalence.
fn prime_two(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);

    let lower_ty = d.le(two, two);
    let divisors_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hyp = d.dvd(x, two);
        let is_one = d.eq(x, one);
        let is_two = d.eq(x, two);
        let disjunction = d.const_app(p.logic.or, &[is_one, is_two]);
        let inner = d.arrow(hyp, disjunction);
        d.pi_fv(x_fv, nat, inner)
    };

    let lower = d.const_app(p.le_refl, &[two]);

    let clause = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let dvd_c2 = d.dvd(c, two);

        let disjunction_proof = two_divisor_dichotomy(d, &p, c, hyp);

        let clause_body = d.lam_fv(hyp_fv, dvd_c2, disjunction_proof);
        d.lam_fv(c_fv, nat, clause_body)
    };

    d.const_app(p.logic.and_intro, &[lower_ty, divisors_ty, lower, clause])
}

/// `Nat.coprime_two_left : ∀ n, Iff (Eq (gcd two n) one) (Odd n)`.
///
/// `2` is prime ([`prime_two`]), so
/// [`NatPrelude::coprime_or_dvd_of_prime`] splits `gcd 2 n = 1 ∨ dvd 2 n`,
/// and [`NatPrelude::prime_dvd_iff_not_coprime`] relates `dvd 2 n` to
/// `Not (gcd 2 n = 1)`. [`even_of_dvd_two`]/[`dvd_two_of_even`] bridge
/// `dvd 2 n` and `Even n`, and [`NatPrelude::even_or_odd_exists`]/
/// [`NatPrelude::even_not_odd`] finish each direction by ruling out the even
/// case.
///
/// mp: given `h : gcd 2 n = 1`, case on `even_or_odd_exists n`. The `Odd n`
/// branch is the goal directly. The `Even n` branch builds `dvd 2 n`
/// ([`dvd_two_of_even`]), transports it through `prime_dvd_iff_not_coprime`'s
/// forward direction into `Not (gcd 2 n = 1)`, and applies that to `h` for
/// `False`.
///
/// mpr: given `ho : Odd n`, case on `coprime_or_dvd_of_prime 2 n prime_two`.
/// The `gcd 2 n = 1` branch is the goal directly. The `dvd 2 n` branch
/// builds `Even n` ([`even_of_dvd_two`]) and applies `even_not_odd n` to it
/// and `ho` for `False`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_two_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_two_left, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let gcd_2n = d.gcd(two, n);
        let cop_ty = d.eq(gcd_2n, one);
        let odd_ty = d.lemma(p.odd, &[n]);
        let stmt = d.const_app(p.logic.iff, &[cop_ty, odd_ty]);

        let prime2 = prime_two(d, &p);

        // mp : gcd 2 n = 1 -> Odd n
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let split = d.lemma(p.even_or_odd_exists, &[n]);
            let even_ty = d.lemma(p.even, &[n]);
            let dvd_ty = d.dvd(two, n);

            let on_even = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let dvd2n = dvd_two_of_even(d, &p, n, he);
                let iff_dvd_notcop = d.lemma(p.prime_dvd_iff_not_coprime, &[two, n, prime2]);
                let not_cop_ty = d.const_app(p.logic.not, &[cop_ty]);
                let mp_fn = iff_forward(d, dvd_ty, not_cop_ty, iff_dvd_notcop);
                let not_cop = d.apply(mp_fn, &[dvd2n]);
                let false_pf = d.apply(not_cop, &[h]);
                let body = absurd(d, odd_ty, false_pf);
                d.lam_fv(he_fv, even_ty, body)
            };
            let on_odd = {
                let ho_fv = d.fresh_fvar();
                let ho = d.kernel().fvar(ho_fv);
                d.lam_fv(ho_fv, odd_ty, ho)
            };
            let result = or_cases(d, even_ty, odd_ty, odd_ty, on_even, on_odd, split);
            d.lam_fv(h_fv, cop_ty, result)
        };

        // mpr : Odd n -> gcd 2 n = 1
        let mpr = {
            let ho_fv = d.fresh_fvar();
            let ho = d.kernel().fvar(ho_fv);

            let split = d.lemma(p.coprime_or_dvd_of_prime, &[two, n, prime2]);
            let dvd_ty = d.dvd(two, n);

            let on_cop = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                d.lam_fv(h_fv, cop_ty, h)
            };
            let on_dvd = {
                let hd_fv = d.fresh_fvar();
                let hd = d.kernel().fvar(hd_fv);
                let even_n = even_of_dvd_two(d, &p, n, hd);
                let not_odd_fn = d.lemma(p.even_not_odd, &[n]);
                let not_odd = d.apply(not_odd_fn, &[even_n]);
                let false_pf = d.apply(not_odd, &[ho]);
                let body = absurd(d, cop_ty, false_pf);
                d.lam_fv(hd_fv, dvd_ty, body)
            };
            let result = or_cases(d, cop_ty, dvd_ty, cop_ty, on_cop, on_dvd, split);
            d.lam_fv(ho_fv, odd_ty, result)
        };

        let proof = d.const_app(p.logic.iff_intro, &[cop_ty, odd_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.coprime_two_right : ∀ n, Iff (Eq (gcd n two) one) (Odd n)` —
/// [`declare_coprime_two_left`] composed with [`NatPrelude::coprime_symmetric`]
/// on both sides of the `Iff` to swap `gcd`'s argument order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_two_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_two_right, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let gcd_n2 = d.gcd(n, two);
        let gcd_2n = d.gcd(two, n);
        let cop_n2_ty = d.eq(gcd_n2, one);
        let cop_2n_ty = d.eq(gcd_2n, one);
        let odd_ty = d.lemma(p.odd, &[n]);
        let stmt = d.const_app(p.logic.iff, &[cop_n2_ty, odd_ty]);

        let left_iff = d.lemma(p.coprime_two_left, &[n]);

        // mp : gcd n 2 = 1 -> Odd n
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let flipped = d.lemma(p.coprime_symmetric, &[n, two, h]);
            let mp_fn = iff_forward(d, cop_2n_ty, odd_ty, left_iff);
            let result = d.apply(mp_fn, &[flipped]);
            d.lam_fv(h_fv, cop_n2_ty, result)
        };
        // mpr : Odd n -> gcd n 2 = 1
        let mpr = {
            let ho_fv = d.fresh_fvar();
            let ho = d.kernel().fvar(ho_fv);
            let mpr_fn = iff_reverse(d, cop_2n_ty, odd_ty, left_iff);
            let cop_2n = d.apply(mpr_fn, &[ho]);
            let flipped = d.lemma(p.coprime_symmetric, &[two, n, cop_2n]);
            d.lam_fv(ho_fv, odd_ty, flipped)
        };

        let proof = d.const_app(p.logic.iff_intro, &[cop_n2_ty, odd_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.odd_of_left : ∀ n, Eq (gcd two n) one → Odd n` — the `mp`
/// direction of [`declare_coprime_two_left`] alone.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_odd_of_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_odd_of_left, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let gcd_2n = d.gcd(two, n);
        let cop_ty = d.eq(gcd_2n, one);
        let odd_ty = d.lemma(p.odd, &[n]);
        let stmt = d.arrow(cop_ty, odd_ty);

        let iff_pf = d.lemma(p.coprime_two_left, &[n]);
        let proof = iff_forward(d, cop_ty, odd_ty, iff_pf);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.odd_of_right : ∀ n, Eq (gcd n two) one → Odd n` — the `mp`
/// direction of [`declare_coprime_two_right`] alone.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_odd_of_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_odd_of_right, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let gcd_n2 = d.gcd(n, two);
        let cop_ty = d.eq(gcd_n2, one);
        let odd_ty = d.lemma(p.odd, &[n]);
        let stmt = d.arrow(cop_ty, odd_ty);

        let iff_pf = d.lemma(p.coprime_two_right, &[n]);
        let proof = iff_forward(d, cop_ty, odd_ty, iff_pf);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_odd_of_ne_two` / `Nat.prime_even_iff` / `Nat.prime_not_dvd_mul` —
// Mathlib v4.30's `Nat.Prime.odd_of_ne_two`, `Nat.Prime.even_iff`,
// `Nat.Prime.not_dvd_mul`.
// ============================================================================

/// Shared case split for both `prime_odd_of_ne_two` and `prime_even_iff`:
/// `prime_condition p_var → Or (Eq (gcd p_var two) one) (dvd p_var two)`,
/// via [`declare_coprime_or_dvd_of_prime`] applied at `(p_var, two)`.
fn prime_vs_two_split(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_var: ExprId,
    prime_hyp: ExprId,
) -> ExprId {
    let two = d.num(2);
    d.lemma(p.coprime_or_dvd_of_prime, &[p_var, two, prime_hyp])
}

/// The `dvd p_var two` branch shared by both theorems below: `2`'s own
/// primality ([`prime_two`]) applied to `p_var` as a divisor gives
/// `p_var = 1 ∨ p_var = 2`.
fn dvd_two_disjunction(d: &mut NatDev<'_>, p: &NatPrelude, p_var: ExprId, hd: ExprId) -> ExprId {
    let two = d.num(2);
    let prime2 = prime_two(d, p);
    let (two_le_two, divisors_two) = prime_parts(d, p, two);
    let divisors_two_proof = and_right(d, two_le_two, divisors_two, prime2);
    d.apply(divisors_two_proof, &[p_var, hd])
}

/// The `p_var = 1` sub-branch shared by both theorems below: contradicts
/// `prime_hyp`'s own lower bound `2 ≤ p_var` (`le_of_succ_le_succ` +
/// `not_succ_le_zero`, mirroring [`declare_prime_dvd_iff_not_coprime`]'s
/// `mp` branch), refuting into `goal`.
fn refute_eq_one_against_prime_lower_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_var: ExprId,
    prime_hyp: ExprId,
    h1: ExprId,
    goal: ExprId,
) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let (lower_ty, divisors_ty) = prime_parts(d, p, p_var);
    let two_le_p = and_left(d, lower_ty, divisors_ty, prime_hyp);
    let motive = d.eq_motive(p_var, &|d, x| {
        let two = d.num(2);
        d.le(two, x)
    });
    let two_le_one = d.transport(p_var, motive, two_le_p, one, h1);
    let one_le_zero = d.lemma(p.le_of_succ_le_succ, &[one, zero, two_le_one]);
    let false_pf = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
    absurd(d, goal, false_pf)
}

/// `Nat.prime_odd_of_ne_two : ∀ p, prime_condition p → Not (Eq p two) →
/// Odd p`.
///
/// See [`NatPrelude::prime_odd_of_ne_two`] for the route: split on
/// [`prime_vs_two_split`]. `gcd p two = 1` gives `Odd p` directly via
/// [`declare_coprime_symmetric`] + [`declare_coprime_odd_of_left`].
/// `dvd p two` gives `p = 1 ∨ p = 2` via [`dvd_two_disjunction`]; `p = 1`
/// is refuted by [`refute_eq_one_against_prime_lower_bound`], and `p = 2`
/// contradicts the `Not (Eq p two)` hypothesis directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_odd_of_ne_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_odd_of_ne_two, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let one = d.num(1);

        let prime_ty = prime_condition(d, &p, p_var);
        let ne_ty = {
            let eq_ty = d.eq(p_var, two);
            d.const_app(p.logic.not, &[eq_ty])
        };
        let odd_ty = d.lemma(p.odd, &[p_var]);
        let stmt = {
            let inner = d.arrow(ne_ty, odd_ty);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let ne_fv = d.fresh_fvar();
        let ne_hyp = d.kernel().fvar(ne_fv);

        let split = prime_vs_two_split(d, &p, p_var, prime_hyp);
        let gcd_p2 = d.gcd(p_var, two);
        let cop_ty = d.eq(gcd_p2, one);
        let dvd_ty = d.dvd(p_var, two);

        let on_cop = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let flipped = d.lemma(p.coprime_symmetric, &[p_var, two, h]);
            let odd_pf = d.lemma(p.coprime_odd_of_left, &[p_var, flipped]);
            d.lam_fv(h_fv, cop_ty, odd_pf)
        };
        let on_dvd = {
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let disj2 = dvd_two_disjunction(d, &p, p_var, hd);
            let is_one_ty = d.eq(p_var, one);
            let is_two_ty = d.eq(p_var, two);
            let on_one = {
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let body =
                    refute_eq_one_against_prime_lower_bound(d, &p, p_var, prime_hyp, h1, odd_ty);
                d.lam_fv(h1_fv, is_one_ty, body)
            };
            let on_two = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let false_pf = d.apply(ne_hyp, &[h2]);
                let body = absurd(d, odd_ty, false_pf);
                d.lam_fv(h2_fv, is_two_ty, body)
            };
            let result = or_cases(d, is_one_ty, is_two_ty, odd_ty, on_one, on_two, disj2);
            d.lam_fv(hd_fv, dvd_ty, result)
        };
        let body = or_cases(d, cop_ty, dvd_ty, odd_ty, on_cop, on_dvd, split);
        let with_ne = d.lam_fv(ne_fv, ne_ty, body);
        let proof = d.lam_fv(prime_fv, prime_ty, with_ne);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_even_iff : ∀ p, prime_condition p → Iff (Even p) (Eq p two)`.
///
/// See [`NatPrelude::prime_even_iff`]. `mp` reuses
/// [`declare_prime_odd_of_ne_two`]'s exact case split: the
/// `gcd p two = 1` branch now derives `Odd p` and contradicts the
/// `Even p` hypothesis via [`NatPrelude::even_not_odd`] instead of closing
/// the goal directly; the `dvd p two` branch is unchanged except that its
/// `p = 2` sub-branch **is** the goal, not a contradiction. `mpr`
/// transports [`even_of_dvd_two`] applied to `2`'s self-divisibility
/// (`dvd_refl`) along the hypothesised `p = 2`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_even_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_even_iff, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let one = d.num(1);

        let prime_ty = prime_condition(d, &p, p_var);
        let even_ty = d.lemma(p.even, &[p_var]);
        let is_two_ty = d.eq(p_var, two);
        let iff_target = d.const_app(p.logic.iff, &[even_ty, is_two_ty]);
        let stmt = d.arrow(prime_ty, iff_target);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        // mp : Even p -> p = 2
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let split = prime_vs_two_split(d, &p, p_var, prime_hyp);
            let gcd_p2 = d.gcd(p_var, two);
            let cop_ty = d.eq(gcd_p2, one);
            let dvd_ty = d.dvd(p_var, two);

            let on_cop = {
                let hc_fv = d.fresh_fvar();
                let hc = d.kernel().fvar(hc_fv);
                let flipped = d.lemma(p.coprime_symmetric, &[p_var, two, hc]);
                let odd_pf = d.lemma(p.coprime_odd_of_left, &[p_var, flipped]);
                let not_odd_fn = d.lemma(p.even_not_odd, &[p_var]);
                let not_odd = d.apply(not_odd_fn, &[h]);
                let false_pf = d.apply(not_odd, &[odd_pf]);
                let body = absurd(d, is_two_ty, false_pf);
                d.lam_fv(hc_fv, cop_ty, body)
            };
            let on_dvd = {
                let hd_fv = d.fresh_fvar();
                let hd = d.kernel().fvar(hd_fv);
                let disj2 = dvd_two_disjunction(d, &p, p_var, hd);
                let is_one_ty = d.eq(p_var, one);
                let on_one = {
                    let h1_fv = d.fresh_fvar();
                    let h1 = d.kernel().fvar(h1_fv);
                    let body = refute_eq_one_against_prime_lower_bound(
                        d, &p, p_var, prime_hyp, h1, is_two_ty,
                    );
                    d.lam_fv(h1_fv, is_one_ty, body)
                };
                let on_two = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    d.lam_fv(h2_fv, is_two_ty, h2)
                };
                let result = or_cases(d, is_one_ty, is_two_ty, is_two_ty, on_one, on_two, disj2);
                d.lam_fv(hd_fv, dvd_ty, result)
            };
            let body = or_cases(d, cop_ty, dvd_ty, is_two_ty, on_cop, on_dvd, split);
            d.lam_fv(h_fv, even_ty, body)
        };

        // mpr : p = 2 -> Even p
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let dvd2_self = d.lemma(p.dvd_refl, &[two]);
            let even2 = even_of_dvd_two(d, &p, two, dvd2_self);
            let h_sym = d.symm(p_var, two, h);
            let motive = d.eq_motive(two, &|d, x| d.lemma(p.even, &[x]));
            let result = d.transport(two, motive, even2, p_var, h_sym);
            d.lam_fv(h_fv, is_two_ty, result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[even_ty, is_two_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_not_dvd_mul : ∀ p m n, prime_condition p → Not (dvd p m) →
/// Not (dvd p n) → Not (dvd p (mul m n))`.
///
/// The contrapositive of `euclid_lemma` (`bezout.rs`): assume
/// `dvd p (mul m n)`; `euclid_lemma` splits it into `dvd p m ∨ dvd p n`,
/// and each branch applies directly to one of the two `Not` hypotheses.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_not_dvd_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_not_dvd_mul, 3, &|d, v| {
        let (p_var, m_var, n_var) = (v[0], v[1], v[2]);

        let prime_ty = prime_condition(d, &p, p_var);
        let dvd_m_ty = d.dvd(p_var, m_var);
        let dvd_n_ty = d.dvd(p_var, n_var);
        let not_dvd_m_ty = d.const_app(p.logic.not, &[dvd_m_ty]);
        let not_dvd_n_ty = d.const_app(p.logic.not, &[dvd_n_ty]);
        let mn = d.mul(m_var, n_var);
        let dvd_mn_ty = d.dvd(p_var, mn);
        let not_dvd_mn_ty = d.const_app(p.logic.not, &[dvd_mn_ty]);

        let stmt = {
            let inner2 = d.arrow(not_dvd_n_ty, not_dvd_mn_ty);
            let inner1 = d.arrow(not_dvd_m_ty, inner2);
            d.arrow(prime_ty, inner1)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let nm_fv = d.fresh_fvar();
        let nm = d.kernel().fvar(nm_fv);
        let nn_fv = d.fresh_fvar();
        let nn = d.kernel().fvar(nn_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let split = d.lemma(p.euclid_lemma, &[p_var, m_var, n_var, prime_hyp, h]);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        let on_m = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let false_pf = d.apply(nm, &[hm]);
            d.lam_fv(hm_fv, dvd_m_ty, false_pf)
        };
        let on_n = {
            let hn_fv = d.fresh_fvar();
            let hn = d.kernel().fvar(hn_fv);
            let false_pf = d.apply(nn, &[hn]);
            d.lam_fv(hn_fv, dvd_n_ty, false_pf)
        };
        let cases_result = or_cases(d, dvd_m_ty, dvd_n_ty, false_ty, on_m, on_n, split);
        let not_dvd_mn = d.lam_fv(h_fv, dvd_mn_ty, cases_result);
        let with_nn = d.lam_fv(nn_fv, not_dvd_n_ty, not_dvd_mn);
        let with_nm = d.lam_fv(nm_fv, not_dvd_m_ty, with_nn);
        let proof = d.lam_fv(prime_fv, prime_ty, with_nm);
        (stmt, proof)
    })?;
    Ok(())
}

/// `dvd p_var one → False`, for a prime `p_var`: the same
/// `le_of_dvd`/`le_trans`/`le_of_succ_le_succ`/`not_succ_le_zero` route
/// [`declare_prime_dvd_iff_not_coprime`]'s `mp` branch already uses against
/// `p ≤ 1` (there reached through `p ∣ 1`), pulled out so
/// [`declare_prime_dvd_of_dvd_pow`]'s base case can reuse it directly.
fn refute_dvd_one_against_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_var: ExprId,
    prime_hyp: ExprId,
    dvd_p_one: ExprId,
) -> ExprId {
    let one = d.num(1);
    let two = d.num(2);
    let zero = d.zero();
    let (lower_ty, divisors_ty) = prime_parts(d, p, p_var);
    let two_le_p = and_left(d, lower_ty, divisors_ty, prime_hyp);
    let one_le_one = d.lemma(p.le_refl_thm, &[one]);
    let p_le_1 = d.lemma(p.le_of_dvd, &[p_var, one, one_le_one, dvd_p_one]);
    let two_le_1 = d.lemma(p.le_trans, &[two, p_var, one, two_le_p, p_le_1]);
    let one_le_zero = d.lemma(p.le_of_succ_le_succ, &[one, zero, two_le_1]);
    d.lemma(p.not_succ_le_zero, &[zero, one_le_zero])
}

/// `Nat.prime_dvd_of_dvd_pow : ∀ p m n, prime_condition p → dvd p (pow m n)
/// → dvd p m`.
///
/// See [`NatPrelude::prime_dvd_of_dvd_pow`] for the route: induction on `n`.
/// `n = 0`: `pow m 0 = 1` (`pow_zero`), and
/// [`refute_dvd_one_against_prime`] rules out `dvd p 1`, so the hypothesis
/// is vacuous. `n = succ j`: `pow m (succ j) = mul (pow m j) m`
/// (`pow_succ`), and `euclid_lemma` splits `dvd p (mul (pow m j) m)` into
/// `dvd p (pow m j) ∨ dvd p m` — the first branch applies the induction
/// hypothesis, the second **is** the goal.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_of_dvd_pow(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_of_dvd_pow, 3, &|d, v| {
        let (p_var, m_var, n_var) = (v[0], v[1], v[2]);

        let prime_ty = prime_condition(d, &p, p_var);
        let dvd_m_ty = d.dvd(p_var, m_var);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let pw = d.pow(m_var, x);
            let dvd_pw_ty = d.dvd(p_var, pw);
            d.arrow(dvd_pw_ty, dvd_m_ty)
        };

        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let one = d.num(1);
            let pw0 = d.pow(m_var, zero);
            let dvd_pw0_ty = d.dvd(p_var, pw0);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq_pf = d.lemma(p.pow_zero, &[m_var]);
            let motive = d.eq_motive(pw0, &|d, x| d.dvd(p_var, x));
            let dvd_one = d.transport(pw0, motive, h, one, eq_pf);
            let false_pf = refute_dvd_one_against_prime(d, &p, p_var, prime_hyp, dvd_one);
            let body = absurd(d, dvd_m_ty, false_pf);
            d.lam_fv(h_fv, dvd_pw0_ty, body)
        };

        let at_succ = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| {
            let sj = d.succ(j);
            let pw_sj = d.pow(m_var, sj);
            let dvd_pw_sj_ty = d.dvd(p_var, pw_sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let eq_pf = d.lemma(p.pow_succ, &[m_var, j]);
            let pw_j = d.pow(m_var, j);
            let prod = d.mul(pw_j, m_var);
            let motive = d.eq_motive(pw_sj, &|d, x| d.dvd(p_var, x));
            let dvd_prod = d.transport(pw_sj, motive, h, prod, eq_pf);

            let split = d.lemma(p.euclid_lemma, &[p_var, pw_j, m_var, prime_hyp, dvd_prod]);
            let dvd_pwj_ty = d.dvd(p_var, pw_j);

            let on_pwj = {
                let hh_fv = d.fresh_fvar();
                let hh = d.kernel().fvar(hh_fv);
                let result = d.apply(ih, &[hh]);
                d.lam_fv(hh_fv, dvd_pwj_ty, result)
            };
            let on_m = {
                let hm_fv = d.fresh_fvar();
                let hm = d.kernel().fvar(hm_fv);
                d.lam_fv(hm_fv, dvd_m_ty, hm)
            };
            let result = or_cases(d, dvd_pwj_ty, dvd_m_ty, dvd_m_ty, on_pwj, on_m, split);
            d.lam_fv(h_fv, dvd_pw_sj_ty, result)
        };

        let induction_proof = d.induct(&claim, &at_zero, &at_succ, n_var);

        let stmt = {
            let pw_n = d.pow(m_var, n_var);
            let dvd_pw_n_ty = d.dvd(p_var, pw_n);
            let inner = d.arrow(dvd_pw_n_ty, dvd_m_ty);
            d.arrow(prime_ty, inner)
        };
        let proof = d.lam_fv(prime_fv, prime_ty, induction_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_of_dvd' : ∀ m n, (∀ k, prime_condition k → dvd k m → dvd k n →
// dvd k one) → gcd m n = one`.
// ============================================================================

/// Eliminate `exists_proof : ∃ pw, prime_condition pw ∧ dvd pw target`,
/// continuing with the witness `pw` and the split-out `(prime_pw, dvd_pw_target)`
/// pair to build a proof of `goal` (which must not mention `pw`). Mirrors the
/// inline elimination [`declare_euclid`] already builds for the same
/// `exists_prime_dvd` result shape, pulled out because this file needs it a
/// second time.
fn eliminate_prime_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    target: ExprId,
    goal: ExprId,
    exists_proof: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let level = d.level_one();
    let anon = d.anon_name();
    let predicate = prime_divisor_predicate(d, &p, target);
    let source_ty = {
        let exists = d.kernel().const_(p.logic.exists_, vec![level]);
        d.apply(exists, &[nat, predicate])
    };
    let motive = d.kernel().lam(anon, source_ty, goal, BinderInfo::Default);
    let minor = {
        let pw_fv = d.fresh_fvar();
        let pw = d.kernel().fvar(pw_fv);
        let prime_pw_ty = prime_condition(d, &p, pw);
        let dvd_pw_target_ty = d.dvd(pw, target);
        let hpand_ty = d.const_app(p.logic.and, &[prime_pw_ty, dvd_pw_target_ty]);
        let hpand_fv = d.fresh_fvar();
        let hpand = d.kernel().fvar(hpand_fv);
        let prime_pw = and_left(d, prime_pw_ty, dvd_pw_target_ty, hpand);
        let dvd_pw_target = and_right(d, prime_pw_ty, dvd_pw_target_ty, hpand);
        let body = continuation(d, pw, prime_pw, dvd_pw_target);
        let with_hpand = d.lam_fv(hpand_fv, hpand_ty, body);
        d.lam_fv(pw_fv, nat, with_hpand)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level]);
    d.apply(exists_rec, &[nat, predicate, motive, minor, exists_proof])
}

/// See [`NatPrelude::coprime_of_forall_prime_dvd`] for the route. Trichotomy
/// on `g := gcd m n` via `lt_or_ge` twice:
///
/// - `g < 1` (so `g = 0`, via `le_of_succ_le_succ` + `zero_le` +
///   `le_antisymm`): `g ∣ m` and `g ∣ n` (`gcd_dvd_left`/`_right`) transport
///   along `g = 0` to `dvd 0 m`/`dvd 0 n`, which force `m = 0`/`n = 0`
///   (`zero_mul` on the witness, `dvd_elim`). Apply the hypothesis at `k = 2`
///   (`prime_two`, already proved in this file) -- `dvd 2 m`/`dvd 2 n` hold
///   trivially once `m`/`n` are `0` (`dvd_zero`) -- to get `dvd 2 one`, which
///   [`refute_dvd_one_against_prime`] refutes. `False.rec` closes this branch.
/// - `1 ≤ g` and `g < 2` (so `g = 1` directly via `le_of_succ_le_succ` +
///   `le_antisymm`): this **is** the goal.
/// - `1 ≤ g` and `2 ≤ g`: `exists_prime_dvd` gives a prime `pw ∣ g`, hence
///   `pw ∣ m` and `pw ∣ n` (`dvd_trans` through `gcd_dvd_left`/`_right`), so
///   the hypothesis gives `pw ∣ 1` -- refuted by
///   [`refute_dvd_one_against_prime`] again. `False.rec` closes this branch
///   too.
///
/// No case needs decidable equality or classical choice beyond the two
/// order trichotomies already proved (`lt_or_ge`); everything else is a
/// direct construction.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_of_forall_prime_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.coprime_of_forall_prime_dvd, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let g = d.gcd(m, n);
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();

        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let prime_k_ty = prime_condition(d, &p, k);
        let dvd_k_m_ty = d.dvd(k, m);
        let dvd_k_n_ty = d.dvd(k, n);
        let dvd_k_1_ty = d.dvd(k, one);
        let inner1 = d.arrow(dvd_k_n_ty, dvd_k_1_ty);
        let inner2 = d.arrow(dvd_k_m_ty, inner1);
        let body0 = d.arrow(prime_k_ty, inner2);
        let hyp_ty = d.pi_fv(k_fv, nat, body0);

        let target = d.eq(g, one);
        let stmt = d.arrow(hyp_ty, target);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let g_dvd_m = d.lemma(p.gcd_dvd_left, &[m, n]);
        let g_dvd_n = d.lemma(p.gcd_dvd_right, &[m, n]);

        let dich1 = d.lemma(p.lt_or_ge, &[g, one]); // Or (Lt g one) (Le one g)
        let lt_g1_ty = d.lt(g, one);
        let le_1g_ty = d.le(one, g);

        // Branch A: g < 1, i.e. g = 0. Forces m = n = 0, and the hypothesis
        // at k = 2 then contradicts itself.
        let branch_a = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let le_g_zero = d.lemma(p.le_of_succ_le_succ, &[g, zero, h]);
            let zero_le_g = d.lemma(p.zero_le, &[g]);
            let g_eq_zero = d.lemma(p.le_antisymm, &[g, zero, le_g_zero, zero_le_g]);

            let zero_dvd_m = transport_dvd_left(d, g, zero, g_eq_zero, m, g_dvd_m);
            let zero_dvd_n = transport_dvd_left(d, g, zero, g_eq_zero, n, g_dvd_n);

            let m_eq_zero_ty = d.eq(m, zero);
            let m_eq_zero = dvd_elim(d, zero, m, m_eq_zero_ty, zero_dvd_m, &|d, q, eq_m_0q| {
                let zero_q = d.mul(zero, q);
                let zero_mul_eq = d.lemma(p.zero_mul, &[q]);
                let (_, chained) = d.chain(m, &[(zero_q, eq_m_0q), (zero, zero_mul_eq)]);
                chained
            });
            let n_eq_zero_ty = d.eq(n, zero);
            let n_eq_zero = dvd_elim(d, zero, n, n_eq_zero_ty, zero_dvd_n, &|d, q, eq_n_0q| {
                let zero_q = d.mul(zero, q);
                let zero_mul_eq = d.lemma(p.zero_mul, &[q]);
                let (_, chained) = d.chain(n, &[(zero_q, eq_n_0q), (zero, zero_mul_eq)]);
                chained
            });

            let prime_2 = prime_two(d, &p);
            let dvd_2_zero = d.lemma(p.dvd_zero, &[two]);
            let eq_zero_m = d.symm(m, zero, m_eq_zero);
            let eq_zero_n = d.symm(n, zero, n_eq_zero);
            let dvd_2_m = transport_dvd_right(d, two, zero, m, eq_zero_m, dvd_2_zero);
            let dvd_2_n = transport_dvd_right(d, two, zero, n, eq_zero_n, dvd_2_zero);

            let hyp_at_2 = d.apply(hyp, &[two]);
            let step1 = d.apply(hyp_at_2, &[prime_2]);
            let step2 = d.apply(step1, &[dvd_2_m]);
            let dvd_2_1 = d.apply(step2, &[dvd_2_n]);

            let false_pf = refute_dvd_one_against_prime(d, &p, two, prime_2, dvd_2_1);
            let branch_proof = absurd(d, target, false_pf);
            d.lam_fv(h_fv, lt_g1_ty, branch_proof)
        };

        // Branch B: 1 ≤ g. Split again on g < 2 vs 2 ≤ g.
        let branch_b = {
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);

            let dich2 = d.lemma(p.lt_or_ge, &[g, two]); // Or (Lt g two) (Le two g)
            let lt_g2_ty = d.lt(g, two);
            let le_2g_ty = d.le(two, g);

            let branch_b1 = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let le_g_1 = d.lemma(p.le_of_succ_le_succ, &[g, one, h2]);
                let eq_g_1 = d.lemma(p.le_antisymm, &[g, one, le_g_1, h1]);
                d.lam_fv(h2_fv, lt_g2_ty, eq_g_1)
            };

            let branch_b2 = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let ex_proof = d.lemma(p.exists_prime_dvd, &[g, h2]);
                let branch_proof = eliminate_prime_dvd(
                    d,
                    &p,
                    g,
                    target,
                    ex_proof,
                    &|d, pw, prime_pw, dvd_pw_g| {
                        let dvd_pw_m = d.lemma(p.dvd_trans, &[pw, g, m, dvd_pw_g, g_dvd_m]);
                        let dvd_pw_n = d.lemma(p.dvd_trans, &[pw, g, n, dvd_pw_g, g_dvd_n]);
                        let hyp_at_pw = d.apply(hyp, &[pw]);
                        let step1 = d.apply(hyp_at_pw, &[prime_pw]);
                        let step2 = d.apply(step1, &[dvd_pw_m]);
                        let dvd_pw_1 = d.apply(step2, &[dvd_pw_n]);
                        let false_pf = refute_dvd_one_against_prime(d, &p, pw, prime_pw, dvd_pw_1);
                        absurd(d, target, false_pf)
                    },
                );
                d.lam_fv(h2_fv, le_2g_ty, branch_proof)
            };

            let body = or_cases(d, lt_g2_ty, le_2g_ty, target, branch_b1, branch_b2, dich2);
            d.lam_fv(h1_fv, le_1g_ty, body)
        };

        let body = or_cases(d, lt_g1_ty, le_1g_ty, target, branch_a, branch_b, dich1);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.dvd_of_forall_prime_mul_dvd : ∀ a b, (∀ k, prime_condition k → dvd k a
/// → dvd (mul k a) b) → dvd a b`. Closes ledger fact
/// `F:ml430-nat-dvd-of-forall-prime-mul-dvd`.
///
/// The hypothesis only needs to fire at ONE prime dividing `a` (any one), not
/// all of them, so no induction over `a`'s factorization is needed —
/// `a`'s only role is to be either `0`, `1`, or `≥ 2`:
///
/// - `a = 0`: apply the hypothesis at `k = 2` (`prime_two`, and `2 ∣ 0` via
///   `dvd_zero`) to get `dvd (2*0) b`; `2*0` computes to `0` (`mul_zero`), so
///   this is `dvd 0 b` — already the goal after substituting `a = 0`.
/// - `a = 1`: `dvd_mul` at `(one, b)` gives `dvd 1 (1*b)`, and `1*b = b`
///   (`one_mul`) — the hypothesis is not even needed.
/// - `a ≥ 2`: `exists_prime_dvd` supplies a prime `pw ∣ a`; the hypothesis at
///   `k = pw` gives `dvd (pw*a) b`. `dvd_mul` gives `dvd a (a*pw)`, and
///   `mul_comm` turns `pw*a` into `a*pw`, so `dvd_trans` chains
///   `a ∣ (a*pw) ∣ b`.
///
/// The same nested `lt_or_ge`-on-`a` trichotomy as
/// [`declare_coprime_of_forall_prime_dvd`] (`a < 1`, `1 ≤ a < 2`, `2 ≤ a`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_of_forall_prime_mul_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.dvd_of_forall_prime_mul_dvd, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();

        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let prime_k_ty = prime_condition(d, &p, k);
        let dvd_k_a_ty = d.dvd(k, a);
        let ka = d.mul(k, a);
        let dvd_ka_b_ty = d.dvd(ka, b);
        let inner1 = d.arrow(dvd_k_a_ty, dvd_ka_b_ty);
        let body0 = d.arrow(prime_k_ty, inner1);
        let hyp_ty = d.pi_fv(k_fv, nat, body0);

        let target = d.dvd(a, b);
        let stmt = d.arrow(hyp_ty, target);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let dich1 = d.lemma(p.lt_or_ge, &[a, one]); // Or (Lt a one) (Le one a)
        let lt_a1_ty = d.lt(a, one);
        let le_1a_ty = d.le(one, a);

        // Branch A: a < 1, i.e. a = 0.
        let branch_a = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let le_a_zero = d.lemma(p.le_of_succ_le_succ, &[a, zero, h]);
            let zero_le_a = d.lemma(p.zero_le, &[a]);
            let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, le_a_zero, zero_le_a]);
            let eq_zero_a = d.symm(a, zero, a_eq_zero); // Eq zero a

            let prime_2 = prime_two(d, &p);
            let dvd_2_zero = d.lemma(p.dvd_zero, &[two]); // dvd 2 zero
            let dvd_2_a = transport_dvd_right(d, two, zero, a, eq_zero_a, dvd_2_zero); // dvd 2 a

            let hyp_at_2 = d.apply(hyp, &[two]);
            let step1 = d.apply(hyp_at_2, &[prime_2]);
            let dvd_2a_b = d.apply(step1, &[dvd_2_a]); // dvd (2*a) b

            let two_a = d.mul(two, a);
            let two_zero = d.mul(two, zero);
            let step_congr = d.congr(a, zero, a_eq_zero, &|d, t| d.mul(two, t)); // Eq (2*a) (2*zero)
            let mul_zero_2 = d.lemma(p.mul_zero, &[two]); // Eq (2*zero) zero
            let (_, two_a_eq_zero) = d.chain(two_a, &[(two_zero, step_congr), (zero, mul_zero_2)]);

            let dvd_zero_b = transport_dvd_left(d, two_a, zero, two_a_eq_zero, b, dvd_2a_b); // dvd zero b
            let branch_proof = transport_dvd_left(d, zero, a, eq_zero_a, b, dvd_zero_b); // dvd a b
            d.lam_fv(h_fv, lt_a1_ty, branch_proof)
        };

        // Branch B: 1 ≤ a. Split again on a < 2 vs 2 ≤ a.
        let branch_b = {
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);

            let dich2 = d.lemma(p.lt_or_ge, &[a, two]); // Or (Lt a two) (Le two a)
            let lt_a2_ty = d.lt(a, two);
            let le_2a_ty = d.le(two, a);

            // Branch B1: a < 2 and 1 ≤ a, i.e. a = 1. The hypothesis is not
            // needed: `dvd_mul` alone gives `dvd 1 (1*b)`, and `1*b = b`.
            let branch_b1 = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let le_a_1 = d.lemma(p.le_of_succ_le_succ, &[a, one, h2]);
                let a_eq_1 = d.lemma(p.le_antisymm, &[a, one, le_a_1, h1]); // Eq a one
                let eq_1_a = d.symm(a, one, a_eq_1); // Eq one a

                let one_b = d.mul(one, b);
                let dvd_1_oneb = d.lemma(p.dvd_mul, &[one, b]); // dvd one (one*b)
                let one_mul_b = d.lemma(p.one_mul, &[b]); // Eq (one*b) b
                let dvd_1_b = transport_dvd_right(d, one, one_b, b, one_mul_b, dvd_1_oneb); // dvd one b
                let branch_proof = transport_dvd_left(d, one, a, eq_1_a, b, dvd_1_b); // dvd a b
                d.lam_fv(h2_fv, lt_a2_ty, branch_proof)
            };

            // Branch B2: 2 ≤ a. `exists_prime_dvd` supplies a prime `pw ∣ a`.
            let branch_b2 = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let ex_proof = d.lemma(p.exists_prime_dvd, &[a, h2]);
                let branch_proof = eliminate_prime_dvd(
                    d,
                    &p,
                    a,
                    target,
                    ex_proof,
                    &|d, pw, prime_pw, dvd_pw_a| {
                        let hyp_at_pw = d.apply(hyp, &[pw]);
                        let step1 = d.apply(hyp_at_pw, &[prime_pw]);
                        let dvd_pwa_b = d.apply(step1, &[dvd_pw_a]); // dvd (pw*a) b

                        let pw_a = d.mul(pw, a);
                        let a_pw = d.mul(a, pw);
                        let comm = d.lemma(p.mul_comm, &[pw, a]); // Eq (pw*a) (a*pw)
                        let dvd_apw_b = transport_dvd_left(d, pw_a, a_pw, comm, b, dvd_pwa_b); // dvd (a*pw) b
                        let dvd_a_apw = d.lemma(p.dvd_mul, &[a, pw]); // dvd a (a*pw)
                        d.lemma(p.dvd_trans, &[a, a_pw, b, dvd_a_apw, dvd_apw_b]) // dvd a b
                    },
                );
                d.lam_fv(h2_fv, le_2a_ty, branch_proof)
            };

            let body = or_cases(d, lt_a2_ty, le_2a_ty, target, branch_b1, branch_b2, dich2);
            d.lam_fv(h1_fv, le_1a_ty, body)
        };

        let body = or_cases(d, lt_a1_ty, le_1a_ty, target, branch_a, branch_b, dich1);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}
