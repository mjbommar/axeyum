//! Divisibility `Nat.dvd a n := exists q, n = a * q` and its laws.

use super::NatPrelude;
use super::division::declare_executable_division_spec;
use super::helpers::and_left;
use super::helpers::{iff_forward, iff_reverse, transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use super::steps::dvd_elim;
use super::steps::dvd_intro;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.dvd`, `dvd_mul`, and `dvd_add`, all constructed from the logic
/// prelude's checked `Exists` eliminator and the proved Nat multiplication
/// laws. No proposition is admitted as an axiom.
pub(super) fn declare_divisibility(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // dvd a n := Exists Nat (fun q => Eq Nat n (a * q))
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pred = d.dvd_predicate(a, n);
        let exists = d.kernel().const_(p.logic.exists_, vec![one]);
        let body = d.apply(exists, &[nat, pred]);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(a_fv, nat, inner)
        };
        let ty = {
            let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            d.kernel().pi(anon, nat, inner, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.dvd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // valuationAt a n e := dvd (a^e) n ∧ Not (dvd (a^(succ e)) n)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let power = d.pow(a, e);
        let se = d.succ(e);
        let next_power = d.pow(a, se);
        let divides = d.dvd(power, n);
        let next_divides = d.dvd(next_power, n);
        let not_next = d.const_app(p.logic.not, &[next_divides]);
        let body = d.const_app(p.logic.and, &[divides, not_next]);
        let value = {
            let with_e = d.lam_fv(e_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_e);
            d.lam_fv(a_fv, nat, with_n)
        };
        let ty = {
            let with_e = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_n = d.kernel().pi(anon, nat, with_e, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_n, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.valuation_at,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // div_mod_remainder_eq_zero_iff_dvd :
    //   ∀ d n q r, divMod d n q r → (r=0 ↔ dvd d n)
    // A zero remainder exposes q as a divisibility witness. Conversely, any
    // divisibility witness gives a zero-remainder decomposition; uniqueness
    // against the supplied decomposition forces its remainder to be zero.
    d.theorem(p.div_mod_remainder_eq_zero_iff_dvd, 4, &|d, v| {
        let (divisor, dividend, quotient, remainder) = (v[0], v[1], v[2], v[3]);
        let zero = d.zero();
        let product = d.mul(divisor, quotient);
        let reconstructed = d.add(product, remainder);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let zero_remainder_ty = d.eq(remainder, zero);
        let divides_ty = d.dvd(divisor, dividend);
        let target = d.const_app(p.logic.iff, &[zero_remainder_ty, divides_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, target, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);

            let forward = {
                let zero_remainder_fv = d.fresh_fvar();
                let zero_remainder = d.kernel().fvar(zero_remainder_fv);
                let product_plus_zero = d.add(product, zero);
                let replace_remainder =
                    d.congr(remainder, zero, zero_remainder, &|d, x| d.add(product, x));
                let remove_zero = d.lemma(p.add_zero, &[product]);
                let (_, witness_equation) = d.chain(
                    dividend,
                    &[
                        (reconstructed, equation),
                        (product_plus_zero, replace_remainder),
                        (product, remove_zero),
                    ],
                );
                let predicate = d.dvd_predicate(divisor, dividend);
                let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(exists_intro, &[nat, predicate, quotient, witness_equation]);
                d.lam_fv(zero_remainder_fv, zero_remainder_ty, body)
            };

            let reverse = {
                let divides_fv = d.fresh_fvar();
                let divides = d.kernel().fvar(divides_fv);
                let zero_le_remainder = d.lemma(p.zero_le, &[remainder]);
                let positive = d.lemma(
                    p.lt_of_le_of_lt,
                    &[zero, remainder, divisor, zero_le_remainder, bound],
                );
                let predicate = d.dvd_predicate(divisor, dividend);
                let exists_motive =
                    d.kernel()
                        .lam(anon, divides_ty, zero_remainder_ty, BinderInfo::Default);
                let exists_minor = {
                    let candidate_fv = d.fresh_fvar();
                    let candidate = d.kernel().fvar(candidate_fv);
                    let candidate_product = d.mul(divisor, candidate);
                    let witness_equation_fv = d.fresh_fvar();
                    let witness_equation_ty = d.eq(dividend, candidate_product);
                    let witness_equation = d.kernel().fvar(witness_equation_fv);
                    let candidate_plus_zero = d.add(candidate_product, zero);
                    let candidate_add_zero = d.lemma(p.add_zero, &[candidate_product]);
                    let candidate_add_zero_rev =
                        d.symm(candidate_plus_zero, candidate_product, candidate_add_zero);
                    let (_, zero_equation) = d.chain(
                        dividend,
                        &[
                            (candidate_product, witness_equation),
                            (candidate_plus_zero, candidate_add_zero_rev),
                        ],
                    );
                    let zero_equation_ty = d.eq(dividend, candidate_plus_zero);
                    let zero_bound_ty = d.lt(zero, divisor);
                    let zero_relation = d.const_app(
                        p.logic.and_intro,
                        &[zero_equation_ty, zero_bound_ty, zero_equation, positive],
                    );
                    let unique = d.lemma(
                        p.div_mod_unique,
                        &[
                            divisor,
                            dividend,
                            quotient,
                            remainder,
                            candidate,
                            zero,
                            relation,
                            zero_relation,
                        ],
                    );
                    let quotient_eq_ty = d.eq(quotient, candidate);
                    let unique_ty = d.const_app(p.logic.and, &[quotient_eq_ty, zero_remainder_ty]);
                    let unique_motive =
                        d.kernel()
                            .lam(anon, unique_ty, zero_remainder_ty, BinderInfo::Default);
                    let unique_minor = {
                        let quotient_eq_fv = d.fresh_fvar();
                        let remainder_eq_fv = d.fresh_fvar();
                        let remainder_eq = d.kernel().fvar(remainder_eq_fv);
                        let with_remainder =
                            d.lam_fv(remainder_eq_fv, zero_remainder_ty, remainder_eq);
                        d.lam_fv(quotient_eq_fv, quotient_eq_ty, with_remainder)
                    };
                    let level_zero = d.kernel().level_zero();
                    let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
                    let body = d.apply(
                        and_rec,
                        &[
                            quotient_eq_ty,
                            zero_remainder_ty,
                            unique_motive,
                            unique_minor,
                            unique,
                        ],
                    );
                    let with_equation = d.lam_fv(witness_equation_fv, witness_equation_ty, body);
                    d.lam_fv(candidate_fv, nat, with_equation)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, predicate, exists_motive, exists_minor, divides],
                );
                d.lam_fv(divides_fv, divides_ty, body)
            };

            let body = d.const_app(
                p.logic.iff_intro,
                &[zero_remainder_ty, divides_ty, forward, reverse],
            );
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                equation_ty,
                bound_ty,
                relation_motive,
                relation_minor,
                relation,
            ],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_exact_exists :
    //   ∀ d n, Le one d → dvd d n → ∃ q, divMod d n q zero
    // Eliminate the factorization witness and reuse it as the quotient. The
    // positive divisor hypothesis is definitionally the zero-remainder bound.
    d.theorem(p.div_mod_exact_exists, 2, &|d, v| {
        let (divisor, dividend) = (v[0], v[1]);
        let unit = d.num(1);
        let zero = d.zero();
        let positive_ty = d.le(unit, divisor);
        let divides_ty = d.dvd(divisor, dividend);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);

        let quotient_fv = d.fresh_fvar();
        let quotient = d.kernel().fvar(quotient_fv);
        let relation = d.div_mod(divisor, dividend, quotient, zero);
        let exact_predicate = d.lam_fv(quotient_fv, nat, relation);
        let exists = d.kernel().const_(p.logic.exists_, vec![one]);
        let target = d.apply(exists, &[nat, exact_predicate]);
        let divides_predicate = d.dvd_predicate(divisor, dividend);
        let exists_motive = d
            .kernel()
            .lam(anon, divides_ty, target, BinderInfo::Default);
        let exists_minor = {
            let candidate_fv = d.fresh_fvar();
            let candidate = d.kernel().fvar(candidate_fv);
            let product = d.mul(divisor, candidate);
            let witness_equation_fv = d.fresh_fvar();
            let witness_equation_ty = d.eq(dividend, product);
            let witness_equation = d.kernel().fvar(witness_equation_fv);
            let product_plus_zero = d.add(product, zero);
            let add_zero = d.lemma(p.add_zero, &[product]);
            let add_zero_rev = d.symm(product_plus_zero, product, add_zero);
            let (_, zero_equation) = d.chain(
                dividend,
                &[
                    (product, witness_equation),
                    (product_plus_zero, add_zero_rev),
                ],
            );
            let zero_equation_ty = d.eq(dividend, product_plus_zero);
            let zero_bound_ty = d.lt(zero, divisor);
            let exact_relation = d.const_app(
                p.logic.and_intro,
                &[zero_equation_ty, zero_bound_ty, zero_equation, positive],
            );
            let exact_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let body = d.apply(
                exact_intro,
                &[nat, exact_predicate, candidate, exact_relation],
            );
            let with_equation = d.lam_fv(witness_equation_fv, witness_equation_ty, body);
            d.lam_fv(candidate_fv, nat, with_equation)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[nat, divides_predicate, exists_motive, exists_minor, divides],
        );
        let divides_to_target = d.arrow(divides_ty, target);
        let stmt = d.arrow(positive_ty, divides_to_target);
        let with_divides = d.lam_fv(divides_fv, divides_ty, body);
        let proof = d.lam_fv(positive_fv, positive_ty, with_divides);
        (stmt, proof)
    })?;

    declare_executable_division_spec(d, &p, anon)?;

    // dvd_mul : ∀ a q, dvd a (a * q)
    d.theorem(p.dvd_mul, 2, &|d, v| {
        let (a, q) = (v[0], v[1]);
        let aq = d.mul(a, q);
        let stmt = d.dvd(a, aq);
        let pred = d.dvd_predicate(a, aq);
        let witness_proof = d.refl(aq);
        let one = d.level_one();
        let intro_name = d.prelude().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one]);
        let nat = d.nat_ty();
        let proof = d.apply(intro, &[nat, pred, q, witness_proof]);
        (stmt, proof)
    })?;

    d.theorem(p.dvd_refl, 1, &|d, v| {
        let a = v[0];
        let unit = d.num(1);
        let product = d.mul(a, unit);
        let product_eq = d.lemma(p.mul_one, &[a]);
        let witness_eq = d.symm(product, a, product_eq);
        let predicate = d.dvd_predicate(a, a);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let proof = d.apply(intro, &[nat, predicate, unit, witness_eq]);
        (d.dvd(a, a), proof)
    })?;

    // mod_self : ∀ n, mod n n = zero
    //
    // At zero this is the total division convention `mod 0 0 = 0`.  At a
    // successor, executable division supplies the checked quotient/remainder
    // relation; its zero-remainder characterization and reflexive divisibility
    // close the result.  Keeping this as an equality (rather than routing
    // through native `Nat.modEq`) matches the imported Mathlib `Nat.ModEq`
    // representation, which unfolds to equality of remainders.
    d.theorem(p.mod_self, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let self_remainder = d.modulo(n, n);
        let stmt = d.eq(self_remainder, zero);
        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let remainder = d.modulo(x, x);
            d.eq(remainder, zero)
        };
        // Use the numerator-zero law, whose proof transports across the
        // imported implementation.  The denominator-zero defining equation
        // is true natively but its reflexivity proof is representation-bound.
        let at_zero = |d: &mut NatDev<'_>| d.lemma(p.zero_mod, &[zero]);
        let at_succ = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| {
            let divisor = d.succ(k);
            let quotient = d.div(divisor, divisor);
            let remainder = d.modulo(divisor, divisor);
            let relation = d.lemma(p.div_mod_exec, &[k, divisor]);
            let characterization = d.lemma(
                p.div_mod_remainder_eq_zero_iff_dvd,
                &[divisor, divisor, quotient, remainder, relation],
            );
            let remainder_zero = d.eq(remainder, zero);
            let divides_self = d.dvd(divisor, divisor);
            let reverse = iff_reverse(d, remainder_zero, divides_self, characterization);
            let divides = d.lemma(p.dvd_refl, &[divisor]);
            d.apply(reverse, &[divides])
        };
        let proof = d.induct(&claim, &at_zero, &at_succ, n);
        (stmt, proof)
    })?;

    d.theorem(p.dvd_zero, 1, &|d, v| {
        let a = v[0];
        let zero = d.zero();
        let product = d.mul(a, zero);
        let product_eq = d.lemma(p.mul_zero, &[a]);
        let witness_eq = d.symm(product, zero, product_eq);
        let predicate = d.dvd_predicate(a, zero);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let proof = d.apply(intro, &[nat, predicate, zero, witness_eq]);
        (d.dvd(a, zero), proof)
    })?;

    // Divisibility transitivity composes the two existential factors and uses
    // associativity to expose their product as the new witness.
    d.theorem(p.dvd_trans, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let hab_ty = d.dvd(a, b);
        let hbc_ty = d.dvd(b, c);
        let target = d.dvd(a, c);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let hbc_fv = d.fresh_fvar();
        let hbc = d.kernel().fvar(hbc_fv);
        let pred_ab = d.dvd_predicate(a, b);
        let pred_bc = d.dvd_predicate(b, c);
        let motive_ab = d.kernel().lam(anon, hab_ty, target, BinderInfo::Default);
        let minor_ab = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let aq = d.mul(a, q);
            let eq_ab_fv = d.fresh_fvar();
            let eq_ab_ty = d.eq(b, aq);
            let eq_ab = d.kernel().fvar(eq_ab_fv);
            let motive_bc = d.kernel().lam(anon, hbc_ty, target, BinderInfo::Default);
            let minor_bc = {
                let r_fv = d.fresh_fvar();
                let r = d.kernel().fvar(r_fv);
                let br = d.mul(b, r);
                let eq_bc_fv = d.fresh_fvar();
                let eq_bc_ty = d.eq(c, br);
                let eq_bc = d.kernel().fvar(eq_bc_fv);
                let aqr = d.mul(aq, r);
                let qr = d.mul(q, r);
                let target_product = d.mul(a, qr);
                let replace_b = d.congr(b, aq, eq_ab, &|d, x| d.mul(x, r));
                let associate = d.lemma(p.mul_assoc, &[a, q, r]);
                let (_, witness_eq) = d.chain(
                    c,
                    &[(br, eq_bc), (aqr, replace_b), (target_product, associate)],
                );
                let predicate = d.dvd_predicate(a, c);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, predicate, qr, witness_eq]);
                let with_eq = d.lam_fv(eq_bc_fv, eq_bc_ty, body);
                d.lam_fv(r_fv, nat, with_eq)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(exists_rec, &[nat, pred_bc, motive_bc, minor_bc, hbc]);
            let with_eq = d.lam_fv(eq_ab_fv, eq_ab_ty, body);
            d.lam_fv(q_fv, nat, with_eq)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(exists_rec, &[nat, pred_ab, motive_ab, minor_ab, hab]);
        let proof = {
            let with_hbc = d.lam_fv(hbc_fv, hbc_ty, body);
            d.lam_fv(hab_fv, hab_ty, with_hbc)
        };
        let hbc_to_target = d.arrow(hbc_ty, target);
        let stmt = d.arrow(hab_ty, hbc_to_target);
        (stmt, proof)
    })?;

    // Multiplication on the right preserves divisibility by transitivity with
    // the canonical factor witness.
    d.theorem(p.dvd_mul_right_of_dvd, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let source = d.dvd(a, b);
        let target_product = d.mul(b, c);
        let target = d.dvd(a, target_product);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let b_divides_product = d.lemma(p.dvd_mul, &[b, c]);
        let body = d.lemma(
            p.dvd_trans,
            &[a, b, target_product, source_proof, b_divides_product],
        );
        let proof = d.lam_fv(source_fv, source, body);
        (d.arrow(source, target), proof)
    })?;

    // dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h1_ty = d.dvd(a, m);
        let h2_ty = d.dvd(a, n);
        let mn = d.add(m, n);
        let goal = d.dvd(a, mn);
        let p1 = d.dvd_predicate(a, m);
        let p2 = d.dvd_predicate(a, n);
        let one = d.level_one();

        let motive_for = |d: &mut NatDev<'_>, pred: ExprId| {
            let exists_name = d.prelude().logic.exists_;
            let exists = d.kernel().const_(exists_name, vec![one]);
            let nat = d.nat_ty();
            let dom = d.apply(exists, &[nat, pred]);
            let anon = d.anon_name();
            d.kernel().lam(anon, dom, goal, BinderInfo::Default)
        };

        let minor1 = {
            let q1_fv = d.fresh_fvar();
            let q1 = d.kernel().fvar(q1_fv);
            let aq1 = d.mul(a, q1);
            let e1_fv = d.fresh_fvar();
            let e1_ty = d.eq(m, aq1);
            let e1 = d.kernel().fvar(e1_fv);
            let minor2 = {
                let q2_fv = d.fresh_fvar();
                let q2 = d.kernel().fvar(q2_fv);
                let aq2 = d.mul(a, q2);
                let e2_fv = d.fresh_fvar();
                let e2_ty = d.eq(n, aq2);
                let e2 = d.kernel().fvar(e2_fv);

                // m+n = a*q1+n = a*q1+a*q2 = a*(q1+q2)
                let s1 = d.add(aq1, n);
                let c1 = d.congr(m, aq1, e1, &|d, t| d.add(t, n));
                let s2 = d.add(aq1, aq2);
                let c2 = d.congr(n, aq2, e2, &|d, t| d.add(aq1, t));
                let q12 = d.add(q1, q2);
                let aq12 = d.mul(a, q12);
                let h_distrib = d.lemma(p.left_distrib, &[a, q1, q2]);
                let c3 = d.symm(aq12, s2, h_distrib);
                let (_, witness_proof) = d.chain(mn, &[(s1, c1), (s2, c2), (aq12, c3)]);
                let pred = d.dvd_predicate(a, mn);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let nat = d.nat_ty();
                let body = d.apply(intro, &[nat, pred, q12, witness_proof]);
                let with_e2 = d.lam_fv(e2_fv, e2_ty, body);
                d.lam_fv(q2_fv, nat, with_e2)
            };
            let motive2 = motive_for(d, p2);
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let nat = d.nat_ty();
            let inner = d.apply(rec, &[nat, p2, motive2, minor2, h2]);
            let with_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, nat, with_e1)
        };
        let motive1 = motive_for(d, p1);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let proof = d.apply(rec, &[nat, p1, motive1, minor1, h1]);

        let ty = {
            let t = d.kernel().pi(anon, h2_ty, goal, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(n_fv, nat, t);
            let t = d.pi_fv(m_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, proof);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(n_fv, nat, v);
            let v = d.lam_fv(m_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        d.declare_theorem(p.dvd_add, ty, value)?;
    }

    // dvd_add_iff_right : dvd k m -> (dvd k n <-> dvd k (m+n)). The reverse
    // direction is all-Nat: subtract the factor for m from the factor for the
    // sum, using total truncated distributivity rather than a positivity case.
    d.theorem(p.dvd_add_iff_right, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let sum = d.add(m, n);
        let divides_m_ty = d.dvd(k, m);
        let divides_n_ty = d.dvd(k, n);
        let divides_sum_ty = d.dvd(k, sum);
        let iff_ty = d.const_app(p.logic.iff, &[divides_n_ty, divides_sum_ty]);
        let divides_m_fv = d.fresh_fvar();
        let divides_m = d.kernel().fvar(divides_m_fv);

        let forward = {
            let divides_n_fv = d.fresh_fvar();
            let divides_n = d.kernel().fvar(divides_n_fv);
            let body = d.lemma(p.dvd_add, &[k, m, n, divides_m, divides_n]);
            d.lam_fv(divides_n_fv, divides_n_ty, body)
        };

        let reverse = {
            let divides_sum_fv = d.fresh_fvar();
            let divides_sum = d.kernel().fvar(divides_sum_fv);
            let pred_m = d.dvd_predicate(k, m);
            let pred_sum = d.dvd_predicate(k, sum);
            let motive_m = d
                .kernel()
                .lam(anon, divides_m_ty, divides_n_ty, BinderInfo::Default);
            let minor_m = {
                let left_factor_fv = d.fresh_fvar();
                let left_factor = d.kernel().fvar(left_factor_fv);
                let k_left = d.mul(k, left_factor);
                let left_eq_fv = d.fresh_fvar();
                let left_eq_ty = d.eq(m, k_left);
                let left_eq = d.kernel().fvar(left_eq_fv);
                let motive_sum =
                    d.kernel()
                        .lam(anon, divides_sum_ty, divides_n_ty, BinderInfo::Default);
                let minor_sum = {
                    let sum_factor_fv = d.fresh_fvar();
                    let sum_factor = d.kernel().fvar(sum_factor_fv);
                    let k_sum = d.mul(k, sum_factor);
                    let sum_eq_fv = d.fresh_fvar();
                    let sum_eq_ty = d.eq(sum, k_sum);
                    let sum_eq = d.kernel().fvar(sum_eq_fv);
                    let factor_difference = d.sub(sum_factor, left_factor);
                    let k_difference = d.mul(k, factor_difference);
                    let sum_minus_m = d.sub(sum, m);
                    let ksum_minus_m = d.sub(k_sum, m);
                    let ksum_minus_kleft = d.sub(k_sum, k_left);
                    let cancel = d.lemma(p.add_sub_cancel_left, &[m, n]);
                    let n_to_difference = d.symm(sum_minus_m, n, cancel);
                    let replace_sum = d.congr(sum, k_sum, sum_eq, &|d, x| d.sub(x, m));
                    let replace_m = d.congr(m, k_left, left_eq, &|d, x| d.sub(k_sum, x));
                    let distribute =
                        d.lemma(p.mul_sub_left_distrib_total, &[k, sum_factor, left_factor]);
                    let undistribute = d.symm(k_difference, ksum_minus_kleft, distribute);
                    let (_, witness_eq) = d.chain(
                        n,
                        &[
                            (sum_minus_m, n_to_difference),
                            (ksum_minus_m, replace_sum),
                            (ksum_minus_kleft, replace_m),
                            (k_difference, undistribute),
                        ],
                    );
                    let predicate = d.dvd_predicate(k, n);
                    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                    let body = d.apply(intro, &[nat, predicate, factor_difference, witness_eq]);
                    let with_eq = d.lam_fv(sum_eq_fv, sum_eq_ty, body);
                    d.lam_fv(sum_factor_fv, nat, with_eq)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, pred_sum, motive_sum, minor_sum, divides_sum],
                );
                let with_eq = d.lam_fv(left_eq_fv, left_eq_ty, body);
                d.lam_fv(left_factor_fv, nat, with_eq)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(exists_rec, &[nat, pred_m, motive_m, minor_m, divides_m]);
            d.lam_fv(divides_sum_fv, divides_sum_ty, body)
        };

        let iff_proof = d.const_app(
            p.logic.iff_intro,
            &[divides_n_ty, divides_sum_ty, forward, reverse],
        );
        let proof = d.lam_fv(divides_m_fv, divides_m_ty, iff_proof);
        (d.arrow(divides_m_ty, iff_ty), proof)
    })?;

    // dvd_mod_iff : dvd k (succ d) ->
    //   (dvd k (mod n (succ d)) <-> dvd k n).
    // The executable division equation writes n as divisor*quotient+remainder;
    // `dvd_add_iff_right` removes that known divisible multiple in either
    // direction, including the k=0 corner.
    d.theorem(p.dvd_mod_iff, 3, &|d, v| {
        let (k, divisor_predecessor, dividend) = (v[0], v[1], v[2]);
        let divisor = d.succ(divisor_predecessor);
        let quotient = d.div(dividend, divisor);
        let remainder = d.modulo(dividend, divisor);
        let multiple = d.mul(divisor, quotient);
        let reconstructed = d.add(multiple, remainder);
        let divides_divisor_ty = d.dvd(k, divisor);
        let divides_remainder_ty = d.dvd(k, remainder);
        let divides_dividend_ty = d.dvd(k, dividend);
        let target = d.const_app(p.logic.iff, &[divides_remainder_ty, divides_dividend_ty]);
        let divides_divisor_fv = d.fresh_fvar();
        let divides_divisor = d.kernel().fvar(divides_divisor_fv);
        let divides_multiple = d.lemma(
            p.dvd_mul_right_of_dvd,
            &[k, divisor, quotient, divides_divisor],
        );
        let add_iff = d.lemma(
            p.dvd_add_iff_right,
            &[k, multiple, remainder, divides_multiple],
        );
        let divides_reconstructed_ty = d.dvd(k, reconstructed);
        let add_forward = iff_forward(d, divides_remainder_ty, divides_reconstructed_ty, add_iff);
        let add_reverse = iff_reverse(d, divides_remainder_ty, divides_reconstructed_ty, add_iff);

        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let relation_ty = d.const_app(p.logic.and, &[equation_ty, bound_ty]);
        let relation = d.lemma(p.div_mod_exec, &[divisor_predecessor, dividend]);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, equation_ty, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let with_bound = d.lam_fv(bound_fv, bound_ty, equation);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let zero_level = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![zero_level]);
        let equation = d.apply(
            and_rec,
            &[
                equation_ty,
                bound_ty,
                relation_motive,
                relation_minor,
                relation,
            ],
        );

        let forward = {
            let proof_fv = d.fresh_fvar();
            let proof = d.kernel().fvar(proof_fv);
            let reconstructed_proof = d.apply(add_forward, &[proof]);
            let equation_rev = d.symm(dividend, reconstructed, equation);
            let motive = d.eq_motive(reconstructed, &|d, value| d.dvd(k, value));
            let body = d.transport(
                reconstructed,
                motive,
                reconstructed_proof,
                dividend,
                equation_rev,
            );
            d.lam_fv(proof_fv, divides_remainder_ty, body)
        };
        let reverse = {
            let proof_fv = d.fresh_fvar();
            let proof = d.kernel().fvar(proof_fv);
            let motive = d.eq_motive(dividend, &|d, value| d.dvd(k, value));
            let reconstructed_proof = d.transport(dividend, motive, proof, reconstructed, equation);
            let body = d.apply(add_reverse, &[reconstructed_proof]);
            d.lam_fv(proof_fv, divides_dividend_ty, body)
        };
        let iff_proof = d.const_app(
            p.logic.iff_intro,
            &[divides_remainder_ty, divides_dividend_ty, forward, reverse],
        );
        let proof = d.lam_fv(divides_divisor_fv, divides_divisor_ty, iff_proof);
        (d.arrow(divides_divisor_ty, target), proof)
    })?;

    // dvd_add_right_cancel_of_pos :
    //   ∀ a m n, Le one a → dvd a m → dvd a (m+n) → dvd a n
    // Expose both divisibility witnesses. Order reflection proves the first
    // quotient is bounded by the second; their difference is then a witness
    // for `n`, after checked subtraction restoration and additive cancellation.
    d.theorem(p.dvd_add_right_cancel_of_pos, 3, &|d, v| {
        let (a, m, n) = (v[0], v[1], v[2]);
        let unit = d.num(1);
        let positive_ty = d.le(unit, a);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let divides_m_ty = d.dvd(a, m);
        let divides_m_fv = d.fresh_fvar();
        let divides_m = d.kernel().fvar(divides_m_fv);
        let mn = d.add(m, n);
        let divides_sum_ty = d.dvd(a, mn);
        let divides_sum_fv = d.fresh_fvar();
        let divides_sum = d.kernel().fvar(divides_sum_fv);
        let goal = d.dvd(a, n);
        let pred_m = d.dvd_predicate(a, m);
        let pred_sum = d.dvd_predicate(a, mn);

        let motive_for = |d: &mut NatDev<'_>, domain: ExprId| {
            d.kernel().lam(anon, domain, goal, BinderInfo::Default)
        };
        let minor_m = {
            let q1_fv = d.fresh_fvar();
            let q1 = d.kernel().fvar(q1_fv);
            let aq1 = d.mul(a, q1);
            let e1_fv = d.fresh_fvar();
            let e1_ty = d.eq(m, aq1);
            let e1 = d.kernel().fvar(e1_fv);
            let minor_sum = {
                let q2_fv = d.fresh_fvar();
                let q2 = d.kernel().fvar(q2_fv);
                let aq2 = d.mul(a, q2);
                let e2_fv = d.fresh_fvar();
                let e2_ty = d.eq(mn, aq2);
                let e2 = d.kernel().fvar(e2_fv);

                let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
                let aq1_le_sum = {
                    let motive = d.eq_motive(m, &|d, lower| d.le(lower, mn));
                    d.transport(m, motive, m_le_sum, aq1, e1)
                };
                let aq1_le_aq2 = {
                    let motive = d.eq_motive(mn, &|d, upper| d.le(aq1, upper));
                    d.transport(mn, motive, aq1_le_sum, aq2, e2)
                };
                let q1_le_q2 = d.lemma(p.le_of_mul_le_mul_left, &[a, q1, q2, positive, aq1_le_aq2]);

                let difference = d.sub(q2, q1);
                let a_difference = d.mul(a, difference);
                let scaled_difference = d.sub(aq2, aq1);
                let h_scaled_difference = d.lemma(p.mul_sub_left_distrib, &[a, q2, q1, q1_le_q2]);
                let restored = d.add(scaled_difference, aq1);
                let h_restored = d.lemma(p.sub_add_cancel, &[aq1, aq2, aq1_le_aq2]);

                let start = d.add(a_difference, m);
                let with_scaled_difference = d.add(scaled_difference, m);
                let h1 = d.congr(
                    a_difference,
                    scaled_difference,
                    h_scaled_difference,
                    &|d, x| d.add(x, m),
                );
                let h2 = d.congr(m, aq1, e1, &|d, x| d.add(scaled_difference, x));
                let aq2_eq_sum = d.symm(mn, aq2, e2);
                let n_plus_m = d.add(n, m);
                let h_sum_comm = d.lemma(p.add_comm, &[n, m]);
                let sum_eq_n_plus_m = d.symm(n_plus_m, mn, h_sum_comm);
                let (_, common_sum) = d.chain(
                    start,
                    &[
                        (with_scaled_difference, h1),
                        (restored, h2),
                        (aq2, h_restored),
                        (mn, aq2_eq_sum),
                        (n_plus_m, sum_eq_n_plus_m),
                    ],
                );
                let a_difference_eq_n =
                    d.lemma(p.add_right_cancel, &[a_difference, n, m, common_sum]);
                let witness_proof = d.symm(a_difference, n, a_difference_eq_n);
                let pred = d.dvd_predicate(a, n);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, pred, difference, witness_proof]);
                let with_e2 = d.lam_fv(e2_fv, e2_ty, body);
                d.lam_fv(q2_fv, nat, with_e2)
            };
            let motive_sum = motive_for(d, divides_sum_ty);
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let inner = d.apply(rec, &[nat, pred_sum, motive_sum, minor_sum, divides_sum]);
            let with_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, nat, with_e1)
        };
        let motive_m = motive_for(d, divides_m_ty);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, pred_m, motive_m, minor_m, divides_m]);
        let proof = {
            let with_sum = d.lam_fv(divides_sum_fv, divides_sum_ty, body);
            let with_m = d.lam_fv(divides_m_fv, divides_m_ty, with_sum);
            d.lam_fv(positive_fv, positive_ty, with_m)
        };
        let stmt = {
            let with_sum = d.arrow(divides_sum_ty, goal);
            let with_m = d.arrow(divides_m_ty, with_sum);
            d.arrow(positive_ty, with_m)
        };
        (stmt, proof)
    })?;

    // not_dvd_one_of_two_le : ∀ a, Le two a → Not (dvd a one)
    // Eliminate a hypothetical witness `one=a*q`, then inspect `q`. At zero
    // the equality makes one bounded by zero. At a successor, monotonicity
    // gives `a<=a*q=one`, contradicting `two<=a` after successor inversion.
    d.theorem(p.not_dvd_one_of_two_le, 1, &|d, v| {
        let a = v[0];
        let unit = d.num(1);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let divides_ty = d.dvd(a, unit);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let pred = d.dvd_predicate(a, unit);
        let motive = d
            .kernel()
            .lam(anon, divides_ty, false_ty, BinderInfo::Default);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let aq = d.mul(a, q);
            let e_fv = d.fresh_fvar();
            let e_ty = d.eq(unit, aq);
            let e = d.kernel().fvar(e_fv);
            let impossible_at = |d: &mut NatDev<'_>, x: ExprId| {
                let ax = d.mul(a, x);
                let equality = d.eq(unit, ax);
                d.arrow(equality, false_ty)
            };
            let at_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let e0_ty = d.eq(unit, zero);
                let e0_fv = d.fresh_fvar();
                let e0 = d.kernel().fvar(e0_fv);
                let reflexive = d.lemma(p.le_refl, &[unit]);
                let upper_motive = d.eq_motive(unit, &|d, upper| d.le(unit, upper));
                let one_le_zero = d.transport(unit, upper_motive, reflexive, zero, e0);
                let body = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
                d.lam_fv(e0_fv, e0_ty, body)
            };
            let at_succ = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| {
                let sj = d.succ(j);
                let asj = d.mul(a, sj);
                let es_ty = d.eq(unit, asj);
                let es_fv = d.fresh_fvar();
                let es = d.kernel().fvar(es_fv);
                let zero = d.zero();
                let one_le_sj = {
                    let zero_le_j = d.lemma(p.zero_le, &[j]);
                    d.lemma(p.le_succ_succ, &[zero, j, zero_le_j])
                };
                let a_one = d.mul(a, unit);
                let a_one_le_asj = d.lemma(p.mul_le_mul_left, &[a, unit, sj, one_le_sj]);
                let a_one_eq_a = d.lemma(p.mul_one, &[a]);
                let a_le_asj = {
                    let lower_motive = d.eq_motive(a_one, &|d, lower| d.le(lower, asj));
                    d.transport(a_one, lower_motive, a_one_le_asj, a, a_one_eq_a)
                };
                let asj_eq_one = d.symm(unit, asj, es);
                let a_le_one = {
                    let upper_motive = d.eq_motive(asj, &|d, upper| d.le(a, upper));
                    d.transport(asj, upper_motive, a_le_asj, unit, asj_eq_one)
                };
                let two_le_one = d.lemma(p.le_trans, &[two, a, unit, bound, a_le_one]);
                let one_le_zero = d.lemma(p.le_of_succ_le_succ, &[unit, zero, two_le_one]);
                let body = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
                d.lam_fv(es_fv, es_ty, body)
            };
            let body = d.induct(&impossible_at, &at_zero, &at_succ, q);
            let applied = d.apply(body, &[e]);
            let with_e = d.lam_fv(e_fv, e_ty, applied);
            d.lam_fv(q_fv, nat, with_e)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, pred, motive, minor, divides]);
        let proof = {
            let with_divides = d.lam_fv(divides_fv, divides_ty, body);
            d.lam_fv(bound_fv, bound_ty, with_divides)
        };
        let not_divides = d.const_app(p.logic.not, &[divides_ty]);
        let stmt = d.arrow(bound_ty, not_divides);
        (stmt, proof)
    })?;

    // eq_one_of_dvd_one : ∀ d, dvd d one → Eq d one
    // The closing step for coprimality after dividing by a gcd: once a common
    // divisor of the two quotients is shown to divide `1`, it *is* `1`.
    // Three cases. At zero the witness gives `1 = 0*q = 0`, which `le_refl`
    // transported into `not_succ_le_zero` refutes. At `succ zero` the goal is
    // `1 = 1`. At `succ (succ j)` the divisor is at least two, so
    // `not_dvd_one_of_two_le` contradicts the hypothesis outright.
    d.theorem(p.eq_one_of_dvd_one, 1, &|d, v| {
        let subject = v[0];
        let unit = d.num(1);
        let divides_ty = d.dvd(subject, unit);
        let conclusion = d.eq(subject, unit);
        let stmt = d.arrow(divides_ty, conclusion);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let unit = d.num(1);
            let hypothesis = d.dvd(x, unit);
            let target = d.eq(x, unit);
            d.arrow(hypothesis, target)
        };
        let explode = |d: &mut NatDev<'_>, goal: ExprId, contradiction: ExprId| {
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            d.apply(rec, &[motive, contradiction])
        };

        let at_zero = |d: &mut NatDev<'_>| {
            let nat = d.nat_ty();
            let one = d.level_one();
            let unit = d.num(1);
            let zero = d.zero();
            let hypothesis_ty = d.dvd(zero, unit);
            let hypothesis_fv = d.fresh_fvar();
            let hypothesis = d.kernel().fvar(hypothesis_fv);
            let goal = d.eq(zero, unit);
            let predicate = d.dvd_predicate(zero, unit);
            let anon = d.anon_name();
            let motive = d
                .kernel()
                .lam(anon, hypothesis_ty, goal, BinderInfo::Default);
            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let product = d.mul(zero, q);
                let equality_ty = d.eq(unit, product);
                let e_fv = d.fresh_fvar();
                let e = d.kernel().fvar(e_fv);
                // `0*q = 0`, so the witness equation collapses to `1 = 0`.
                let collapse = d.lemma(p.zero_mul, &[q]);
                let one_eq_zero = {
                    let motive = d.eq_motive(product, &|d, x| {
                        let unit = d.num(1);
                        d.eq(unit, x)
                    });
                    d.transport(product, motive, e, zero, collapse)
                };
                let reflexive = d.lemma(p.le_refl, &[unit]);
                let upper = d.eq_motive(unit, &|d, upper| {
                    let unit = d.num(1);
                    d.le(unit, upper)
                });
                let one_le_zero = d.transport(unit, upper, reflexive, zero, one_eq_zero);
                let contradiction = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
                let body = explode(d, goal, contradiction);
                let with_e = d.lam_fv(e_fv, equality_ty, body);
                d.lam_fv(q_fv, nat, with_e)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, predicate, motive, minor, hypothesis]);
            d.lam_fv(hypothesis_fv, hypothesis_ty, body)
        };

        let at_succ = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| {
            let inner_claim = |d: &mut NatDev<'_>, y: ExprId| {
                let successor = d.succ(y);
                let unit = d.num(1);
                let hypothesis = d.dvd(successor, unit);
                let target = d.eq(successor, unit);
                d.arrow(hypothesis, target)
            };
            let inner_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let successor = d.succ(zero);
                let unit = d.num(1);
                let hypothesis_ty = d.dvd(successor, unit);
                let hypothesis_fv = d.fresh_fvar();
                let reflexive = d.refl(successor);
                d.lam_fv(hypothesis_fv, hypothesis_ty, reflexive)
            };
            let inner_succ = |d: &mut NatDev<'_>, j: ExprId, _inner_ih: ExprId| {
                let zero = d.zero();
                let sj = d.succ(j);
                let ssj = d.succ(sj);
                let unit = d.num(1);
                let hypothesis_ty = d.dvd(ssj, unit);
                let hypothesis_fv = d.fresh_fvar();
                let hypothesis = d.kernel().fvar(hypothesis_fv);
                let two_le = {
                    let base = d.lemma(p.zero_le, &[j]);
                    let step = d.lemma(p.le_succ_succ, &[zero, j, base]);
                    let one = d.succ(zero);
                    d.lemma(p.le_succ_succ, &[one, sj, step])
                };
                let not_divides = d.lemma(p.not_dvd_one_of_two_le, &[ssj, two_le]);
                let contradiction = d.apply(not_divides, &[hypothesis]);
                let goal = d.eq(ssj, unit);
                let body = explode(d, goal, contradiction);
                d.lam_fv(hypothesis_fv, hypothesis_ty, body)
            };
            d.induct(&inner_claim, &inner_zero, &inner_succ, k)
        };

        let proof = d.induct(&claim, &at_zero, &at_succ, subject);
        (stmt, proof)
    })?;

    // not_dvd_one_add_mul_of_two_le :
    //   ∀ a t, Le two a → Not (dvd a (one+a*t))
    // A divisor of the whole sum also divides the multiple `a*t`; cancel it
    // with the preceding theorem and contradict nondivisibility of one.
    d.theorem(p.not_dvd_one_add_mul_of_two_le, 2, &|d, v| {
        let (a, t) = (v[0], v[1]);
        let unit = d.num(1);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let at = d.mul(a, t);
        let sum = d.add(unit, at);
        let divides_sum_ty = d.dvd(a, sum);
        let divides_sum_fv = d.fresh_fvar();
        let divides_sum = d.kernel().fvar(divides_sum_fv);

        let at_plus_one = d.add(at, unit);
        let sum_eq_reordered = d.lemma(p.add_comm, &[unit, at]);
        let reordered_divides = {
            let motive = d.eq_motive(sum, &|d, value| d.dvd(a, value));
            d.transport(sum, motive, divides_sum, at_plus_one, sum_eq_reordered)
        };
        let one_le_two = d.lemma(p.le_add_right, &[unit, unit]);
        let positive = d.lemma(p.le_trans, &[unit, two, a, one_le_two, bound]);
        let divides_at = d.lemma(p.dvd_mul, &[a, t]);
        let divides_one = d.lemma(
            p.dvd_add_right_cancel_of_pos,
            &[a, at, unit, positive, divides_at, reordered_divides],
        );
        let one_not_divides = d.lemma(p.not_dvd_one_of_two_le, &[a, bound]);
        let body = d.apply(one_not_divides, &[divides_one]);
        let proof = {
            let with_divides = d.lam_fv(divides_sum_fv, divides_sum_ty, body);
            d.lam_fv(bound_fv, bound_ty, with_divides)
        };
        let not_divides = d.const_app(p.logic.not, &[divides_sum_ty]);
        let stmt = d.arrow(bound_ty, not_divides);
        (stmt, proof)
    })?;

    // valuation_at_two_mul_sq :
    //   ∀ a u, Le two a → Not (dvd a u) → valuationAt a ((a*a)*u) two
    d.theorem(p.valuation_at_two_mul_sq, 2, &|d, v| {
        let (a, u) = (v[0], v[1]);
        let unit = d.num(1);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let a_dvd_u = d.dvd(a, u);
        let not_dvd_u_ty = d.const_app(p.logic.not, &[a_dvd_u]);
        let not_dvd_u_fv = d.fresh_fvar();
        let not_dvd_u = d.kernel().fvar(not_dvd_u_fv);

        let zero = d.zero();
        let one_exp = d.succ(zero);
        let two_exp = d.succ(one_exp);
        let three_exp = d.succ(two_exp);
        let pow0 = d.pow(a, zero);
        let pow1 = d.pow(a, one_exp);
        let pow2 = d.pow(a, two_exp);
        let pow3 = d.pow(a, three_exp);
        let aa = d.mul(a, a);
        let z = d.mul(aa, u);

        let pow1_step = d.mul(pow0, a);
        let one_a = d.mul(unit, a);
        let h_pow1_step = d.lemma(p.pow_succ, &[a, zero]);
        let h_pow0 = d.lemma(p.pow_zero, &[a]);
        let h_pow0_under_mul = d.congr(pow0, unit, h_pow0, &|d, x| d.mul(x, a));
        let h_one_mul = d.lemma(p.one_mul, &[a]);
        let (_, pow1_eq_a) = d.chain(
            pow1,
            &[
                (pow1_step, h_pow1_step),
                (one_a, h_pow0_under_mul),
                (a, h_one_mul),
            ],
        );
        let pow1_a = d.mul(pow1, a);
        let h_pow2_step = d.lemma(p.pow_succ, &[a, one_exp]);
        let h_pow1_under_mul = d.congr(pow1, a, pow1_eq_a, &|d, x| d.mul(x, a));
        let (_, pow2_eq_aa) = d.chain(pow2, &[(pow1_a, h_pow2_step), (aa, h_pow1_under_mul)]);

        let divides_aa = d.lemma(p.dvd_mul, &[aa, u]);
        let aa_eq_pow2 = d.symm(pow2, aa, pow2_eq_aa);
        let divides_pow2 = {
            let motive = d.eq_motive(aa, &|d, divisor| d.dvd(divisor, z));
            d.transport(aa, motive, divides_aa, pow2, aa_eq_pow2)
        };

        let pow2_a = d.mul(pow2, a);
        let cube = d.mul(aa, a);
        let h_pow3_step = d.lemma(p.pow_succ, &[a, two_exp]);
        let h_pow2_under_mul = d.congr(pow2, aa, pow2_eq_aa, &|d, x| d.mul(x, a));
        let (_, pow3_eq_cube) = d.chain(pow3, &[(pow2_a, h_pow3_step), (cube, h_pow2_under_mul)]);
        let pow3_dvd_z = d.dvd(pow3, z);
        let not_pow3_dvd_z = {
            let divides_fv = d.fresh_fvar();
            let divides = d.kernel().fvar(divides_fv);
            let cube_divides_ty = d.dvd(cube, z);
            let cube_divides = {
                let motive = d.eq_motive(pow3, &|d, divisor| d.dvd(divisor, z));
                d.transport(pow3, motive, divides, cube, pow3_eq_cube)
            };
            let pred = d.dvd_predicate(cube, z);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let motive = d
                .kernel()
                .lam(anon, cube_divides_ty, false_ty, BinderInfo::Default);
            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let cube_q = d.mul(cube, q);
                let e_fv = d.fresh_fvar();
                let e_ty = d.eq(z, cube_q);
                let e = d.kernel().fvar(e_fv);
                let aq = d.mul(a, q);
                let aa_aq = d.mul(aa, aq);
                let h_assoc = d.lemma(p.mul_assoc, &[aa, a, q]);
                let (_, common_product) = d.chain(z, &[(cube_q, e), (aa_aq, h_assoc)]);

                let one_le_two = d.lemma(p.le_add_right, &[unit, unit]);
                let one_le_a = d.lemma(p.le_trans, &[unit, two, a, one_le_two, bound]);
                let a_one = d.mul(a, unit);
                let a_one_le_aa = d.lemma(p.mul_le_mul_left, &[a, unit, a, one_le_a]);
                let a_one_eq_a = d.lemma(p.mul_one, &[a]);
                let a_le_aa = {
                    let lower_motive = d.eq_motive(a_one, &|d, lower| d.le(lower, aa));
                    d.transport(a_one, lower_motive, a_one_le_aa, a, a_one_eq_a)
                };
                let one_le_aa = d.lemma(p.le_trans, &[unit, a, aa, one_le_a, a_le_aa]);
                let u_eq_aq = d.lemma(
                    p.mul_left_cancel_of_pos,
                    &[aa, u, aq, one_le_aa, common_product],
                );
                let pred_u = d.dvd_predicate(a, u);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let a_dvd_u_proof = d.apply(intro, &[nat, pred_u, q, u_eq_aq]);
                let body = d.apply(not_dvd_u, &[a_dvd_u_proof]);
                let with_e = d.lam_fv(e_fv, e_ty, body);
                d.lam_fv(q_fv, nat, with_e)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, pred, motive, minor, cube_divides]);
            d.lam_fv(divides_fv, pow3_dvd_z, body)
        };

        let divides_pow2_ty = d.dvd(pow2, z);
        let next_not = d.const_app(p.logic.not, &[pow3_dvd_z]);
        let proof_pair = d.const_app(
            p.logic.and_intro,
            &[divides_pow2_ty, next_not, divides_pow2, not_pow3_dvd_z],
        );
        let conclusion = d.valuation_at(a, z, two);
        let proof = {
            let with_not_dvd = d.lam_fv(not_dvd_u_fv, not_dvd_u_ty, proof_pair);
            d.lam_fv(bound_fv, bound_ty, with_not_dvd)
        };
        let stmt = {
            let with_not_dvd = d.arrow(not_dvd_u_ty, conclusion);
            d.arrow(bound_ty, with_not_dvd)
        };
        (stmt, proof)
    })?;
    // div_mul_cancel_of_dvd : ∀ g n, 1 ≤ g → dvd g n → Eq (mul g (div n g)) n
    //
    // Exact division recovers its dividend. `Rat.normalize` divides a numerator
    // and denominator by their gcd and then has to say what the quotients
    // multiply back to; this is that step.
    //
    // `div_mod_exact_exists` gives a quotient with remainder ZERO, and
    // `div_mod_exec` gives the executable `div`/`mod` pair for the same inputs.
    // `div_mod_unique` identifies them, so the exact quotient IS `n / g`, and the
    // defining equation `n = g*q + 0` collapses by `add_zero`.
    d.theorem(p.div_mul_cancel_of_dvd, 2, &|d, values| {
        let (divisor, dividend) = (values[0], values[1]);
        let zero = d.zero();
        let unit = d.succ(zero);
        let positive_ty = d.le(unit, divisor);
        let divides_ty = d.dvd(divisor, dividend);
        let conclusion = {
            let quotient = d.div(dividend, divisor);
            let product = d.mul(divisor, quotient);
            d.eq(product, dividend)
        };
        let stmt = {
            let inner = d.arrow(divides_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let positive = d.le(unit, x);
            let divides = d.dvd(x, dividend);
            let quotient = d.div(dividend, x);
            let product = d.mul(x, quotient);
            let target = d.eq(product, dividend);
            let inner = d.arrow(divides, target);
            d.arrow(positive, inner)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let positive_ty = d.le(unit, zero);
            let divides_ty = d.dvd(zero, dividend);
            let quotient = d.div(dividend, zero);
            let product = d.mul(zero, quotient);
            let goal = d.eq(product, dividend);
            let positive_fv = d.fresh_fvar();
            let positive = d.kernel().fvar(positive_fv);
            let divides_fv = d.fresh_fvar();
            let contradiction = d.lemma(p.not_succ_le_zero, &[zero, positive]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            let with_divides = d.lam_fv(divides_fv, divides_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_divides)
        };
        let at_succ = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| {
            let nat = d.nat_ty();
            let one_level = d.level_one();
            let zero = d.zero();
            let unit = d.succ(zero);
            let divisor = d.succ(k);
            let positive_ty = d.le(unit, divisor);
            let divides_ty = d.dvd(divisor, dividend);
            let positive_fv = d.fresh_fvar();
            let positive = d.kernel().fvar(positive_fv);
            let divides_fv = d.fresh_fvar();
            let divides = d.kernel().fvar(divides_fv);

            let quotient = d.div(dividend, divisor);
            let remainder = d.modulo(dividend, divisor);
            let product = d.mul(divisor, quotient);
            let goal = d.eq(product, dividend);

            let exact = d.lemma(
                p.div_mod_exact_exists,
                &[divisor, dividend, positive, divides],
            );
            let executable = d.lemma(p.div_mod_exec, &[k, dividend]);

            // ∃ q, divMod divisor dividend q 0
            let predicate = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let body = d.div_mod(divisor, dividend, q, zero);
                d.lam_fv(q_fv, nat, body)
            };
            let exists_ty = {
                let exists = d.kernel().const_(p.logic.exists_, vec![one_level]);
                d.apply(exists, &[nat, predicate])
            };
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, exists_ty, goal, BinderInfo::Default);
            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let relation_ty = d.div_mod(divisor, dividend, q, zero);
                let relation_fv = d.fresh_fvar();
                let relation = d.kernel().fvar(relation_fv);

                // `divMod` unfolds to `(dividend = divisor*q + 0) ∧ (0 < divisor)`.
                let scaled = d.mul(divisor, q);
                let reconstructed = d.add(scaled, zero);
                let equation_ty = d.eq(dividend, reconstructed);
                let bound_ty = d.lt(zero, divisor);
                let equation = and_left(d, equation_ty, bound_ty, relation);

                // The exact quotient is the executable one.
                let uniqueness = d.lemma(
                    p.div_mod_unique,
                    &[
                        divisor, dividend, q, zero, quotient, remainder, relation, executable,
                    ],
                );
                let quotient_eq_ty = d.eq(q, quotient);
                let remainder_eq_ty = d.eq(zero, remainder);
                let quotient_eq = and_left(d, quotient_eq_ty, remainder_eq_ty, uniqueness);

                // dividend = divisor*q + 0 = divisor*q = divisor*(dividend/divisor)
                let collapse = d.lemma(p.add_zero, &[scaled]);
                let lifted = d.congr(q, quotient, quotient_eq, &|d, x| d.mul(divisor, x));
                let (_reached, chained) =
                    d.chain(reconstructed, &[(scaled, collapse), (product, lifted)]);
                let dividend_eq = d.trans(dividend, reconstructed, product, equation, chained);
                let body = d.symm(dividend, product, dividend_eq);
                let with_relation = d.lam_fv(relation_fv, relation_ty, body);
                d.lam_fv(q_fv, nat, with_relation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one_level]);
            let body = d.apply(rec, &[nat, predicate, motive, minor, exact]);
            let with_divides = d.lam_fv(divides_fv, divides_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_divides)
        };
        let proof = d.induct(&claim, &at_zero, &at_succ, divisor);
        (stmt, proof)
    })?;

    // one_le_right_of_mul : ∀ g q, 1 ≤ g * q → 1 ≤ q
    // A product cannot be positive with a zero factor; `mul_zero` closes it.
    d.theorem(p.one_le_right_of_mul, 2, &|d, values| {
        let (scale, factor) = (values[0], values[1]);
        let zero = d.zero();
        let unit = d.succ(zero);
        let product = d.mul(scale, factor);
        let hypothesis_ty = d.le(unit, product);
        let conclusion = d.le(unit, factor);
        let stmt = d.arrow(hypothesis_ty, conclusion);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let product = d.mul(scale, x);
            let hypothesis = d.le(unit, product);
            let target = d.le(unit, x);
            d.arrow(hypothesis, target)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let product = d.mul(scale, zero);
            let hypothesis_ty = d.le(unit, product);
            let goal = d.le(unit, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // `scale * 0 = 0`, so the hypothesis says `1 <= 0`.
            let collapse = d.lemma(p.mul_zero, &[scale]);
            let bounded = {
                let motive = d.eq_motive(product, &|d, x| {
                    let zero = d.zero();
                    let unit = d.succ(zero);
                    d.le(unit, x)
                });
                d.transport(product, motive, h, zero, collapse)
            };
            let contradiction = d.lemma(p.not_succ_le_zero, &[zero, bounded]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };
        let at_succ = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let successor = d.succ(j);
            let product = d.mul(scale, successor);
            let hypothesis_ty = d.le(unit, product);
            let h_fv = d.fresh_fvar();
            let base = d.lemma(p.zero_le, &[j]);
            let body = d.lemma(p.le_succ_succ, &[zero, j, base]);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };
        let proof = d.induct(&claim, &at_zero, &at_succ, factor);
        (stmt, proof)
    })?;

    // one_le_left_of_mul : ∀ g q, 1 ≤ g * q → 1 ≤ g
    // The mirror of the previous lemma, on the left factor; `zero_mul` closes it.
    d.theorem(p.one_le_left_of_mul, 2, &|d, values| {
        let (scale, factor) = (values[0], values[1]);
        let zero = d.zero();
        let unit = d.succ(zero);
        let product = d.mul(scale, factor);
        let hypothesis_ty = d.le(unit, product);
        let conclusion = d.le(unit, scale);
        let stmt = d.arrow(hypothesis_ty, conclusion);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let product = d.mul(x, factor);
            let hypothesis = d.le(unit, product);
            let target = d.le(unit, x);
            d.arrow(hypothesis, target)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let product = d.mul(zero, factor);
            let hypothesis_ty = d.le(unit, product);
            let goal = d.le(unit, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let collapse = d.lemma(p.zero_mul, &[factor]);
            let bounded = {
                let motive = d.eq_motive(product, &|d, x| {
                    let zero = d.zero();
                    let unit = d.succ(zero);
                    d.le(unit, x)
                });
                d.transport(product, motive, h, zero, collapse)
            };
            let contradiction = d.lemma(p.not_succ_le_zero, &[zero, bounded]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };
        let at_succ = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let successor = d.succ(j);
            let product = d.mul(successor, factor);
            let hypothesis_ty = d.le(unit, product);
            let h_fv = d.fresh_fvar();
            let base = d.lemma(p.zero_le, &[j]);
            let body = d.lemma(p.le_succ_succ, &[zero, j, base]);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };
        let proof = d.induct(&claim, &at_zero, &at_succ, scale);
        (stmt, proof)
    })?;

    // one_le_of_dvd_pos : ∀ g n, 1 ≤ n → dvd g n → 1 ≤ g
    // A divisor of a positive number is positive: the witness gives `n = g*q`,
    // and a zero divisor would force `n = 0`.
    d.theorem(p.one_le_of_dvd_pos, 2, &|d, values| {
        let (divisor, dividend) = (values[0], values[1]);
        let nat = d.nat_ty();
        let one_level = d.level_one();
        let zero = d.zero();
        let unit = d.succ(zero);
        let positive_ty = d.le(unit, dividend);
        let divides_ty = d.dvd(divisor, dividend);
        let conclusion = d.le(unit, divisor);
        let stmt = {
            let inner = d.arrow(divides_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);

        let predicate = d.dvd_predicate(divisor, dividend);
        let anon = d.anon_name();
        let motive = d
            .kernel()
            .lam(anon, divides_ty, conclusion, BinderInfo::Default);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let product = d.mul(divisor, q);
            let equation_ty = d.eq(dividend, product);
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            // `1 <= dividend = divisor*q`, so `1 <= divisor*q`.
            let scaled = {
                let motive = d.eq_motive(dividend, &|d, x| {
                    let zero = d.zero();
                    let unit = d.succ(zero);
                    d.le(unit, x)
                });
                d.transport(dividend, motive, positive, product, e)
            };
            let body = d.lemma(p.one_le_left_of_mul, &[divisor, q, scaled]);
            let with_e = d.lam_fv(e_fv, equation_ty, body);
            d.lam_fv(q_fv, nat, with_e)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one_level]);
        let body = d.apply(rec, &[nat, predicate, motive, minor, divides]);
        let proof = {
            let with_divides = d.lam_fv(divides_fv, divides_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_divides)
        };
        (stmt, proof)
    })?;

    // one_le_mul : ∀ a b, 1 ≤ a → 1 ≤ b → 1 ≤ a * b
    // Case on the RIGHT factor: at zero the second hypothesis is absurd, and at
    // a successor `a * succ j = a*j + a` is at least `a`, which is at least 1.
    d.theorem(p.one_le_mul, 2, &|d, values| {
        let (left, right) = (values[0], values[1]);
        let zero = d.zero();
        let unit = d.succ(zero);
        let left_ty = d.le(unit, left);
        let right_ty = d.le(unit, right);
        let product = d.mul(left, right);
        let conclusion = d.le(unit, product);
        let stmt = {
            let inner = d.arrow(right_ty, conclusion);
            d.arrow(left_ty, inner)
        };

        let left_fv = d.fresh_fvar();
        let left_positive = d.kernel().fvar(left_fv);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let hypothesis = d.le(unit, x);
            let product = d.mul(left, x);
            let target = d.le(unit, product);
            d.arrow(hypothesis, target)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let hypothesis_ty = d.le(unit, zero);
            let product = d.mul(left, zero);
            let goal = d.le(unit, product);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let contradiction = d.lemma(p.not_succ_le_zero, &[zero, h]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };
        let at_succ = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| {
            let zero = d.zero();
            let unit = d.succ(zero);
            let successor = d.succ(j);
            let hypothesis_ty = d.le(unit, successor);
            let h_fv = d.fresh_fvar();

            // 1 <= left <= left + left*j = left*j + left = left * succ j
            let scaled = d.mul(left, j);
            let shifted = d.add(left, scaled);
            let reach = d.lemma(p.le_add_right, &[left, scaled]);
            let bounded = d.lemma(p.le_trans, &[unit, left, shifted, left_positive, reach]);
            let swapped = d.add(scaled, left);
            let commute = d.lemma(p.add_comm, &[left, scaled]);
            let product = d.mul(left, successor);
            let expand = d.lemma(p.mul_succ, &[left, j]);
            let back = d.symm(product, swapped, expand);
            let (_reached, chained) = d.chain(shifted, &[(swapped, commute), (product, back)]);
            let motive = d.eq_motive(shifted, &|d, x| {
                let zero = d.zero();
                let unit = d.succ(zero);
                d.le(unit, x)
            });
            let body = d.transport(shifted, motive, bounded, product, chained);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };
        let selected = d.induct(&claim, &at_zero, &at_succ, right);
        let proof = d.lam_fv(left_fv, left_ty, selected);
        (stmt, proof)
    })?;

    // dvd_factorial_of_le : ∀ d n, 1 ≤ d → d ≤ n → dvd d (factorial n)
    //
    // The first of the two ingredients Euclid's theorem (`F:nat-exists-prime-gt`)
    // is missing: a single number that EVERY positive `d ≤ n` divides. Combined
    // with the already-proved `not_dvd_one_add_mul_of_two_le` it is what makes
    // `1 + n!` have no divisor in `[2, n]`; the remaining gap is "every `m ≥ 2`
    // has a prime divisor", which needs minimisation over `lt_well_founded`.
    //
    // Induction on `n`, with the ORDER hypothesis inside the motive (the
    // positivity hypothesis is fixed and stays outside), because the step needs
    // to apply the induction hypothesis at a strictly smaller bound:
    //
    //   zero    `d ≤ 0` and `1 ≤ d` chain to `1 ≤ 0`, which `not_succ_le_zero`
    //           refutes; `False.rec` supplies the goal.
    //   succ j  `lt_or_eq_of_le` splits `d ≤ succ j` into `d < succ j` or
    //           `d = succ j`. `factorial (succ j) ≡ factorial j * succ j` holds
    //           DEFINITIONALLY, so neither branch rewrites the goal to reach it:
    //             * `d < succ j` is `succ d ≤ succ j`, so `le_of_succ_le_succ`
    //               gives `d ≤ j`, the induction hypothesis gives
    //               `d ∣ factorial j`, and `dvd_mul_right_of_dvd` multiplies by
    //               `succ j`;
    //             * `d = succ j` uses `dvd_mul (succ j) (factorial j)`, commutes
    //               the product into the definitional shape, and transports the
    //               divisor back along `succ j = d` — note the `symm`, since the
    //               branch hypothesis reads `d = succ j` and the transport has to
    //               run the other way.
    d.theorem(p.dvd_factorial_of_le, 2, &|d, values| {
        let (divisor, bound) = (values[0], values[1]);
        let zero = d.zero();
        let unit = d.succ(zero);
        let positive_ty = d.le(unit, divisor);
        let order_ty = d.le(divisor, bound);
        let conclusion = {
            let target = d.factorial(bound);
            d.dvd(divisor, target)
        };
        let stmt = {
            let inner = d.arrow(order_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);

        // The motive carries the order hypothesis so the step can weaken it.
        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let hypothesis = d.le(divisor, x);
            let factorial = d.factorial(x);
            let target = d.dvd(divisor, factorial);
            d.arrow(hypothesis, target)
        };

        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let hypothesis_ty = d.le(divisor, zero);
            let goal = {
                let factorial = d.factorial(zero);
                d.dvd(divisor, factorial)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // 1 ≤ divisor ≤ 0, i.e. `Le (succ zero) zero`, which is refutable.
            let unit = d.succ(zero);
            let one_le_zero = d.lemma(p.le_trans, &[unit, divisor, zero, positive, h]);
            let contradiction = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            d.lam_fv(h_fv, hypothesis_ty, body)
        };

        let at_succ = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| {
            let successor = d.succ(j);
            let hypothesis_ty = d.le(divisor, successor);
            let target = {
                let factorial = d.factorial(successor);
                d.dvd(divisor, factorial)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let strict_ty = d.lt(divisor, successor);
            let equal_ty = d.eq(divisor, successor);
            let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
            let split = d.lemma(p.lt_or_eq_of_le, &[divisor, successor, h]);
            let anon = d.anon_name();
            let split_motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);

            // `d < succ j` unfolds to `succ d ≤ succ j`, so the bound drops to `j`.
            let strict_minor = {
                let strict_fv = d.fresh_fvar();
                let strict = d.kernel().fvar(strict_fv);
                let smaller = d.lemma(p.le_of_succ_le_succ, &[divisor, j, strict]);
                let inherited = d.apply(ih, &[smaller]);
                let prior = d.factorial(j);
                // `factorial j * succ j` IS `factorial (succ j)` definitionally.
                let body = d.lemma(
                    p.dvd_mul_right_of_dvd,
                    &[divisor, prior, successor, inherited],
                );
                d.lam_fv(strict_fv, strict_ty, body)
            };

            // `d = succ j`: the last factor of `factorial (succ j)` is the divisor.
            let equal_minor = {
                let equal_fv = d.fresh_fvar();
                let equal = d.kernel().fvar(equal_fv);
                let prior = d.factorial(j);
                let left_product = d.mul(successor, prior);
                let right_product = d.mul(prior, successor);
                let canonical = d.lemma(p.dvd_mul, &[successor, prior]);
                let commute = d.lemma(p.mul_comm, &[successor, prior]);
                let reoriented = {
                    let motive = d.eq_motive(left_product, &|d, x| d.dvd(successor, x));
                    d.transport(left_product, motive, canonical, right_product, commute)
                };
                // `equal : d = succ j`, and the transport replaces `succ j` by
                // `d`, so it needs the equation the OTHER way round.
                let reverse = d.symm(divisor, successor, equal);
                let motive = d.eq_motive(successor, &|d, x| {
                    let factorial = d.factorial(successor);
                    d.dvd(x, factorial)
                });
                let body = d.transport(successor, motive, reoriented, divisor, reverse);
                d.lam_fv(equal_fv, equal_ty, body)
            };

            let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                or_rec,
                &[
                    strict_ty,
                    equal_ty,
                    split_motive,
                    strict_minor,
                    equal_minor,
                    split,
                ],
            );
            d.lam_fv(h_fv, hypothesis_ty, body)
        };

        let selected = d.induct(&claim, &at_zero, &at_succ, bound);
        let proof = d.lam_fv(positive_fv, positive_ty, selected);
        (stmt, proof)
    })?;

    // factorial_dvd_factorial : ∀ m n, Le m n → dvd (factorial m) (factorial n)
    //
    // Induction on `n`, with the order hypothesis inside the motive (same
    // shape as `dvd_factorial_of_le` above). The `at_succ` branch is IDENTICAL
    // to that theorem's — it never touched the divisor's positivity, only the
    // order hypothesis — so it is repeated verbatim with `divisor` renamed to
    // `m`. The `at_zero` branch differs: there is no fixed `1 ≤ m` here to
    // contradict `m ≤ 0` outright, since `m = 0` is a real case (`0! ∣ 0!` by
    // `dvd_refl`). So it case-splits on `m` itself via a NESTED induction:
    // `m = 0` closes by `dvd_refl`, and `m = succ j` makes `Le (succ j) 0`
    // refutable by `not_succ_le_zero`, exactly as the divisor-positivity
    // branch above does for a different hypothesis.
    d.theorem(p.factorial_dvd_factorial, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let stmt = {
            let hyp = d.le(m, n);
            let mfact = d.factorial(m);
            let nfact = d.factorial(n);
            let concl = d.dvd(mfact, nfact);
            d.arrow(hyp, concl)
        };

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let hypothesis = d.le(m, x);
            let mfact = d.factorial(m);
            let factorial = d.factorial(x);
            let target = d.dvd(mfact, factorial);
            d.arrow(hypothesis, target)
        };

        let at_zero = |d: &mut NatDev<'_>| {
            // Inner induction on `m`, proving `Le x zero -> dvd(factorial x, factorial zero)`.
            let inner_claim = |d: &mut NatDev<'_>, x: ExprId| {
                let zero = d.zero();
                let hypothesis = d.le(x, zero);
                let xfact = d.factorial(x);
                let zfact = d.factorial(zero);
                let target = d.dvd(xfact, zfact);
                d.arrow(hypothesis, target)
            };
            let inner_at_zero = |d: &mut NatDev<'_>| {
                let h_fv = d.fresh_fvar();
                let zero = d.zero();
                let hypothesis_ty = d.le(zero, zero);
                let zfact = d.factorial(zero);
                let refl = d.lemma(p.dvd_refl, &[zfact]);
                d.lam_fv(h_fv, hypothesis_ty, refl)
            };
            let inner_at_succ = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let zero = d.zero();
                let successor = d.succ(j);
                let hypothesis_ty = d.le(successor, zero);
                let contradiction = d.lemma(p.not_succ_le_zero, &[j, h]);
                let goal = {
                    let sfact = d.factorial(successor);
                    let zfact = d.factorial(zero);
                    d.dvd(sfact, zfact)
                };
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let level = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
                let anon = d.anon_name();
                let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
                let body = d.apply(rec, &[motive, contradiction]);
                d.lam_fv(h_fv, hypothesis_ty, body)
            };
            d.induct(&inner_claim, &inner_at_zero, &inner_at_succ, m)
        };

        let at_succ = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| {
            let successor = d.succ(j);
            let hypothesis_ty = d.le(m, successor);
            let target = {
                let mfact = d.factorial(m);
                let factorial = d.factorial(successor);
                d.dvd(mfact, factorial)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let strict_ty = d.lt(m, successor);
            let equal_ty = d.eq(m, successor);
            let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
            let split = d.lemma(p.lt_or_eq_of_le, &[m, successor, h]);
            let anon = d.anon_name();
            let split_motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);

            // `m < succ j` unfolds to `succ m ≤ succ j`, so the bound drops to `j`.
            // NOTE: unlike `dvd_factorial_of_le`, the thing dividing is
            // `factorial m`, not `m` itself — `dvd_mul_right_of_dvd`'s first
            // argument must be `factorial m`.
            let strict_minor = {
                let strict_fv = d.fresh_fvar();
                let strict = d.kernel().fvar(strict_fv);
                let smaller = d.lemma(p.le_of_succ_le_succ, &[m, j, strict]);
                let inherited = d.apply(ih, &[smaller]);
                let mfact = d.factorial(m);
                let prior = d.factorial(j);
                let body = d.lemma(
                    p.dvd_mul_right_of_dvd,
                    &[mfact, prior, successor, inherited],
                );
                d.lam_fv(strict_fv, strict_ty, body)
            };

            // `m = succ j`: `factorial m = factorial (succ j)` by congruence on
            // `equal`, and `dvd_refl (factorial (succ j))` transported along its
            // reverse gives `dvd (factorial m) (factorial (succ j))`.
            let equal_minor = {
                let equal_fv = d.fresh_fvar();
                let equal = d.kernel().fvar(equal_fv);
                let mfact = d.factorial(m);
                let sfact = d.factorial(successor);
                let fact_eq = d.congr(m, successor, equal, &|d, x| d.factorial(x));
                let fact_reverse = d.symm(mfact, sfact, fact_eq);
                let refl_s = d.lemma(p.dvd_refl, &[sfact]);
                let motive = d.eq_motive(sfact, &|d, x| {
                    let sfact = d.factorial(successor);
                    d.dvd(x, sfact)
                });
                let body = d.transport(sfact, motive, refl_s, mfact, fact_reverse);
                d.lam_fv(equal_fv, equal_ty, body)
            };

            let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                or_rec,
                &[
                    strict_ty,
                    equal_ty,
                    split_motive,
                    strict_minor,
                    equal_minor,
                    split,
                ],
            );
            d.lam_fv(h_fv, hypothesis_ty, body)
        };

        let selected = d.induct(&claim, &at_zero, &at_succ, n);
        (stmt, selected)
    })?;

    Ok(())
}

/// `Nat.factorial_le`, `Nat.factorial_lt_of_lt`, and `Nat.factorial_ne_zero`.
///
/// Split out from [`declare_divisibility`] and called LATER in the build
/// order (after `declare_euclid`, mirroring `declare_dvd_antisymm`'s
/// precedent in `lcm.rs`): all three need `one_le_factorial`, which
/// `declare_euclid` (`primes.rs`) declares, and `declare_euclid` itself runs
/// after `declare_divisibility`.
pub(super) fn declare_factorial_order(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    // factorial_le : ∀ m n, Le m n → Le (factorial m) (factorial n), via
    // `factorial_dvd_factorial` and `le_of_dvd` against the positivity of
    // `factorial n` (`one_le_factorial`).
    d.theorem(p.factorial_le, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let mfact = d.factorial(m);
        let nfact = d.factorial(n);
        let stmt = {
            let hyp = d.le(m, n);
            let concl = d.le(mfact, nfact);
            d.arrow(hyp, concl)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp_ty = d.le(m, n);

        let divides = d.lemma(p.factorial_dvd_factorial, &[m, n, h]);
        let positive = d.lemma(p.one_le_factorial, &[n]);
        let le = d.lemma(p.le_of_dvd, &[mfact, nfact, positive, divides]);

        (stmt, d.lam_fv(h_fv, hyp_ty, le))
    })?;

    // factorial_lt_of_lt : ∀ m n, Lt zero n → Lt n m → Lt (factorial n) (factorial m)
    //
    // `n! < (succ n)! ≤ m!`. The strict step expands `(succ n)!` (defeq
    // `factorial n * succ n`, defeq `add (factorial n * n) (factorial n)` by
    // `mul`'s recursion on its right argument) and shows `factorial n * n ≥ 1`
    // (`one_le_mul` against `0 < n`), so adding `factorial n` on the left
    // strictly grows past `factorial n` (`add_lt_add_left`, then `add_comm` to
    // land on the `mul`-recursion shape). The non-strict step is `factorial_le`
    // at `succ n ≤ m`; `lt_of_lt_of_le` chains them.
    d.theorem(p.factorial_lt_of_lt, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let zero = d.zero();
        let nfact = d.factorial(n);
        let mfact = d.factorial(m);
        let hyp1_ty = d.lt(zero, n);
        let hyp2_ty = d.lt(n, m);
        let stmt = {
            let concl = d.lt(nfact, mfact);
            let inner = d.arrow(hyp2_ty, concl);
            d.arrow(hyp1_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let successor = d.succ(n);
        // (succ n)! ≤ m!
        let step_le = d.lemma(p.factorial_le, &[successor, m, h2]);

        // n! < (succ n)!
        let prod = d.mul(nfact, n);
        let positive_fact = d.lemma(p.one_le_factorial, &[n]);
        let mul_pos = d.lemma(p.one_le_mul, &[nfact, n, positive_fact, h1]);
        let strict_step = d.lemma(p.add_lt_add_left, &[nfact, zero, prod, mul_pos]);
        let add_n_prod = d.add(nfact, prod);
        let add_prod_n = d.add(prod, nfact);
        let commute = d.lemma(p.add_comm, &[nfact, prod]);
        let motive = d.eq_motive(add_n_prod, &|d, x| {
            let nfact = d.factorial(n);
            d.lt(nfact, x)
        });
        let step_lt = d.transport(add_n_prod, motive, strict_step, add_prod_n, commute);

        let succ_n_fact = d.factorial(successor);
        let chained = d.lemma(
            p.lt_of_lt_of_le,
            &[nfact, succ_n_fact, mfact, step_lt, step_le],
        );

        let inner = d.lam_fv(h2_fv, hyp2_ty, chained);
        let proof = d.lam_fv(h1_fv, hyp1_ty, inner);
        (stmt, proof)
    })?;

    // factorial_ne_zero : ∀ n, Not (Eq (factorial n) zero), via
    // `one_le_factorial` transported along a hypothetical `factorial n = zero`
    // into `Le 1 zero`, refuted by `not_succ_le_zero`.
    d.theorem(p.factorial_ne_zero, 1, &|d, values| {
        let n = values[0];
        let value = d.factorial(n);
        let zero = d.zero();
        let eqn = d.eq(value, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let stmt = d.arrow(eqn, false_ty);

        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let positive = d.lemma(p.one_le_factorial, &[n]);
        let motive = d.eq_motive(value, &|d, x| {
            let unit = d.num(1);
            d.le(unit, x)
        });
        let le_unit_zero = d.transport(value, motive, positive, zero, heq);
        let contradiction = d.lemma(p.not_succ_le_zero, &[zero, le_unit_zero]);

        let proof = d.lam_fv(heq_fv, eqn, contradiction);
        (stmt, proof)
    })?;

    Ok(())
}

// ============================================================================
// `Nat.div_dvd_div_left : ∀ n m k, dvd m k → dvd n m → dvd (k/m) (k/n)`.
// ============================================================================

/// See [`NatPrelude::div_dvd_div_left`] for the route. Case-split on `m`
/// (`d.induct`, ignoring the induction hypothesis -- this is a case split,
/// not a recursion) to isolate `m`'s positivity, which `div_mul_cancel_of_dvd`
/// needs:
///
/// - `m = 0`: `dvd 0 k` forces `k = 0` (`zero_mul` on the witness), so both
///   `k/0` and `k/n` reduce to `0` (`zero_div`) and `dvd_refl` closes it.
///   `dvd n 0` is unused.
/// - `m = succ pred`: `dvd (succ pred) k` gives `k = (succ pred)*p` for a
///   witness `p`, and `div_mul_cancel_of_dvd` gives
///   `(succ pred)*(k/succ pred) = k`. `dvd n (succ pred)` gives
///   `succ pred = n*q` for a witness `q`; substituting shows `n ∣ k` with
///   witness `q*p` (`mul_assoc`), so `n` is positive too
///   (`one_le_of_dvd_pos`, since `succ pred` is positive) and
///   `div_mul_cancel_of_dvd` again gives `n*(k/n) = k`. Cancelling `n` from
///   both expressions for `k` (`mul_left_cancel_of_pos`) gives
///   `k/n = q*(k/succ pred)`, i.e. (`mul_comm`) `k/n = (k/succ pred)*q` --
///   exactly the witness `div_dvd_div_left` needs.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_div_dvd_div_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_dvd_div_left, 3, &|d, values| {
        let (n, m, k) = (values[0], values[1], values[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let dvd_x_k = d.dvd(x, k);
            let dvd_n_x = d.dvd(n, x);
            let kdivx = d.div(k, x);
            let kdivn = d.div(k, n);
            let concl = d.dvd(kdivx, kdivn);
            let inner = d.arrow(dvd_n_x, concl);
            d.arrow(dvd_x_k, inner)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let dvd0k_ty = d.dvd(zero, k);
            let dvd0k_fv = d.fresh_fvar();
            let dvd0k = d.kernel().fvar(dvd0k_fv);
            let dvdn0_ty = d.dvd(n, zero);
            let dvdn0_fv = d.fresh_fvar();

            let k_eq_zero_ty = d.eq(k, zero);
            let k_eq_zero = dvd_elim(d, zero, k, k_eq_zero_ty, dvd0k, &|d, q, eq_k_0q| {
                let zero_q = d.mul(zero, q);
                let zero_mul_eq = d.lemma(p.zero_mul, &[q]); // Eq zero_q zero
                let (_, chained) = d.chain(k, &[(zero_q, eq_k_0q), (zero, zero_mul_eq)]);
                chained
            });
            let eq_zero_k = d.symm(k, zero, k_eq_zero);

            let div00 = d.div(zero, zero);
            let div0n = d.div(zero, n);
            let div00_eq_zero = d.lemma(p.zero_div, &[zero]); // Eq div00 zero
            let div0n_eq_zero = d.lemma(p.zero_div, &[n]); // Eq div0n zero
            let eq_zero_div00 = d.symm(div00, zero, div00_eq_zero);
            let eq_zero_div0n = d.symm(div0n, zero, div0n_eq_zero);
            let dvd_zero_zero = d.lemma(p.dvd_refl, &[zero]);
            let dvd_div00_zero =
                transport_dvd_left(d, zero, div00, eq_zero_div00, zero, dvd_zero_zero);
            let proof_at_zero =
                transport_dvd_right(d, div00, zero, div0n, eq_zero_div0n, dvd_div00_zero);

            let goal_motive = d.eq_motive(zero, &|d, x| {
                let divx0 = d.div(x, zero);
                let divxn = d.div(x, n);
                d.dvd(divx0, divxn)
            });
            let goal_proof = d.transport(zero, goal_motive, proof_at_zero, k, eq_zero_k);

            let inner = d.lam_fv(dvdn0_fv, dvdn0_ty, goal_proof);
            d.lam_fv(dvd0k_fv, dvd0k_ty, inner)
        };
        let step = |d: &mut NatDev<'_>, pred: ExprId, _ih: ExprId| -> ExprId {
            let succ_pred = d.succ(pred);
            let dvd_succpred_k_ty = d.dvd(succ_pred, k);
            let dvd_succpred_k_fv = d.fresh_fvar();
            let dvd_succpred_k = d.kernel().fvar(dvd_succpred_k_fv);
            let dvd_n_succpred_ty = d.dvd(n, succ_pred);
            let dvd_n_succpred_fv = d.fresh_fvar();
            let dvd_n_succpred = d.kernel().fvar(dvd_n_succpred_fv);

            let one_le_succ_pred = d.zero_lt_succ(pred); // defeq to `1 <= succ pred`
            let kdivm = d.div(k, succ_pred);
            let kdivm_eq = d.lemma(
                p.div_mul_cancel_of_dvd,
                &[succ_pred, k, one_le_succ_pred, dvd_succpred_k],
            ); // Eq (mul succ_pred kdivm) k
            let succpred_kdivm = d.mul(succ_pred, kdivm);
            let k_eq_succpred_kdivm = d.symm(succpred_kdivm, k, kdivm_eq);

            let one_le_n = d.lemma(
                p.one_le_of_dvd_pos,
                &[n, succ_pred, one_le_succ_pred, dvd_n_succpred],
            );

            let kdivn = d.div(k, n);
            let goal = d.dvd(kdivm, kdivn);
            let goal_proof = dvd_elim(
                d,
                n,
                succ_pred,
                goal,
                dvd_n_succpred,
                &|d, q, succpred_eq_nq| {
                    let nq = d.mul(n, q);
                    let step_congr =
                        d.congr(succ_pred, nq, succpred_eq_nq, &|d, x| d.mul(x, kdivm));
                    let assoc_eq = d.lemma(p.mul_assoc, &[n, q, kdivm]); // Eq (mul nq kdivm) (mul n (mul q kdivm))
                    let nq_kdivm = d.mul(nq, kdivm);
                    let qkdivm = d.mul(q, kdivm);
                    let n_qkdivm = d.mul(n, qkdivm);
                    let (_, eq_k_n_qkdivm) = d.chain(
                        k,
                        &[
                            (succpred_kdivm, k_eq_succpred_kdivm),
                            (nq_kdivm, step_congr),
                            (n_qkdivm, assoc_eq),
                        ],
                    );
                    let dvd_n_k = dvd_intro(d, n, k, qkdivm, eq_k_n_qkdivm);
                    let eq_cancel_n = d.lemma(p.div_mul_cancel_of_dvd, &[n, k, one_le_n, dvd_n_k]); // Eq (mul n kdivn) k
                    let n_kdivn = d.mul(n, kdivn);
                    let (_, combined_eq) =
                        d.chain(n_kdivn, &[(k, eq_cancel_n), (n_qkdivm, eq_k_n_qkdivm)]);
                    let kdivn_eq_qkdivm = d.lemma(
                        p.mul_left_cancel_of_pos,
                        &[n, kdivn, qkdivm, one_le_n, combined_eq],
                    ); // Eq kdivn qkdivm
                    let comm_eq = d.lemma(p.mul_comm, &[q, kdivm]); // Eq qkdivm (mul kdivm q)
                    let kdivm_q = d.mul(kdivm, q);
                    let (_, kdivn_eq_kdivm_q) =
                        d.chain(kdivn, &[(qkdivm, kdivn_eq_qkdivm), (kdivm_q, comm_eq)]);
                    dvd_intro(d, kdivm, kdivn, q, kdivn_eq_kdivm_q)
                },
            );

            let inner = d.lam_fv(dvd_n_succpred_fv, dvd_n_succpred_ty, goal_proof);
            d.lam_fv(dvd_succpred_k_fv, dvd_succpred_k_ty, inner)
        };
        let proof = d.induct(&motive, &base, &step, m);
        (motive(d, m), proof)
    })?;
    Ok(())
}
