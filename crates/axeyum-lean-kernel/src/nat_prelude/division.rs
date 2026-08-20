//! Euclidean division: the relational `Nat.divMod` specification and the proof
//! that the executable `Nat.div`/`Nat.mod` projections satisfy it.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

/// Relational Euclidean division with constructive existence for every
/// positive divisor. The quotient and remainder are proof witnesses rather
/// than trusted computations.
pub(super) fn declare_euclidean_division(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let level_one = d.level_one();

    // divMod d n q r := n = d*q+r ∧ r<d
    {
        let divisor_fv = d.fresh_fvar();
        let divisor = d.kernel().fvar(divisor_fv);
        let dividend_fv = d.fresh_fvar();
        let dividend = d.kernel().fvar(dividend_fv);
        let quotient_fv = d.fresh_fvar();
        let quotient = d.kernel().fvar(quotient_fv);
        let remainder_fv = d.fresh_fvar();
        let remainder = d.kernel().fvar(remainder_fv);
        let product = d.mul(divisor, quotient);
        let reconstructed = d.add(product, remainder);
        let equation = d.eq(dividend, reconstructed);
        let bound = d.lt(remainder, divisor);
        let body = d.const_app(p.logic.and, &[equation, bound]);
        let value = {
            let with_remainder = d.lam_fv(remainder_fv, nat, body);
            let with_quotient = d.lam_fv(quotient_fv, nat, with_remainder);
            let with_dividend = d.lam_fv(dividend_fv, nat, with_quotient);
            d.lam_fv(divisor_fv, nat, with_dividend)
        };
        let ty = {
            let with_remainder = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_quotient = d
                .kernel()
                .pi(anon, nat, with_remainder, BinderInfo::Default);
            let with_dividend = d.kernel().pi(anon, nat, with_quotient, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_dividend, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.div_mod,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    // div_mod_exists : ∀ d n, Le one d → ∃ q r, divMod d n q r
    d.theorem(p.div_mod_exists, 2, &|d, v| {
        let (divisor, dividend) = (v[0], v[1]);
        let zero = d.zero();
        let one = d.num(1);
        let positive_ty = d.le(one, divisor);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);

        let exists_at = |d: &mut NatDev<'_>, n: ExprId| {
            let quotient_fv = d.fresh_fvar();
            let quotient = d.kernel().fvar(quotient_fv);
            let remainder_fv = d.fresh_fvar();
            let remainder = d.kernel().fvar(remainder_fv);
            let relation = d.div_mod(divisor, n, quotient, remainder);
            let remainder_predicate = d.lam_fv(remainder_fv, nat, relation);
            let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let remainder_exists = d.apply(exists, &[nat, remainder_predicate]);
            let quotient_predicate = d.lam_fv(quotient_fv, nat, remainder_exists);
            d.apply(exists, &[nat, quotient_predicate])
        };
        let introduce = |d: &mut NatDev<'_>,
                         n: ExprId,
                         quotient: ExprId,
                         remainder: ExprId,
                         relation_proof: ExprId| {
            let remainder_fv = d.fresh_fvar();
            let remainder_var = d.kernel().fvar(remainder_fv);
            let relation = d.div_mod(divisor, n, quotient, remainder_var);
            let remainder_predicate = d.lam_fv(remainder_fv, nat, relation);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
            let remainder_exists = d.apply(
                intro,
                &[nat, remainder_predicate, remainder, relation_proof],
            );

            let quotient_fv = d.fresh_fvar();
            let quotient_var = d.kernel().fvar(quotient_fv);
            let inner_remainder_fv = d.fresh_fvar();
            let inner_remainder = d.kernel().fvar(inner_remainder_fv);
            let inner_relation = d.div_mod(divisor, n, quotient_var, inner_remainder);
            let inner_predicate = d.lam_fv(inner_remainder_fv, nat, inner_relation);
            let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let inner_exists = d.apply(exists, &[nat, inner_predicate]);
            let quotient_predicate = d.lam_fv(quotient_fv, nat, inner_exists);
            d.apply(
                intro,
                &[nat, quotient_predicate, quotient, remainder_exists],
            )
        };

        let motive = |d: &mut NatDev<'_>, n: ExprId| exists_at(d, n);
        let base = |d: &mut NatDev<'_>| {
            let product = d.mul(divisor, zero);
            let reconstructed = d.add(product, zero);
            let equation_ty = d.eq(zero, reconstructed);
            let bound_ty = d.lt(zero, divisor);
            let equation = d.refl(zero);
            let relation_proof = d.const_app(
                p.logic.and_intro,
                &[equation_ty, bound_ty, equation, positive],
            );
            introduce(d, zero, zero, zero, relation_proof)
        };
        let step = |d: &mut NatDev<'_>, n: ExprId, ih: ExprId| {
            let sn = d.succ(n);
            let target = exists_at(d, sn);
            let source = exists_at(d, n);
            let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);

            let outer_minor = {
                let quotient_fv = d.fresh_fvar();
                let quotient = d.kernel().fvar(quotient_fv);
                let remainder_fv = d.fresh_fvar();
                let remainder = d.kernel().fvar(remainder_fv);
                let source_relation = d.div_mod(divisor, n, quotient, remainder);
                let remainder_predicate = d.lam_fv(remainder_fv, nat, source_relation);
                let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
                let remainder_exists_ty = d.apply(exists, &[nat, remainder_predicate]);
                let remainder_exists_fv = d.fresh_fvar();
                let remainder_exists = d.kernel().fvar(remainder_exists_fv);

                let inner_motive =
                    d.kernel()
                        .lam(anon, remainder_exists_ty, target, BinderInfo::Default);
                let inner_minor = {
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let relation_ty = d.div_mod(divisor, n, quotient, r);
                    let relation_fv = d.fresh_fvar();
                    let relation = d.kernel().fvar(relation_fv);
                    let product = d.mul(divisor, quotient);
                    let reconstructed = d.add(product, r);
                    let equation_ty = d.eq(n, reconstructed);
                    let bound_ty = d.lt(r, divisor);
                    let relation_motive =
                        d.kernel()
                            .lam(anon, relation_ty, target, BinderInfo::Default);
                    let relation_minor = {
                        let equation_fv = d.fresh_fvar();
                        let equation = d.kernel().fvar(equation_fv);
                        let bound_fv = d.fresh_fvar();
                        let bound = d.kernel().fvar(bound_fv);
                        let sr = d.succ(r);
                        let strict_ty = d.lt(sr, divisor);
                        let equal_ty = d.eq(sr, divisor);
                        let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                        let split = d.lemma(p.lt_or_eq_of_le, &[sr, divisor, bound]);
                        let split_motive =
                            d.kernel().lam(anon, split_ty, target, BinderInfo::Default);

                        let strict_minor = {
                            let strict_fv = d.fresh_fvar();
                            let strict = d.kernel().fvar(strict_fv);
                            let next_reconstructed = d.add(product, sr);
                            let next_equation_ty = d.eq(sn, next_reconstructed);
                            let next_equation =
                                d.congr(n, reconstructed, equation, &|d, x| d.succ(x));
                            let next_relation = d.const_app(
                                p.logic.and_intro,
                                &[next_equation_ty, strict_ty, next_equation, strict],
                            );
                            let body = introduce(d, sn, quotient, sr, next_relation);
                            d.lam_fv(strict_fv, strict_ty, body)
                        };
                        let equal_minor = {
                            let equal_fv = d.fresh_fvar();
                            let equal = d.kernel().fvar(equal_fv);
                            let sq = d.succ(quotient);
                            let next_product = d.mul(divisor, sq);
                            let next_reconstructed = d.add(next_product, zero);
                            let next_equation_ty = d.eq(sn, next_reconstructed);
                            let successor_reconstructed = d.succ(reconstructed);
                            let lifted = d.congr(n, reconstructed, equation, &|d, x| d.succ(x));
                            let product_plus_sr = d.add(product, sr);
                            let successor_eq_product_plus_sr = d.refl(successor_reconstructed);
                            let product_plus_divisor = d.add(product, divisor);
                            let replace_remainder =
                                d.congr(sr, divisor, equal, &|d, x| d.add(product, x));
                            let product_plus_divisor_eq_next = d.refl(product_plus_divisor);
                            let (_, next_equation) = d.chain(
                                sn,
                                &[
                                    (successor_reconstructed, lifted),
                                    (product_plus_sr, successor_eq_product_plus_sr),
                                    (product_plus_divisor, replace_remainder),
                                    (next_reconstructed, product_plus_divisor_eq_next),
                                ],
                            );
                            let zero_bound_ty = d.lt(zero, divisor);
                            let next_relation = d.const_app(
                                p.logic.and_intro,
                                &[next_equation_ty, zero_bound_ty, next_equation, positive],
                            );
                            let body = introduce(d, sn, sq, zero, next_relation);
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
                    let with_relation = d.lam_fv(relation_fv, relation_ty, body);
                    d.lam_fv(r_fv, nat, with_relation)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
                let inner = d.apply(
                    exists_rec,
                    &[
                        nat,
                        remainder_predicate,
                        inner_motive,
                        inner_minor,
                        remainder_exists,
                    ],
                );
                let with_remainder_exists =
                    d.lam_fv(remainder_exists_fv, remainder_exists_ty, inner);
                d.lam_fv(quotient_fv, nat, with_remainder_exists)
            };
            let quotient_fv = d.fresh_fvar();
            let quotient = d.kernel().fvar(quotient_fv);
            let remainder_fv = d.fresh_fvar();
            let remainder = d.kernel().fvar(remainder_fv);
            let relation = d.div_mod(divisor, n, quotient, remainder);
            let remainder_predicate = d.lam_fv(remainder_fv, nat, relation);
            let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let remainder_exists = d.apply(exists, &[nat, remainder_predicate]);
            let quotient_predicate = d.lam_fv(quotient_fv, nat, remainder_exists);
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
            d.apply(
                exists_rec,
                &[nat, quotient_predicate, outer_motive, outer_minor, ih],
            )
        };
        let body = d.induct(&motive, &base, &step, dividend);
        let conclusion = exists_at(d, dividend);
        let stmt = d.arrow(positive_ty, conclusion);
        let proof = d.lam_fv(positive_fv, positive_ty, body);
        (stmt, proof)
    })?;

    // div_mod_unique :
    //   ∀ d n q₁ r₁ q₂ r₂,
    //     divMod d n q₁ r₁ → divMod d n q₂ r₂ → q₁ = q₂ ∧ r₁ = r₂
    // Compare the quotients by totality. A strict gap places one reconstructed
    // dividend strictly below the other because its remainder is below the
    // divisor, contradicting their common value. Equal quotients leave equal
    // remainders by cancellation of the common product.
    d.theorem(p.div_mod_unique, 6, &|d, v| {
        let (divisor, dividend, q1, r1, q2, r2) = (v[0], v[1], v[2], v[3], v[4], v[5]);
        let relation1_ty = d.div_mod(divisor, dividend, q1, r1);
        let relation2_ty = d.div_mod(divisor, dividend, q2, r2);
        let quotient_eq_ty = d.eq(q1, q2);
        let remainder_eq_ty = d.eq(r1, r2);
        let target = d.const_app(p.logic.and, &[quotient_eq_ty, remainder_eq_ty]);

        let relation1_fv = d.fresh_fvar();
        let relation1 = d.kernel().fvar(relation1_fv);
        let relation2_fv = d.fresh_fvar();
        let relation2 = d.kernel().fvar(relation2_fv);

        let product1 = d.mul(divisor, q1);
        let product2 = d.mul(divisor, q2);
        let sum1 = d.add(product1, r1);
        let sum2 = d.add(product2, r2);
        let equation1_ty = d.eq(dividend, sum1);
        let equation2_ty = d.eq(dividend, sum2);
        let bound1_ty = d.lt(r1, divisor);
        let bound2_ty = d.lt(r2, divisor);

        let relation2_to_target = d.arrow(relation2_ty, target);
        let relation1_motive =
            d.kernel()
                .lam(anon, relation1_ty, relation2_to_target, BinderInfo::Default);
        let relation1_minor = {
            let equation1_fv = d.fresh_fvar();
            let equation1 = d.kernel().fvar(equation1_fv);
            let bound1_fv = d.fresh_fvar();
            let bound1 = d.kernel().fvar(bound1_fv);

            let relation2_motive = d
                .kernel()
                .lam(anon, relation2_ty, target, BinderInfo::Default);
            let relation2_minor = {
                let equation2_fv = d.fresh_fvar();
                let equation2 = d.kernel().fvar(equation2_fv);
                let bound2_fv = d.fresh_fvar();
                let bound2 = d.kernel().fvar(bound2_fv);

                let equation1_rev = d.symm(dividend, sum1, equation1);
                let (_, sums_equal) =
                    d.chain(sum1, &[(dividend, equation1_rev), (sum2, equation2)]);
                let order12_ty = d.le(q1, q2);
                let order21_ty = d.le(q2, q1);
                let order_split_ty = d.const_app(p.logic.or, &[order12_ty, order21_ty]);
                let order_split = d.lemma(p.le_total, &[q1, q2]);
                let order_motive =
                    d.kernel()
                        .lam(anon, order_split_ty, quotient_eq_ty, BinderInfo::Default);

                let q1_le_q2_minor = {
                    let order_fv = d.fresh_fvar();
                    let order = d.kernel().fvar(order_fv);
                    let strict_ty = d.lt(q1, q2);
                    let equal_ty = d.eq(q1, q2);
                    let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[q1, q2, order]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_eq_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let product1_plus_divisor = d.add(product1, divisor);
                        let sum1_lt_next =
                            d.lemma(p.add_lt_add_left, &[product1, r1, divisor, bound1]);
                        let sq1 = d.succ(q1);
                        let next_le_product2 =
                            d.lemma(p.mul_le_mul_left, &[divisor, sq1, q2, strict]);
                        let sum1_lt_product2 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                sum1,
                                product1_plus_divisor,
                                product2,
                                sum1_lt_next,
                                next_le_product2,
                            ],
                        );
                        let product2_le_sum2 = d.lemma(p.le_add_right, &[product2, r2]);
                        let sum1_lt_sum2 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[sum1, product2, sum2, sum1_lt_product2, product2_le_sum2],
                        );
                        let sums_equal_rev = d.symm(sum1, sum2, sums_equal);
                        let loop_motive = d.eq_motive(sum2, &|d, x| d.lt(sum1, x));
                        let impossible_strict =
                            d.transport(sum2, loop_motive, sum1_lt_sum2, sum1, sums_equal_rev);
                        let no_loop = d.lemma(p.lt_irrefl, &[sum1]);
                        let impossible = d.apply(no_loop, &[impossible_strict]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let false_motive =
                            d.kernel()
                                .lam(anon, false_ty, quotient_eq_ty, BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let body = d.apply(false_rec, &[false_motive, impossible]);
                        d.lam_fv(strict_fv, strict_ty, body)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        d.lam_fv(equal_fv, equal_ty, equal)
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
                    d.lam_fv(order_fv, order12_ty, body)
                };

                let q2_le_q1_minor = {
                    let order_fv = d.fresh_fvar();
                    let order = d.kernel().fvar(order_fv);
                    let strict_ty = d.lt(q2, q1);
                    let equal_ty = d.eq(q2, q1);
                    let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[q2, q1, order]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_eq_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let product2_plus_divisor = d.add(product2, divisor);
                        let sum2_lt_next =
                            d.lemma(p.add_lt_add_left, &[product2, r2, divisor, bound2]);
                        let sq2 = d.succ(q2);
                        let next_le_product1 =
                            d.lemma(p.mul_le_mul_left, &[divisor, sq2, q1, strict]);
                        let sum2_lt_product1 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                sum2,
                                product2_plus_divisor,
                                product1,
                                sum2_lt_next,
                                next_le_product1,
                            ],
                        );
                        let product1_le_sum1 = d.lemma(p.le_add_right, &[product1, r1]);
                        let sum2_lt_sum1 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[sum2, product1, sum1, sum2_lt_product1, product1_le_sum1],
                        );
                        let loop_motive = d.eq_motive(sum1, &|d, x| d.lt(sum2, x));
                        let impossible_strict =
                            d.transport(sum1, loop_motive, sum2_lt_sum1, sum2, sums_equal);
                        let no_loop = d.lemma(p.lt_irrefl, &[sum2]);
                        let impossible = d.apply(no_loop, &[impossible_strict]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let false_motive =
                            d.kernel()
                                .lam(anon, false_ty, quotient_eq_ty, BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let body = d.apply(false_rec, &[false_motive, impossible]);
                        d.lam_fv(strict_fv, strict_ty, body)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let body = d.symm(q2, q1, equal);
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
                    d.lam_fv(order_fv, order21_ty, body)
                };

                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let quotient_eq = d.apply(
                    or_rec,
                    &[
                        order12_ty,
                        order21_ty,
                        order_motive,
                        q1_le_q2_minor,
                        q2_le_q1_minor,
                        order_split,
                    ],
                );
                let products_equal = d.congr(q1, q2, quotient_eq, &|d, q| d.mul(divisor, q));
                let product1_sum2 = d.add(product1, r2);
                let replace_product =
                    d.congr(product1, product2, products_equal, &|d, x| d.add(x, r2));
                let replace_product_rev = d.symm(product1_sum2, sum2, replace_product);
                let (_, common_sums) = d.chain(
                    sum1,
                    &[(sum2, sums_equal), (product1_sum2, replace_product_rev)],
                );
                let remainder_eq = d.lemma(p.add_left_cancel, &[product1, r1, r2, common_sums]);
                let body = d.const_app(
                    p.logic.and_intro,
                    &[quotient_eq_ty, remainder_eq_ty, quotient_eq, remainder_eq],
                );
                let with_bound2 = d.lam_fv(bound2_fv, bound2_ty, body);
                d.lam_fv(equation2_fv, equation2_ty, with_bound2)
            };
            let level_zero = d.kernel().level_zero();
            let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
            let body = d.apply(
                and_rec,
                &[
                    equation2_ty,
                    bound2_ty,
                    relation2_motive,
                    relation2_minor,
                    relation2,
                ],
            );
            let with_relation2 = d.lam_fv(relation2_fv, relation2_ty, body);
            let with_bound1 = d.lam_fv(bound1_fv, bound1_ty, with_relation2);
            d.lam_fv(equation1_fv, equation1_ty, with_bound1)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                equation1_ty,
                bound1_ty,
                relation1_motive,
                relation1_minor,
                relation1,
            ],
        );
        let relation2_to_target = d.arrow(relation2_ty, target);
        let stmt = d.arrow(relation1_ty, relation2_to_target);
        let proof = d.lam_fv(relation1_fv, relation1_ty, body);
        (stmt, proof)
    })?;

    // div_mod_bounds :
    //   ∀ d n q r, divMod d n q r → d*q ≤ n ∧ n < d*(succ q)
    // The relation equation supplies the lower bound by inclusion of the
    // remainder. Its strict remainder bound supplies the upper endpoint,
    // since `d*q+d` reduces to `d*(succ q)`.
    d.theorem(p.div_mod_bounds, 4, &|d, v| {
        let (divisor, dividend, quotient, remainder) = (v[0], v[1], v[2], v[3]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let product = d.mul(divisor, quotient);
        let reconstructed = d.add(product, remainder);
        let next_quotient = d.succ(quotient);
        let next_product = d.mul(divisor, next_quotient);
        let lower_ty = d.le(product, dividend);
        let upper_ty = d.lt(dividend, next_product);
        let target = d.const_app(p.logic.and, &[lower_ty, upper_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, target, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);
            let reconstructed_eq_dividend = d.symm(dividend, reconstructed, equation);

            let product_le_reconstructed = d.lemma(p.le_add_right, &[product, remainder]);
            let lower_motive = d.eq_motive(reconstructed, &|d, upper| d.le(product, upper));
            let lower = d.transport(
                reconstructed,
                lower_motive,
                product_le_reconstructed,
                dividend,
                reconstructed_eq_dividend,
            );

            let reconstructed_lt_next =
                d.lemma(p.add_lt_add_left, &[product, remainder, divisor, bound]);
            let upper_motive = d.eq_motive(reconstructed, &|d, lower| d.lt(lower, next_product));
            let upper = d.transport(
                reconstructed,
                upper_motive,
                reconstructed_lt_next,
                dividend,
                reconstructed_eq_dividend,
            );
            let body = d.const_app(p.logic.and_intro, &[lower_ty, upper_ty, lower, upper]);
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

    // div_mod_mul_le_iff :
    //   ∀ d n q r s, divMod d n q r → (d*s ≤ n ↔ s ≤ q)
    // The reverse direction is multiplication monotonicity followed by the
    // lower floor bound. For the forward direction, q<s would put n strictly
    // below d*(succ q)≤d*s≤n, contradicting irreflexivity.
    d.theorem(p.div_mod_mul_le_iff, 5, &|d, v| {
        let (divisor, dividend, quotient, remainder, candidate) = (v[0], v[1], v[2], v[3], v[4]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let candidate_product = d.mul(divisor, candidate);
        let quotient_product = d.mul(divisor, quotient);
        let product_bound_ty = d.le(candidate_product, dividend);
        let quotient_bound_ty = d.le(candidate, quotient);
        let target = d.const_app(p.logic.iff, &[product_bound_ty, quotient_bound_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let bounds = d.lemma(
            p.div_mod_bounds,
            &[divisor, dividend, quotient, remainder, relation],
        );
        let next_quotient = d.succ(quotient);
        let next_product = d.mul(divisor, next_quotient);
        let lower_ty = d.le(quotient_product, dividend);
        let upper_ty = d.lt(dividend, next_product);
        let bounds_ty = d.const_app(p.logic.and, &[lower_ty, upper_ty]);
        let bounds_motive = d.kernel().lam(anon, bounds_ty, target, BinderInfo::Default);
        let bounds_minor = {
            let lower_fv = d.fresh_fvar();
            let lower = d.kernel().fvar(lower_fv);
            let upper_fv = d.fresh_fvar();
            let upper = d.kernel().fvar(upper_fv);

            let forward = {
                let product_bound_fv = d.fresh_fvar();
                let product_bound = d.kernel().fvar(product_bound_fv);
                let reverse_order_ty = d.le(quotient, candidate);
                let order_split_ty =
                    d.const_app(p.logic.or, &[quotient_bound_ty, reverse_order_ty]);
                let order_split = d.lemma(p.le_total, &[candidate, quotient]);
                let order_motive =
                    d.kernel()
                        .lam(anon, order_split_ty, quotient_bound_ty, BinderInfo::Default);
                let ordered_minor = {
                    let ordered_fv = d.fresh_fvar();
                    let ordered = d.kernel().fvar(ordered_fv);
                    d.lam_fv(ordered_fv, quotient_bound_ty, ordered)
                };
                let reverse_minor = {
                    let reverse_fv = d.fresh_fvar();
                    let reverse = d.kernel().fvar(reverse_fv);
                    let strict_ty = d.lt(quotient, candidate);
                    let equal_ty = d.eq(quotient, candidate);
                    let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[quotient, candidate, reverse]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_bound_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let next_le_candidate = d.lemma(
                            p.mul_le_mul_left,
                            &[divisor, next_quotient, candidate, strict],
                        );
                        let dividend_lt_candidate_product = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                dividend,
                                next_product,
                                candidate_product,
                                upper,
                                next_le_candidate,
                            ],
                        );
                        let impossible_loop = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                dividend,
                                candidate_product,
                                dividend,
                                dividend_lt_candidate_product,
                                product_bound,
                            ],
                        );
                        let no_loop = d.lemma(p.lt_irrefl, &[dividend]);
                        let impossible = d.apply(no_loop, &[impossible_loop]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let false_motive =
                            d.kernel()
                                .lam(anon, false_ty, quotient_bound_ty, BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let body = d.apply(false_rec, &[false_motive, impossible]);
                        d.lam_fv(strict_fv, strict_ty, body)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let candidate_eq_quotient = d.symm(quotient, candidate, equal);
                        let candidate_refl = d.lemma(p.le_refl, &[candidate]);
                        let equality_motive =
                            d.eq_motive(candidate, &|d, upper| d.le(candidate, upper));
                        let body = d.transport(
                            candidate,
                            equality_motive,
                            candidate_refl,
                            quotient,
                            candidate_eq_quotient,
                        );
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
                    d.lam_fv(reverse_fv, reverse_order_ty, body)
                };
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let body = d.apply(
                    or_rec,
                    &[
                        quotient_bound_ty,
                        reverse_order_ty,
                        order_motive,
                        ordered_minor,
                        reverse_minor,
                        order_split,
                    ],
                );
                d.lam_fv(product_bound_fv, product_bound_ty, body)
            };

            let reverse = {
                let quotient_bound_fv = d.fresh_fvar();
                let quotient_bound = d.kernel().fvar(quotient_bound_fv);
                let products_ordered = d.lemma(
                    p.mul_le_mul_left,
                    &[divisor, candidate, quotient, quotient_bound],
                );
                let body = d.lemma(
                    p.le_trans,
                    &[
                        candidate_product,
                        quotient_product,
                        dividend,
                        products_ordered,
                        lower,
                    ],
                );
                d.lam_fv(quotient_bound_fv, quotient_bound_ty, body)
            };

            let body = d.const_app(
                p.logic.iff_intro,
                &[product_bound_ty, quotient_bound_ty, forward, reverse],
            );
            let with_upper = d.lam_fv(upper_fv, upper_ty, body);
            d.lam_fv(lower_fv, lower_ty, with_upper)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[lower_ty, upper_ty, bounds_motive, bounds_minor, bounds],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_lt_mul_iff :
    //   ∀ d n q r s, divMod d n q r → (n < d*s ↔ q < s)
    // This is the strict dual of the floor adjunction. A candidate at or below
    // q has product at or below n; a candidate above q is at least succ q, so
    // the strict floor upper bound places n below its product.
    d.theorem(p.div_mod_lt_mul_iff, 5, &|d, v| {
        let (divisor, dividend, quotient, remainder, candidate) = (v[0], v[1], v[2], v[3], v[4]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let quotient_product = d.mul(divisor, quotient);
        let candidate_product = d.mul(divisor, candidate);
        let product_bound_ty = d.lt(dividend, candidate_product);
        let quotient_bound_ty = d.lt(quotient, candidate);
        let target = d.const_app(p.logic.iff, &[product_bound_ty, quotient_bound_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let bounds = d.lemma(
            p.div_mod_bounds,
            &[divisor, dividend, quotient, remainder, relation],
        );
        let next_quotient = d.succ(quotient);
        let next_product = d.mul(divisor, next_quotient);
        let lower_ty = d.le(quotient_product, dividend);
        let upper_ty = d.lt(dividend, next_product);
        let bounds_ty = d.const_app(p.logic.and, &[lower_ty, upper_ty]);
        let bounds_motive = d.kernel().lam(anon, bounds_ty, target, BinderInfo::Default);
        let bounds_minor = {
            let lower_fv = d.fresh_fvar();
            let lower = d.kernel().fvar(lower_fv);
            let upper_fv = d.fresh_fvar();
            let upper = d.kernel().fvar(upper_fv);

            let forward = {
                let product_bound_fv = d.fresh_fvar();
                let product_bound = d.kernel().fvar(product_bound_fv);
                let candidate_le_quotient_ty = d.le(candidate, quotient);
                let quotient_le_candidate_ty = d.le(quotient, candidate);
                let order_split_ty = d.const_app(
                    p.logic.or,
                    &[candidate_le_quotient_ty, quotient_le_candidate_ty],
                );
                let order_split = d.lemma(p.le_total, &[candidate, quotient]);
                let order_motive =
                    d.kernel()
                        .lam(anon, order_split_ty, quotient_bound_ty, BinderInfo::Default);
                let eliminate_candidate_le = |d: &mut NatDev<'_>, candidate_le_quotient: ExprId| {
                    let products_ordered = d.lemma(
                        p.mul_le_mul_left,
                        &[divisor, candidate, quotient, candidate_le_quotient],
                    );
                    let candidate_product_le_dividend = d.lemma(
                        p.le_trans,
                        &[
                            candidate_product,
                            quotient_product,
                            dividend,
                            products_ordered,
                            lower,
                        ],
                    );
                    let impossible_loop = d.lemma(
                        p.lt_of_lt_of_le,
                        &[
                            dividend,
                            candidate_product,
                            dividend,
                            product_bound,
                            candidate_product_le_dividend,
                        ],
                    );
                    let no_loop = d.lemma(p.lt_irrefl, &[dividend]);
                    let impossible = d.apply(no_loop, &[impossible_loop]);
                    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                    let false_motive =
                        d.kernel()
                            .lam(anon, false_ty, quotient_bound_ty, BinderInfo::Default);
                    let level_zero = d.kernel().level_zero();
                    let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                    d.apply(false_rec, &[false_motive, impossible])
                };
                let candidate_le_minor = {
                    let ordered_fv = d.fresh_fvar();
                    let ordered = d.kernel().fvar(ordered_fv);
                    let body = eliminate_candidate_le(d, ordered);
                    d.lam_fv(ordered_fv, candidate_le_quotient_ty, body)
                };
                let quotient_le_minor = {
                    let ordered_fv = d.fresh_fvar();
                    let ordered = d.kernel().fvar(ordered_fv);
                    let equal_ty = d.eq(quotient, candidate);
                    let split_ty = d.const_app(p.logic.or, &[quotient_bound_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[quotient, candidate, ordered]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_bound_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        d.lam_fv(strict_fv, quotient_bound_ty, strict)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let candidate_eq_quotient = d.symm(quotient, candidate, equal);
                        let candidate_refl = d.lemma(p.le_refl, &[candidate]);
                        let equality_motive =
                            d.eq_motive(candidate, &|d, upper| d.le(candidate, upper));
                        let candidate_le_quotient = d.transport(
                            candidate,
                            equality_motive,
                            candidate_refl,
                            quotient,
                            candidate_eq_quotient,
                        );
                        let body = eliminate_candidate_le(d, candidate_le_quotient);
                        d.lam_fv(equal_fv, equal_ty, body)
                    };
                    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                    let body = d.apply(
                        or_rec,
                        &[
                            quotient_bound_ty,
                            equal_ty,
                            split_motive,
                            strict_minor,
                            equal_minor,
                            split,
                        ],
                    );
                    d.lam_fv(ordered_fv, quotient_le_candidate_ty, body)
                };
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let body = d.apply(
                    or_rec,
                    &[
                        candidate_le_quotient_ty,
                        quotient_le_candidate_ty,
                        order_motive,
                        candidate_le_minor,
                        quotient_le_minor,
                        order_split,
                    ],
                );
                d.lam_fv(product_bound_fv, product_bound_ty, body)
            };

            let reverse = {
                let quotient_bound_fv = d.fresh_fvar();
                let quotient_bound = d.kernel().fvar(quotient_bound_fv);
                let next_le_candidate = d.lemma(
                    p.mul_le_mul_left,
                    &[divisor, next_quotient, candidate, quotient_bound],
                );
                let body = d.lemma(
                    p.lt_of_lt_of_le,
                    &[
                        dividend,
                        next_product,
                        candidate_product,
                        upper,
                        next_le_candidate,
                    ],
                );
                d.lam_fv(quotient_bound_fv, quotient_bound_ty, body)
            };

            let body = d.const_app(
                p.logic.iff_intro,
                &[product_bound_ty, quotient_bound_ty, forward, reverse],
            );
            let with_upper = d.lam_fv(upper_fv, upper_ty, body);
            d.lam_fv(lower_fv, lower_ty, with_upper)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[lower_ty, upper_ty, bounds_motive, bounds_minor, bounds],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_add_multiple :
    //   ∀ d n q r k, divMod d n q r → divMod d (n+d*k) (q+k) r
    // Shift a relational decomposition by a multiple of its divisor. This is
    // the reusable closure fact needed to compare balanced congruence witnesses
    // through div_mod_unique.
    d.theorem(p.div_mod_add_multiple, 5, &|d, v| {
        let (divisor, dividend, quotient, remainder, shift) = (v[0], v[1], v[2], v[3], v[4]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let shift_product = d.mul(divisor, shift);
        let shifted_dividend = d.add(dividend, shift_product);
        let shifted_quotient = d.add(quotient, shift);
        let target = d.div_mod(divisor, shifted_dividend, shifted_quotient, remainder);
        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);

        let quotient_product = d.mul(divisor, quotient);
        let reconstructed = d.add(quotient_product, remainder);
        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, target, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);

            let expanded = d.add(reconstructed, shift_product);
            let products_sum = d.add(quotient_product, shift_product);
            let regrouped = d.add(products_sum, remainder);
            let shifted_quotient_product = d.mul(divisor, shifted_quotient);
            let shifted_reconstructed = d.add(shifted_quotient_product, remainder);
            let expand = d.congr(dividend, reconstructed, equation, &|d, value| {
                d.add(value, shift_product)
            });
            let regroup = d.lemma(
                p.add_right_comm,
                &[quotient_product, remainder, shift_product],
            );
            let distribute = d.lemma(p.left_distrib, &[divisor, quotient, shift]);
            let factor = d.symm(shifted_quotient_product, products_sum, distribute);
            let factor_under_remainder = d.congr(
                products_sum,
                shifted_quotient_product,
                factor,
                &|d, value| d.add(value, remainder),
            );
            let (_, shifted_equation) = d.chain(
                shifted_dividend,
                &[
                    (expanded, expand),
                    (regrouped, regroup),
                    (shifted_reconstructed, factor_under_remainder),
                ],
            );
            let shifted_equation_ty = d.eq(shifted_dividend, shifted_reconstructed);
            let body = d.const_app(
                p.logic.and_intro,
                &[shifted_equation_ty, bound_ty, shifted_equation, bound],
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
    Ok(())
}

/// Prove that the executable projections satisfy the relational Euclidean
/// specification for every positive divisor, represented constructively as a
/// successor. The proof follows the same Boolean rollover transition as the
/// shared computational state.
pub(super) fn declare_executable_division_spec(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_mod_exec, 2, &|d, values| {
        let (divisor_predecessor, dividend) = (values[0], values[1]);
        let divisor = d.succ(divisor_predecessor);
        let spec = |d: &mut NatDev<'_>, value: ExprId| {
            let quotient = d.div(value, divisor);
            let remainder = d.modulo(value, divisor);
            d.div_mod(divisor, value, quotient, remainder)
        };

        let proof = d.induct(
            &spec,
            &|d| {
                let zero = d.zero();
                let quotient = d.div(zero, divisor);
                let remainder = d.modulo(zero, divisor);
                let product = d.mul(divisor, quotient);
                let reconstructed = d.add(product, remainder);
                let equation_ty = d.eq(zero, reconstructed);
                let equation = d.refl(zero);
                let bound_ty = d.lt(remainder, divisor);
                let zero_le_predecessor = d.lemma(p.zero_le, &[divisor_predecessor]);
                let bound = d.lemma(
                    p.le_succ_succ,
                    &[zero, divisor_predecessor, zero_le_predecessor],
                );
                d.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound])
            },
            &|d, prior_dividend, prior_relation| {
                executable_division_spec_step(
                    d,
                    &p,
                    anon,
                    divisor_predecessor,
                    divisor,
                    prior_dividend,
                    prior_relation,
                )
            },
            dividend,
        );
        (spec(d, dividend), proof)
    })?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn executable_division_spec_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
    divisor_predecessor: ExprId,
    divisor: ExprId,
    prior_dividend: ExprId,
    prior_relation: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let zero = d.zero();
    let successor_dividend = d.succ(prior_dividend);
    let quotient = d.div(prior_dividend, divisor);
    let remainder = d.modulo(prior_dividend, divisor);
    let successor_quotient = d.succ(quotient);
    let successor_remainder = d.succ(remainder);
    let condition = d.beq(remainder, divisor_predecessor);

    let target_for = |d: &mut NatDev<'_>, selector: ExprId| {
        let next_quotient = d.bool_select_nat(selector, successor_quotient, quotient);
        let next_remainder = d.bool_select_nat(selector, zero, successor_remainder);
        d.div_mod(divisor, successor_dividend, next_quotient, next_remainder)
    };
    let branch_for = |d: &mut NatDev<'_>, selector: ExprId| {
        let equality = d.bool_eq(condition, selector);
        let target = target_for(d, selector);
        d.arrow(equality, target)
    };

    let false_value = d.bool_false();
    let true_value = d.bool_true();
    let false_minor = executable_division_spec_no_rollover(
        d,
        p,
        anon,
        divisor_predecessor,
        divisor,
        prior_dividend,
        prior_relation,
        quotient,
        remainder,
        condition,
        false_value,
    );
    let true_minor = executable_division_spec_rollover(
        d,
        p,
        anon,
        divisor_predecessor,
        divisor,
        prior_dividend,
        prior_relation,
        quotient,
        remainder,
        condition,
        true_value,
    );
    let motive = {
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let body = branch_for(d, selector);
        d.lam_fv(selector_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, condition]);
    let condition_refl = d.bool_refl(condition);
    d.apply(selected, &[condition_refl])
}

#[allow(clippy::too_many_arguments)]
fn executable_division_spec_no_rollover(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
    divisor_predecessor: ExprId,
    divisor: ExprId,
    prior_dividend: ExprId,
    prior_relation: ExprId,
    quotient: ExprId,
    remainder: ExprId,
    condition: ExprId,
    false_value: ExprId,
) -> ExprId {
    let false_equality_ty = d.bool_eq(condition, false_value);
    let false_equality_fv = d.fresh_fvar();
    let false_equality = d.kernel().fvar(false_equality_fv);
    let successor_dividend = d.succ(prior_dividend);
    let successor_remainder = d.succ(remainder);
    let target = d.div_mod(divisor, successor_dividend, quotient, successor_remainder);
    let relation_ty = d.div_mod(divisor, prior_dividend, quotient, remainder);
    let product = d.mul(divisor, quotient);
    let reconstructed = d.add(product, remainder);
    let equation_ty = d.eq(prior_dividend, reconstructed);
    let bound_ty = d.lt(remainder, divisor);
    let relation_motive = d
        .kernel()
        .lam(anon, relation_ty, target, BinderInfo::Default);
    let relation_minor = {
        let equation_fv = d.fresh_fvar();
        let equation = d.kernel().fvar(equation_fv);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let remainder_le_predecessor = d.lemma(
            p.le_of_succ_le_succ,
            &[remainder, divisor_predecessor, bound],
        );
        let strict_ty = d.lt(remainder, divisor_predecessor);
        let equal_ty = d.eq(remainder, divisor_predecessor);
        let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
        let split = d.lemma(
            p.lt_or_eq_of_le,
            &[remainder, divisor_predecessor, remainder_le_predecessor],
        );
        let split_motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);
        let strict_minor = {
            let strict_fv = d.fresh_fvar();
            let strict = d.kernel().fvar(strict_fv);
            let next_reconstructed = d.add(product, successor_remainder);
            let next_equation_ty = d.eq(successor_dividend, next_reconstructed);
            let next_equation = d.congr(prior_dividend, reconstructed, equation, &|d, value| {
                d.succ(value)
            });
            let next_bound_ty = d.lt(successor_remainder, divisor);
            let next_bound = d.lemma(
                p.le_succ_succ,
                &[successor_remainder, divisor_predecessor, strict],
            );
            let body = d.const_app(
                p.logic.and_intro,
                &[next_equation_ty, next_bound_ty, next_equation, next_bound],
            );
            d.lam_fv(strict_fv, strict_ty, body)
        };
        let equal_minor = {
            let equal_fv = d.fresh_fvar();
            let equal = d.kernel().fvar(equal_fv);
            let true_value = d.bool_true();
            let true_equality = d.lemma(
                p.beq_eq_true_of_eq,
                &[remainder, divisor_predecessor, equal],
            );
            let reverse_false = d.bool_symm(condition, false_value, false_equality);
            let impossible = d.bool_trans(
                false_value,
                condition,
                true_value,
                reverse_false,
                true_equality,
            );
            let body = d.false_true_elim(target, impossible);
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
            prior_relation,
        ],
    );
    d.lam_fv(false_equality_fv, false_equality_ty, body)
}

#[allow(clippy::too_many_arguments)]
fn executable_division_spec_rollover(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
    divisor_predecessor: ExprId,
    divisor: ExprId,
    prior_dividend: ExprId,
    prior_relation: ExprId,
    quotient: ExprId,
    remainder: ExprId,
    condition: ExprId,
    true_value: ExprId,
) -> ExprId {
    let true_equality_ty = d.bool_eq(condition, true_value);
    let true_equality_fv = d.fresh_fvar();
    let true_equality = d.kernel().fvar(true_equality_fv);
    let zero = d.zero();
    let successor_dividend = d.succ(prior_dividend);
    let successor_quotient = d.succ(quotient);
    let target = d.div_mod(divisor, successor_dividend, successor_quotient, zero);
    let relation_ty = d.div_mod(divisor, prior_dividend, quotient, remainder);
    let product = d.mul(divisor, quotient);
    let reconstructed = d.add(product, remainder);
    let equation_ty = d.eq(prior_dividend, reconstructed);
    let bound_ty = d.lt(remainder, divisor);
    let relation_motive = d
        .kernel()
        .lam(anon, relation_ty, target, BinderInfo::Default);
    let relation_minor = {
        let equation_fv = d.fresh_fvar();
        let equation = d.kernel().fvar(equation_fv);
        let bound_fv = d.fresh_fvar();
        let _bound = d.kernel().fvar(bound_fv);
        let remainder_eq_predecessor = d.lemma(
            p.eq_of_beq_eq_true,
            &[remainder, divisor_predecessor, true_equality],
        );
        let successor_remainder = d.succ(remainder);
        let successor_remainder_eq_divisor = d.congr(
            remainder,
            divisor_predecessor,
            remainder_eq_predecessor,
            &|d, value| d.succ(value),
        );
        let next_product = d.mul(divisor, successor_quotient);
        let next_reconstructed = d.add(next_product, zero);
        let next_equation_ty = d.eq(successor_dividend, next_reconstructed);
        let successor_reconstructed = d.succ(reconstructed);
        let lifted = d.congr(prior_dividend, reconstructed, equation, &|d, value| {
            d.succ(value)
        });
        let product_plus_successor_remainder = d.add(product, successor_remainder);
        let successor_eq_product_plus_successor_remainder = d.refl(successor_reconstructed);
        let product_plus_divisor = d.add(product, divisor);
        let replace_remainder = d.congr(
            successor_remainder,
            divisor,
            successor_remainder_eq_divisor,
            &|d, value| d.add(product, value),
        );
        let product_plus_divisor_eq_next = d.refl(product_plus_divisor);
        let (_, next_equation) = d.chain(
            successor_dividend,
            &[
                (successor_reconstructed, lifted),
                (
                    product_plus_successor_remainder,
                    successor_eq_product_plus_successor_remainder,
                ),
                (product_plus_divisor, replace_remainder),
                (next_reconstructed, product_plus_divisor_eq_next),
            ],
        );
        let zero_bound_ty = d.lt(zero, divisor);
        let zero_le_predecessor = d.lemma(p.zero_le, &[divisor_predecessor]);
        let zero_bound = d.lemma(
            p.le_succ_succ,
            &[zero, divisor_predecessor, zero_le_predecessor],
        );
        let body = d.const_app(
            p.logic.and_intro,
            &[next_equation_ty, zero_bound_ty, next_equation, zero_bound],
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
            prior_relation,
        ],
    );
    d.lam_fv(true_equality_fv, true_equality_ty, body)
}
