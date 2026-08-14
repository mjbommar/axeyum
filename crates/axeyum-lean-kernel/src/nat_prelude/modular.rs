//! Modular congruence: `Nat.modEq d a b := exists u v, a + d*u = b + d*v`.
//!
//! Reflexivity, symmetry, transitivity, the remainder characterization, the
//! divisibility bridge, and additive/multiplicative closure.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;

/// Balanced-witness congruence over naturals. This representation needs
/// neither signed subtraction nor an executable remainder function.
pub(super) fn declare_modular_congruence(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // modEq d a b := ∃ u v, a + d*u = b + d*v
    {
        let modulus_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(modulus_fv);
        let left_fv = d.fresh_fvar();
        let left = d.kernel().fvar(left_fv);
        let right_fv = d.fresh_fvar();
        let right = d.kernel().fvar(right_fv);
        let body = d.mod_eq_witnesses(modulus, left, right);
        let value = {
            let with_right = d.lam_fv(right_fv, nat, body);
            let with_left = d.lam_fv(left_fv, nat, with_right);
            d.lam_fv(modulus_fv, nat, with_left)
        };
        let ty = {
            let with_right = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_left = d.kernel().pi(anon, nat, with_right, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_left, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.mod_eq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // mod_eq_refl : ∀ d a, modEq d a a
    d.theorem(p.mod_eq_refl, 2, &|d, v| {
        let (modulus, value) = (v[0], v[1]);
        let zero = d.zero();
        let outer_predicate = d.mod_eq_outer_predicate(modulus, value, value);
        let inner_predicate = d.mod_eq_inner_predicate(modulus, value, value, zero);
        let equation = d.refl(value);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let inner = d.apply(intro, &[nat, inner_predicate, zero, equation]);
        let proof = d.apply(intro, &[nat, outer_predicate, zero, inner]);
        (d.mod_eq(modulus, value, value), proof)
    })?;

    // mod_eq_symm : ∀ d a b, modEq d a b → modEq d b a
    d.theorem(p.mod_eq_symm, 3, &|d, v| {
        let (modulus, left, right) = (v[0], v[1], v[2]);
        let source = d.mod_eq(modulus, left, right);
        let target = d.mod_eq(modulus, right, left);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(modulus, left, right, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, left, right, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_source, target, BinderInfo::Default);
            let inner_minor = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let left_sum = d.mod_eq_sum(modulus, left, u);
                let right_sum = d.mod_eq_sum(modulus, right, w);
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);
                let reversed = d.symm(left_sum, right_sum, equation);
                let target_outer = d.mod_eq_outer_predicate(modulus, right, left);
                let target_inner = d.mod_eq_inner_predicate(modulus, right, left, w);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner_proof = d.apply(intro, &[nat, target_inner, u, reversed]);
                let body = d.apply(intro, &[nat, target_outer, w, inner_proof]);
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(w_fv, nat, with_equation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_source_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                source_proof,
            ],
        );
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;

    declare_mod_eq_trans(d, &p, nat, anon, one)?;
    declare_mod_eq_add_left(d, &p, nat, anon, one)?;
    declare_mod_eq_additive_compatibility(d, &p)?;
    declare_mod_eq_mul_left(d, &p, nat, anon, one)?;
    declare_mod_eq_multiplicative_compatibility(d, &p)?;
    declare_div_mod_same_remainder_mod_eq(d, &p, nat, anon, one)?;
    declare_div_mod_remainder_eq_of_mod_eq(d, &p, nat, anon, one)?;
    declare_mod_eq_iff_div_mod_remainder_eq(d, &p)?;
    declare_mod_eq_zero_of_dvd(d, &p, nat, anon, one)?;
    declare_dvd_of_mod_eq_zero_of_pos(d, &p, nat, anon, one)?;
    declare_mod_eq_zero_iff_dvd(d, &p, nat, anon, one)?;
    Ok(())
}

fn declare_div_mod_same_remainder_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // div_mod_same_remainder_mod_eq :
    //   divMod d a qa r → divMod d b qb r → modEq d a b
    // The balanced congruence witnesses are the opposite quotients:
    // a + d*qb = (d*qa+r)+d*qb = (d*qb+r)+d*qa = b + d*qa.
    d.theorem(p.div_mod_same_remainder_mod_eq, 6, &|d, values| {
        let (modulus, left, right, left_quotient, right_quotient, remainder) = (
            values[0], values[1], values[2], values[3], values[4], values[5],
        );
        let left_relation_ty = d.div_mod(modulus, left, left_quotient, remainder);
        let right_relation_ty = d.div_mod(modulus, right, right_quotient, remainder);
        let target = d.mod_eq(modulus, left, right);
        let left_relation_fv = d.fresh_fvar();
        let left_relation = d.kernel().fvar(left_relation_fv);
        let right_relation_fv = d.fresh_fvar();
        let right_relation = d.kernel().fvar(right_relation_fv);

        let left_product = d.mul(modulus, left_quotient);
        let right_product = d.mul(modulus, right_quotient);
        let left_reconstructed = d.add(left_product, remainder);
        let right_reconstructed = d.add(right_product, remainder);
        let left_equation_ty = d.eq(left, left_reconstructed);
        let right_equation_ty = d.eq(right, right_reconstructed);
        let bound_ty = d.lt(remainder, modulus);

        let right_to_target = d.arrow(right_relation_ty, target);
        let left_motive =
            d.kernel()
                .lam(anon, left_relation_ty, right_to_target, BinderInfo::Default);
        let left_minor = {
            let left_equation_fv = d.fresh_fvar();
            let left_equation = d.kernel().fvar(left_equation_fv);
            let left_bound_fv = d.fresh_fvar();

            let right_motive = d
                .kernel()
                .lam(anon, right_relation_ty, target, BinderInfo::Default);
            let right_minor = {
                let right_equation_fv = d.fresh_fvar();
                let right_equation = d.kernel().fvar(right_equation_fv);
                let right_bound_fv = d.fresh_fvar();

                let start = d.add(left, right_product);
                let left_expanded = d.add(left_reconstructed, right_product);
                let left_then_right = d.add(left_product, right_product);
                let products_left_first = d.add(left_then_right, remainder);
                let right_then_left = d.add(right_product, left_product);
                let products_right_first = d.add(right_then_left, remainder);
                let right_expanded = d.add(right_reconstructed, left_product);
                let finish = d.add(right, left_product);

                let expand_left = d.congr(left, left_reconstructed, left_equation, &|d, value| {
                    d.add(value, right_product)
                });
                let regroup_left =
                    d.lemma(p.add_right_comm, &[left_product, remainder, right_product]);
                let commute_products = d.lemma(p.add_comm, &[left_product, right_product]);
                let commute_under_remainder = d.congr(
                    left_then_right,
                    right_then_left,
                    commute_products,
                    &|d, value| d.add(value, remainder),
                );
                let regroup_right_forward =
                    d.lemma(p.add_right_comm, &[right_product, remainder, left_product]);
                let regroup_right =
                    d.symm(right_expanded, products_right_first, regroup_right_forward);
                let right_equation_rev = d.symm(right, right_reconstructed, right_equation);
                let collapse_right = d.congr(
                    right_reconstructed,
                    right,
                    right_equation_rev,
                    &|d, value| d.add(value, left_product),
                );
                let (_, equation) = d.chain(
                    start,
                    &[
                        (left_expanded, expand_left),
                        (products_left_first, regroup_left),
                        (products_right_first, commute_under_remainder),
                        (right_expanded, regroup_right),
                        (finish, collapse_right),
                    ],
                );

                let target_outer = d.mod_eq_outer_predicate(modulus, left, right);
                let target_inner = d.mod_eq_inner_predicate(modulus, left, right, right_quotient);
                let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner = d.apply(exists_intro, &[nat, target_inner, left_quotient, equation]);
                let body = d.apply(exists_intro, &[nat, target_outer, right_quotient, inner]);
                let with_bound = d.lam_fv(right_bound_fv, bound_ty, body);
                d.lam_fv(right_equation_fv, right_equation_ty, with_bound)
            };
            let level_zero = d.kernel().level_zero();
            let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
            let body = d.apply(
                and_rec,
                &[
                    right_equation_ty,
                    bound_ty,
                    right_motive,
                    right_minor,
                    right_relation,
                ],
            );
            let with_right_relation = d.lam_fv(right_relation_fv, right_relation_ty, body);
            let with_bound = d.lam_fv(left_bound_fv, bound_ty, with_right_relation);
            d.lam_fv(left_equation_fv, left_equation_ty, with_bound)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                left_equation_ty,
                bound_ty,
                left_motive,
                left_minor,
                left_relation,
            ],
        );
        let stmt = d.arrow(left_relation_ty, right_to_target);
        let proof = d.lam_fv(left_relation_fv, left_relation_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_div_mod_remainder_eq_of_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // div_mod_remainder_eq_of_mod_eq :
    //   modEq d a b → divMod d a qa ra → divMod d b qb rb → ra = rb
    // A balanced witness shifts both divisions to the same dividend; relational
    // uniqueness then compares their remainders.
    d.theorem(p.div_mod_remainder_eq_of_mod_eq, 7, &|d, values| {
        let (modulus, left, right, left_quotient, left_remainder, right_quotient, right_remainder) = (
            values[0], values[1], values[2], values[3], values[4], values[5], values[6],
        );
        let congruence_ty = d.mod_eq(modulus, left, right);
        let left_relation_ty =
            d.div_mod(modulus, left, left_quotient, left_remainder);
        let right_relation_ty =
            d.div_mod(modulus, right, right_quotient, right_remainder);
        let target = d.eq(left_remainder, right_remainder);
        let congruence_fv = d.fresh_fvar();
        let congruence = d.kernel().fvar(congruence_fv);
        let left_relation_fv = d.fresh_fvar();
        let left_relation = d.kernel().fvar(left_relation_fv);
        let right_relation_fv = d.fresh_fvar();
        let right_relation = d.kernel().fvar(right_relation_fv);

        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d
            .kernel()
            .lam(anon, congruence_ty, target, BinderInfo::Default);
        let outer_minor = {
            let left_shift_fv = d.fresh_fvar();
            let left_shift = d.kernel().fvar(left_shift_fv);
            let inner_exists =
                d.mod_eq_inner_exists(modulus, left, right, left_shift);
            let inner_exists_fv = d.fresh_fvar();
            let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
            let inner_predicate =
                d.mod_eq_inner_predicate(modulus, left, right, left_shift);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_exists, target, BinderInfo::Default);
            let inner_minor = {
                let right_shift_fv = d.fresh_fvar();
                let right_shift = d.kernel().fvar(right_shift_fv);
                let shifted_left = d.mod_eq_sum(modulus, left, left_shift);
                let shifted_right = d.mod_eq_sum(modulus, right, right_shift);
                let witness_equation_ty = d.eq(shifted_left, shifted_right);
                let witness_equation_fv = d.fresh_fvar();
                let witness_equation = d.kernel().fvar(witness_equation_fv);

                let shifted_left_quotient = d.add(left_quotient, left_shift);
                let shifted_right_quotient = d.add(right_quotient, right_shift);
                let left_division = d.lemma(
                    p.div_mod_add_multiple,
                    &[
                        modulus,
                        left,
                        left_quotient,
                        left_remainder,
                        left_shift,
                        left_relation,
                    ],
                );
                let right_division = d.lemma(
                    p.div_mod_add_multiple,
                    &[
                        modulus,
                        right,
                        right_quotient,
                        right_remainder,
                        right_shift,
                        right_relation,
                    ],
                );
                let witness_equation_rev =
                    d.symm(shifted_left, shifted_right, witness_equation);
                let right_motive_at_shifted_right =
                    d.eq_motive(shifted_right, &|d, dividend| {
                        d.div_mod(
                            modulus,
                            dividend,
                            shifted_right_quotient,
                            right_remainder,
                        )
                    });
                let right_division_at_left = d.transport(
                    shifted_right,
                    right_motive_at_shifted_right,
                    right_division,
                    shifted_left,
                    witness_equation_rev,
                );
                let unique = d.lemma(
                    p.div_mod_unique,
                    &[
                        modulus,
                        shifted_left,
                        shifted_left_quotient,
                        left_remainder,
                        shifted_right_quotient,
                        right_remainder,
                        left_division,
                        right_division_at_left,
                    ],
                );
                let quotient_eq_ty =
                    d.eq(shifted_left_quotient, shifted_right_quotient);
                let unique_ty = d.const_app(p.logic.and, &[quotient_eq_ty, target]);
                let unique_motive = d
                    .kernel()
                    .lam(anon, unique_ty, target, BinderInfo::Default);
                let unique_minor = {
                    let quotient_eq_fv = d.fresh_fvar();
                    let remainder_eq_fv = d.fresh_fvar();
                    let remainder_eq = d.kernel().fvar(remainder_eq_fv);
                    let with_remainder =
                        d.lam_fv(remainder_eq_fv, target, remainder_eq);
                    d.lam_fv(quotient_eq_fv, quotient_eq_ty, with_remainder)
                };
                let level_zero = d.kernel().level_zero();
                let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
                let body = d.apply(
                    and_rec,
                    &[quotient_eq_ty, target, unique_motive, unique_minor, unique],
                );
                let with_equation =
                    d.lam_fv(witness_equation_fv, witness_equation_ty, body);
                d.lam_fv(right_shift_fv, nat, with_equation)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                exists_rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_exists_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
            d.lam_fv(left_shift_fv, nat, with_inner)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                congruence,
            ],
        );
        let right_to_target = d.arrow(right_relation_ty, target);
        let left_to_target = d.arrow(left_relation_ty, right_to_target);
        let stmt = d.arrow(congruence_ty, left_to_target);
        let with_right = d.lam_fv(right_relation_fv, right_relation_ty, body);
        let with_left = d.lam_fv(left_relation_fv, left_relation_ty, with_right);
        let proof = d.lam_fv(congruence_fv, congruence_ty, with_left);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_iff_div_mod_remainder_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_iff_div_mod_remainder_eq :
    //   divMod d a qa ra → divMod d b qb rb → (modEq d a b ↔ ra = rb)
    d.theorem(p.mod_eq_iff_div_mod_remainder_eq, 7, &|d, values| {
        let (modulus, left, right, left_quotient, left_remainder, right_quotient, right_remainder) = (
            values[0], values[1], values[2], values[3], values[4], values[5], values[6],
        );
        let left_relation_ty =
            d.div_mod(modulus, left, left_quotient, left_remainder);
        let right_relation_ty =
            d.div_mod(modulus, right, right_quotient, right_remainder);
        let congruence_ty = d.mod_eq(modulus, left, right);
        let remainder_eq_ty = d.eq(left_remainder, right_remainder);
        let target = d.const_app(p.logic.iff, &[congruence_ty, remainder_eq_ty]);
        let left_relation_fv = d.fresh_fvar();
        let left_relation = d.kernel().fvar(left_relation_fv);
        let right_relation_fv = d.fresh_fvar();
        let right_relation = d.kernel().fvar(right_relation_fv);

        let forward = {
            let congruence_fv = d.fresh_fvar();
            let congruence = d.kernel().fvar(congruence_fv);
            let body = d.lemma(
                p.div_mod_remainder_eq_of_mod_eq,
                &[
                    modulus,
                    left,
                    right,
                    left_quotient,
                    left_remainder,
                    right_quotient,
                    right_remainder,
                    congruence,
                    left_relation,
                    right_relation,
                ],
            );
            d.lam_fv(congruence_fv, congruence_ty, body)
        };
        let reverse = {
            let remainder_eq_fv = d.fresh_fvar();
            let remainder_eq = d.kernel().fvar(remainder_eq_fv);
            let left_remainder_motive = d.eq_motive(left_remainder, &|d, remainder| {
                d.div_mod(modulus, left, left_quotient, remainder)
            });
            let left_relation_at_right_remainder = d.transport(
                left_remainder,
                left_remainder_motive,
                left_relation,
                right_remainder,
                remainder_eq,
            );
            let body = d.lemma(
                p.div_mod_same_remainder_mod_eq,
                &[
                    modulus,
                    left,
                    right,
                    left_quotient,
                    right_quotient,
                    right_remainder,
                    left_relation_at_right_remainder,
                    right_relation,
                ],
            );
            d.lam_fv(remainder_eq_fv, remainder_eq_ty, body)
        };
        let body = d.const_app(
            p.logic.iff_intro,
            &[congruence_ty, remainder_eq_ty, forward, reverse],
        );
        let right_to_target = d.arrow(right_relation_ty, target);
        let stmt = d.arrow(left_relation_ty, right_to_target);
        let with_right = d.lam_fv(right_relation_fv, right_relation_ty, body);
        let proof = d.lam_fv(left_relation_fv, left_relation_ty, with_right);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_zero_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_zero_of_dvd : dvd d n → modEq d n zero
    // A divisibility witness q becomes balanced congruence witnesses 0 and q.
    d.theorem(p.mod_eq_zero_of_dvd, 2, &|d, values| {
        let (modulus, value) = (values[0], values[1]);
        let zero = d.zero();
        let source = d.dvd(modulus, value);
        let target = d.mod_eq(modulus, value, zero);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let predicate = d.dvd_predicate(modulus, value);
        let motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let minor = {
            let quotient_fv = d.fresh_fvar();
            let quotient = d.kernel().fvar(quotient_fv);
            let product = d.mul(modulus, quotient);
            let equation_ty = d.eq(value, product);
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);

            let zero_product = d.mul(modulus, zero);
            let start = d.add(value, zero_product);
            let value_plus_zero = d.add(value, zero);
            let zero_plus_product = d.add(zero, product);
            let remove_zero_product = d.lemma(p.mul_zero, &[modulus]);
            let step1 = d.congr(zero_product, zero, remove_zero_product, &|d, x| {
                d.add(value, x)
            });
            let step2 = d.lemma(p.add_zero, &[value]);
            let step3 = equation;
            let zero_add_product = d.lemma(p.zero_add, &[product]);
            let step4 = d.symm(zero_plus_product, product, zero_add_product);
            let (_, balanced_equation) = d.chain(
                start,
                &[
                    (value_plus_zero, step1),
                    (value, step2),
                    (product, step3),
                    (zero_plus_product, step4),
                ],
            );

            let target_outer = d.mod_eq_outer_predicate(modulus, value, zero);
            let target_inner = d.mod_eq_inner_predicate(modulus, value, zero, zero);
            let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let inner = d.apply(
                exists_intro,
                &[nat, target_inner, quotient, balanced_equation],
            );
            let body = d.apply(exists_intro, &[nat, target_outer, zero, inner]);
            let with_equation = d.lam_fv(equation_fv, equation_ty, body);
            d.lam_fv(quotient_fv, nat, with_equation)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(exists_rec, &[nat, predicate, motive, minor, source_proof]);
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_dvd_of_mod_eq_zero_of_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // dvd_of_mod_eq_zero_of_pos : Le one d → modEq d n zero → dvd d n
    // A balanced witness says n+d*u=d*v. Both the sum and d*u are divisible
    // by d, so positive-divisor cancellation yields d ∣ n.
    d.theorem(p.dvd_of_mod_eq_zero_of_pos, 2, &|d, values| {
        let (modulus, value) = (values[0], values[1]);
        let zero = d.zero();
        let one_value = d.num(1);
        let positive_ty = d.le(one_value, modulus);
        let congruence_ty = d.mod_eq(modulus, value, zero);
        let target = d.dvd(modulus, value);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let congruence_fv = d.fresh_fvar();
        let congruence = d.kernel().fvar(congruence_fv);

        let outer_predicate = d.mod_eq_outer_predicate(modulus, value, zero);
        let outer_motive = d
            .kernel()
            .lam(anon, congruence_ty, target, BinderInfo::Default);
        let outer_minor = {
            let left_witness_fv = d.fresh_fvar();
            let left_witness = d.kernel().fvar(left_witness_fv);
            let inner_exists = d.mod_eq_inner_exists(modulus, value, zero, left_witness);
            let inner_exists_fv = d.fresh_fvar();
            let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, value, zero, left_witness);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_exists, target, BinderInfo::Default);
            let inner_minor = {
                let right_witness_fv = d.fresh_fvar();
                let right_witness = d.kernel().fvar(right_witness_fv);
                let left_multiple = d.mul(modulus, left_witness);
                let right_multiple = d.mul(modulus, right_witness);
                let value_plus_multiple = d.add(value, left_multiple);
                let zero_plus_right_multiple = d.add(zero, right_multiple);
                let equation_ty = d.eq(value_plus_multiple, zero_plus_right_multiple);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);

                let remove_zero = d.lemma(p.zero_add, &[right_multiple]);
                let (_, sum_equation) = d.chain(
                    value_plus_multiple,
                    &[
                        (zero_plus_right_multiple, equation),
                        (right_multiple, remove_zero),
                    ],
                );
                let sum_predicate = d.dvd_predicate(modulus, value_plus_multiple);
                let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let divides_sum = d.apply(
                    exists_intro,
                    &[nat, sum_predicate, right_witness, sum_equation],
                );
                let divides_multiple = d.lemma(p.dvd_mul, &[modulus, left_witness]);
                let multiple_plus_value = d.add(left_multiple, value);
                let commute = d.lemma(p.add_comm, &[value, left_multiple]);
                let sum_motive = d.eq_motive(value_plus_multiple, &|d, sum| d.dvd(modulus, sum));
                let divides_commuted_sum = d.transport(
                    value_plus_multiple,
                    sum_motive,
                    divides_sum,
                    multiple_plus_value,
                    commute,
                );
                let body = d.lemma(
                    p.dvd_add_right_cancel_of_pos,
                    &[
                        modulus,
                        left_multiple,
                        value,
                        positive,
                        divides_multiple,
                        divides_commuted_sum,
                    ],
                );
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(right_witness_fv, nat, with_equation)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                exists_rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_exists_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
            d.lam_fv(left_witness_fv, nat, with_inner)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[nat, outer_predicate, outer_motive, outer_minor, congruence],
        );
        let congruence_to_target = d.arrow(congruence_ty, target);
        let stmt = d.arrow(positive_ty, congruence_to_target);
        let with_congruence = d.lam_fv(congruence_fv, congruence_ty, body);
        let proof = d.lam_fv(positive_fv, positive_ty, with_congruence);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_zero_iff_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_zero_iff_dvd : modEq d n zero ↔ dvd d n
    // Induction on d keeps the degenerate zero modulus explicit. At zero the
    // balanced equation itself supplies a zero-factor witness; at a successor
    // the positive cancellation theorem applies.
    d.theorem(p.mod_eq_zero_iff_dvd, 2, &|d, values| {
        let (modulus, value) = (values[0], values[1]);
        let zero = d.zero();
        let congruence_ty = d.mod_eq(modulus, value, zero);
        let divides_ty = d.dvd(modulus, value);

        let forward_motive = |d: &mut NatDev<'_>, candidate: ExprId| {
            let congruence = d.mod_eq(candidate, value, zero);
            let divides = d.dvd(candidate, value);
            d.arrow(congruence, divides)
        };
        let forward = d.induct(
            &forward_motive,
            &|d| {
                let congruence_ty = d.mod_eq(zero, value, zero);
                let target = d.dvd(zero, value);
                let congruence_fv = d.fresh_fvar();
                let congruence = d.kernel().fvar(congruence_fv);
                let outer_predicate = d.mod_eq_outer_predicate(zero, value, zero);
                let outer_motive = d
                    .kernel()
                    .lam(anon, congruence_ty, target, BinderInfo::Default);
                let outer_minor = {
                    let left_witness_fv = d.fresh_fvar();
                    let left_witness = d.kernel().fvar(left_witness_fv);
                    let inner_exists = d.mod_eq_inner_exists(zero, value, zero, left_witness);
                    let inner_exists_fv = d.fresh_fvar();
                    let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
                    let inner_predicate = d.mod_eq_inner_predicate(zero, value, zero, left_witness);
                    let inner_motive =
                        d.kernel()
                            .lam(anon, inner_exists, target, BinderInfo::Default);
                    let inner_minor = {
                        let right_witness_fv = d.fresh_fvar();
                        let right_witness = d.kernel().fvar(right_witness_fv);
                        let left_multiple = d.mul(zero, left_witness);
                        let right_multiple = d.mul(zero, right_witness);
                        let left_sum = d.add(value, left_multiple);
                        let right_sum = d.add(zero, right_multiple);
                        let equation_ty = d.eq(left_sum, right_sum);
                        let equation_fv = d.fresh_fvar();
                        let equation = d.kernel().fvar(equation_fv);

                        let value_plus_zero = d.add(value, zero);
                        let add_zero = d.lemma(p.add_zero, &[value]);
                        let add_zero_rev = d.symm(value_plus_zero, value, add_zero);
                        let zero_mul_left = d.lemma(p.zero_mul, &[left_witness]);
                        let zero_to_left_multiple = d.symm(left_multiple, zero, zero_mul_left);
                        let expose_left_multiple =
                            d.congr(zero, left_multiple, zero_to_left_multiple, &|d, x| {
                                d.add(value, x)
                            });
                        let remove_right_zero = d.lemma(p.zero_add, &[right_multiple]);
                        let (_, witness_equation) = d.chain(
                            value,
                            &[
                                (value_plus_zero, add_zero_rev),
                                (left_sum, expose_left_multiple),
                                (right_sum, equation),
                                (right_multiple, remove_right_zero),
                            ],
                        );
                        let predicate = d.dvd_predicate(zero, value);
                        let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                        let body = d.apply(
                            exists_intro,
                            &[nat, predicate, right_witness, witness_equation],
                        );
                        let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                        d.lam_fv(right_witness_fv, nat, with_equation)
                    };
                    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                    let body = d.apply(
                        exists_rec,
                        &[
                            nat,
                            inner_predicate,
                            inner_motive,
                            inner_minor,
                            inner_exists_proof,
                        ],
                    );
                    let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
                    d.lam_fv(left_witness_fv, nat, with_inner)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, outer_predicate, outer_motive, outer_minor, congruence],
                );
                d.lam_fv(congruence_fv, congruence_ty, body)
            },
            &|d, predecessor, _ih| {
                let successor = d.succ(predecessor);
                let congruence_ty = d.mod_eq(successor, value, zero);
                let congruence_fv = d.fresh_fvar();
                let congruence = d.kernel().fvar(congruence_fv);
                let zero_le_predecessor = d.lemma(p.zero_le, &[predecessor]);
                let positive = d.lemma(p.le_succ_succ, &[zero, predecessor, zero_le_predecessor]);
                let body = d.lemma(
                    p.dvd_of_mod_eq_zero_of_pos,
                    &[successor, value, positive, congruence],
                );
                d.lam_fv(congruence_fv, congruence_ty, body)
            },
            modulus,
        );
        let reverse = {
            let divides_fv = d.fresh_fvar();
            let divides = d.kernel().fvar(divides_fv);
            let body = d.lemma(p.mod_eq_zero_of_dvd, &[modulus, value, divides]);
            d.lam_fv(divides_fv, divides_ty, body)
        };
        let target = d.const_app(p.logic.iff, &[congruence_ty, divides_ty]);
        let proof = d.const_app(
            p.logic.iff_intro,
            &[congruence_ty, divides_ty, forward, reverse],
        );
        (target, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_trans(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_trans, 4, &|d, v| {
        let (modulus, left, middle, right) = (v[0], v[1], v[2], v[3]);
        let first_ty = d.mod_eq(modulus, left, middle);
        let second_ty = d.mod_eq(modulus, middle, right);
        let target = d.mod_eq(modulus, left, right);
        let first_fv = d.fresh_fvar();
        let first = d.kernel().fvar(first_fv);
        let second_fv = d.fresh_fvar();
        let second = d.kernel().fvar(second_fv);
        let first_outer = d.mod_eq_outer_predicate(modulus, left, middle);
        let first_motive = d.kernel().lam(anon, first_ty, target, BinderInfo::Default);
        let first_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let first_inner_ty = d.mod_eq_inner_exists(modulus, left, middle, u);
            let first_inner_fv = d.fresh_fvar();
            let first_inner = d.kernel().fvar(first_inner_fv);
            let first_inner_pred = d.mod_eq_inner_predicate(modulus, left, middle, u);
            let first_inner_motive =
                d.kernel()
                    .lam(anon, first_inner_ty, target, BinderInfo::Default);
            let first_inner_minor = {
                let v_fv = d.fresh_fvar();
                let vw = d.kernel().fvar(v_fv);
                let first_lhs = d.mod_eq_sum(modulus, left, u);
                let first_rhs = d.mod_eq_sum(modulus, middle, vw);
                let first_eq_ty = d.eq(first_lhs, first_rhs);
                let first_eq_fv = d.fresh_fvar();
                let first_eq = d.kernel().fvar(first_eq_fv);
                let second_outer = d.mod_eq_outer_predicate(modulus, middle, right);
                let second_motive = d.kernel().lam(anon, second_ty, target, BinderInfo::Default);
                let second_minor = build_mod_eq_trans_second_minor(
                    d, &p, nat, anon, one, modulus, left, middle, right, u, vw, first_eq,
                );
                let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    rec,
                    &[nat, second_outer, second_motive, second_minor, second],
                );
                let with_eq = d.lam_fv(first_eq_fv, first_eq_ty, body);
                d.lam_fv(v_fv, nat, with_eq)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    first_inner_pred,
                    first_inner_motive,
                    first_inner_minor,
                    first_inner,
                ],
            );
            let with_inner = d.lam_fv(first_inner_fv, first_inner_ty, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, first_outer, first_motive, first_minor, first]);
        let second_to_target = d.arrow(second_ty, target);
        let stmt = d.arrow(first_ty, second_to_target);
        let with_second = d.lam_fv(second_fv, second_ty, body);
        let proof = d.lam_fv(first_fv, first_ty, with_second);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_add_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_add_left, 4, &|d, values| {
        let (modulus, left, right, shift) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let shifted_left = d.add(shift, left);
        let shifted_right = d.add(shift, right);
        let target = d.mod_eq(modulus, shifted_left, shifted_right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(modulus, left, right, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, left, right, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_source, target, BinderInfo::Default);
            let inner_minor = {
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let du = d.mul(modulus, u);
                let dv = d.mul(modulus, v);
                let left_sum = d.add(left, du);
                let right_sum = d.add(right, dv);
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);
                let target_left = d.mod_eq_sum(modulus, shifted_left, u);
                let target_right = d.mod_eq_sum(modulus, shifted_right, v);
                let nested_left = d.add(shift, left_sum);
                let nested_right = d.add(shift, right_sum);
                let assoc_left = d.lemma(p.add_assoc, &[shift, left, du]);
                let step1 = assoc_left;
                let step2 = d.congr(left_sum, right_sum, equation, &|d, z| d.add(shift, z));
                let assoc_right = d.lemma(p.add_assoc, &[shift, right, dv]);
                let step3 = d.symm(target_right, nested_right, assoc_right);
                let (_, shifted_equation) = d.chain(
                    target_left,
                    &[
                        (nested_left, step1),
                        (nested_right, step2),
                        (target_right, step3),
                    ],
                );
                let target_outer = d.mod_eq_outer_predicate(modulus, shifted_left, shifted_right);
                let target_inner =
                    d.mod_eq_inner_predicate(modulus, shifted_left, shifted_right, u);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner_proof = d.apply(intro, &[nat, target_inner, v, shifted_equation]);
                let body = d.apply(intro, &[nat, target_outer, u, inner_proof]);
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(v_fv, nat, with_equation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_source_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                source_proof,
            ],
        );
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_additive_compatibility(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_add_right : modEq d a b → modEq d (a+c) (b+c)
    // Reuse left-addition compatibility, then transport both endpoints across
    // proved commutativity rather than reopening the existential witnesses.
    d.theorem(p.mod_eq_add_right, 4, &|d, values| {
        let (modulus, left, right, shift) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let shift_left = d.add(shift, left);
        let left_shift = d.add(left, shift);
        let shift_right = d.add(shift, right);
        let right_shift = d.add(right, shift);
        let shifted = d.lemma(
            p.mod_eq_add_left,
            &[modulus, left, right, shift, source_proof],
        );
        let commute_left = d.lemma(p.add_comm, &[shift, left]);
        let left_motive = d.eq_motive(shift_left, &|d, value| {
            d.mod_eq(modulus, value, shift_right)
        });
        let left_transport =
            d.transport(shift_left, left_motive, shifted, left_shift, commute_left);
        let commute_right = d.lemma(p.add_comm, &[shift, right]);
        let right_motive = d.eq_motive(shift_right, &|d, value| {
            d.mod_eq(modulus, left_shift, value)
        });
        let body = d.transport(
            shift_right,
            right_motive,
            left_transport,
            right_shift,
            commute_right,
        );
        let target = d.mod_eq(modulus, left_shift, right_shift);
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;

    // mod_eq_add : modEq d a b → modEq d c e → modEq d (a+c) (b+e)
    d.theorem(p.mod_eq_add, 5, &|d, values| {
        let (modulus, a, b, c, e) = (values[0], values[1], values[2], values[3], values[4]);
        let first_ty = d.mod_eq(modulus, a, b);
        let second_ty = d.mod_eq(modulus, c, e);
        let first_fv = d.fresh_fvar();
        let first = d.kernel().fvar(first_fv);
        let second_fv = d.fresh_fvar();
        let second = d.kernel().fvar(second_fv);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let be = d.add(b, e);
        let first_shifted = d.lemma(p.mod_eq_add_right, &[modulus, a, b, c, first]);
        let second_shifted = d.lemma(p.mod_eq_add_left, &[modulus, c, e, b, second]);
        let body = d.lemma(
            p.mod_eq_trans,
            &[modulus, ac, bc, be, first_shifted, second_shifted],
        );
        let target = d.mod_eq(modulus, ac, be);
        let second_to_target = d.arrow(second_ty, target);
        let stmt = d.arrow(first_ty, second_to_target);
        let with_second = d.lam_fv(second_fv, second_ty, body);
        let proof = d.lam_fv(first_fv, first_ty, with_second);
        (stmt, proof)
    })?;

    Ok(())
}

fn declare_mod_eq_mul_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_mul_left, 4, &|d, values| {
        let (modulus, left, right, factor) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let scaled_left = d.mul(factor, left);
        let scaled_right = d.mul(factor, right);
        let target = d.mod_eq(modulus, scaled_left, scaled_right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(modulus, left, right, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, left, right, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_source, target, BinderInfo::Default);
            let inner_minor = {
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let du = d.mul(modulus, u);
                let dv = d.mul(modulus, v);
                let left_sum = d.add(left, du);
                let right_sum = d.add(right, dv);
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);
                let factor_u = d.mul(factor, u);
                let factor_v = d.mul(factor, v);
                let target_left = d.mod_eq_sum(modulus, scaled_left, factor_u);
                let target_right = d.mod_eq_sum(modulus, scaled_right, factor_v);
                let factor_du = d.mul(factor, du);
                let factor_dv = d.mul(factor, dv);
                let distributed_left = d.add(scaled_left, factor_du);
                let distributed_right = d.add(scaled_right, factor_dv);
                let factored_left = d.mul(factor, left_sum);
                let factored_right = d.mul(factor, right_sum);

                let scaled_u = mod_eq_scaled_multiple(d, &p, modulus, factor, u);
                let modulus_factor_u = d.mul(modulus, factor_u);
                let step1 = d.congr(modulus_factor_u, factor_du, scaled_u, &|d, value| {
                    d.add(scaled_left, value)
                });
                let left_distrib = d.lemma(p.left_distrib, &[factor, left, du]);
                let step2 = d.symm(factored_left, distributed_left, left_distrib);
                let step3 = d.congr(left_sum, right_sum, equation, &|d, value| {
                    d.mul(factor, value)
                });
                let step4 = d.lemma(p.left_distrib, &[factor, right, dv]);
                let scaled_v = mod_eq_scaled_multiple(d, &p, modulus, factor, v);
                let modulus_factor_v = d.mul(modulus, factor_v);
                let reverse_scaled_v = d.symm(modulus_factor_v, factor_dv, scaled_v);
                let step5 = d.congr(
                    factor_dv,
                    modulus_factor_v,
                    reverse_scaled_v,
                    &|d, value| d.add(scaled_right, value),
                );
                let (_, scaled_equation) = d.chain(
                    target_left,
                    &[
                        (distributed_left, step1),
                        (factored_left, step2),
                        (factored_right, step3),
                        (distributed_right, step4),
                        (target_right, step5),
                    ],
                );
                let target_outer = d.mod_eq_outer_predicate(modulus, scaled_left, scaled_right);
                let target_inner =
                    d.mod_eq_inner_predicate(modulus, scaled_left, scaled_right, factor_u);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner_proof = d.apply(intro, &[nat, target_inner, factor_v, scaled_equation]);
                let body = d.apply(intro, &[nat, target_outer, factor_u, inner_proof]);
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(v_fv, nat, with_equation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_source_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                source_proof,
            ],
        );
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `d * (c*u) = c * (d*u)`, from associativity and commutativity.
fn mod_eq_scaled_multiple(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    factor: ExprId,
    witness: ExprId,
) -> ExprId {
    let p = *p;
    let factor_witness = d.mul(factor, witness);
    let start = d.mul(modulus, factor_witness);
    let modulus_factor = d.mul(modulus, factor);
    let modulus_factor_witness = d.mul(modulus_factor, witness);
    let factor_modulus = d.mul(factor, modulus);
    let factor_modulus_witness = d.mul(factor_modulus, witness);
    let modulus_witness = d.mul(modulus, witness);
    let target = d.mul(factor, modulus_witness);
    let assoc_left = d.lemma(p.mul_assoc, &[modulus, factor, witness]);
    let step1 = d.symm(modulus_factor_witness, start, assoc_left);
    let commute = d.lemma(p.mul_comm, &[modulus, factor]);
    let step2 = d.congr(modulus_factor, factor_modulus, commute, &|d, value| {
        d.mul(value, witness)
    });
    let step3 = d.lemma(p.mul_assoc, &[factor, modulus, witness]);
    let (_, proof) = d.chain(
        start,
        &[
            (modulus_factor_witness, step1),
            (factor_modulus_witness, step2),
            (target, step3),
        ],
    );
    proof
}

fn declare_mod_eq_multiplicative_compatibility(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_mul_right : modEq d a b → modEq d (a*c) (b*c)
    d.theorem(p.mod_eq_mul_right, 4, &|d, values| {
        let (modulus, left, right, factor) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let factor_left = d.mul(factor, left);
        let left_factor = d.mul(left, factor);
        let factor_right = d.mul(factor, right);
        let right_factor = d.mul(right, factor);
        let scaled = d.lemma(
            p.mod_eq_mul_left,
            &[modulus, left, right, factor, source_proof],
        );
        let commute_left = d.lemma(p.mul_comm, &[factor, left]);
        let left_motive = d.eq_motive(factor_left, &|d, value| {
            d.mod_eq(modulus, value, factor_right)
        });
        let left_transport =
            d.transport(factor_left, left_motive, scaled, left_factor, commute_left);
        let commute_right = d.lemma(p.mul_comm, &[factor, right]);
        let right_motive = d.eq_motive(factor_right, &|d, value| {
            d.mod_eq(modulus, left_factor, value)
        });
        let body = d.transport(
            factor_right,
            right_motive,
            left_transport,
            right_factor,
            commute_right,
        );
        let target = d.mod_eq(modulus, left_factor, right_factor);
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;

    // mod_eq_mul : modEq d a b → modEq d c e → modEq d (a*c) (b*e)
    d.theorem(p.mod_eq_mul, 5, &|d, values| {
        let (modulus, a, b, c, e) = (values[0], values[1], values[2], values[3], values[4]);
        let first_ty = d.mod_eq(modulus, a, b);
        let second_ty = d.mod_eq(modulus, c, e);
        let first_fv = d.fresh_fvar();
        let first = d.kernel().fvar(first_fv);
        let second_fv = d.fresh_fvar();
        let second = d.kernel().fvar(second_fv);
        let ac = d.mul(a, c);
        let bc = d.mul(b, c);
        let be = d.mul(b, e);
        let first_scaled = d.lemma(p.mod_eq_mul_right, &[modulus, a, b, c, first]);
        let second_scaled = d.lemma(p.mod_eq_mul_left, &[modulus, c, e, b, second]);
        let body = d.lemma(
            p.mod_eq_trans,
            &[modulus, ac, bc, be, first_scaled, second_scaled],
        );
        let target = d.mod_eq(modulus, ac, be);
        let second_to_target = d.arrow(second_ty, target);
        let stmt = d.arrow(first_ty, second_to_target);
        let with_second = d.lam_fv(second_fv, second_ty, body);
        let proof = d.lam_fv(first_fv, first_ty, with_second);
        (stmt, proof)
    })?;

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_mod_eq_trans_second_minor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
    modulus: ExprId,
    left: ExprId,
    middle: ExprId,
    right: ExprId,
    u: ExprId,
    v: ExprId,
    first_eq: ExprId,
) -> ExprId {
    let p = *p;
    let target = d.mod_eq(modulus, left, right);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let inner_ty = d.mod_eq_inner_exists(modulus, middle, right, x);
    let inner_fv = d.fresh_fvar();
    let inner = d.kernel().fvar(inner_fv);
    let inner_predicate = d.mod_eq_inner_predicate(modulus, middle, right, x);
    let inner_motive = d.kernel().lam(anon, inner_ty, target, BinderInfo::Default);
    let inner_minor = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let middle_x = d.mod_eq_sum(modulus, middle, x);
        let right_y = d.mod_eq_sum(modulus, right, y);
        let second_eq_ty = d.eq(middle_x, right_y);
        let second_eq_fv = d.fresh_fvar();
        let second_eq = d.kernel().fvar(second_eq_fv);

        let ux = d.add(u, x);
        let yv = d.add(y, v);
        let target_left = d.mod_eq_sum(modulus, left, ux);
        let target_right = d.mod_eq_sum(modulus, right, yv);
        let du = d.mul(modulus, u);
        let dx = d.mul(modulus, x);
        let dv = d.mul(modulus, v);
        let dy = d.mul(modulus, y);
        let left_du = d.add(left, du);
        let middle_dv = d.add(middle, dv);
        let middle_dx = d.add(middle, dx);
        let right_dy = d.add(right, dy);
        let du_dx = d.add(du, dx);
        let dx_dv = d.add(dx, dv);
        let dv_dx = d.add(dv, dx);
        let dy_dv = d.add(dy, dv);
        let modulus_ux = d.mul(modulus, ux);
        let modulus_yv = d.mul(modulus, yv);
        let left_nested = d.add(left, du_dx);
        let left_grouped = d.add(left_du, dx);
        let middle_grouped_vx = d.add(middle_dv, dx);
        let middle_nested_vx = d.add(middle, dv_dx);
        let middle_nested_xv = d.add(middle, dx_dv);
        let middle_grouped_xv = d.add(middle_dx, dv);
        let right_grouped = d.add(right_dy, dv);
        let right_nested = d.add(right, dy_dv);

        let distributed_left = d.lemma(p.left_distrib, &[modulus, u, x]);
        let step1 = d.congr(modulus_ux, du_dx, distributed_left, &|d, z| d.add(left, z));
        let associated_left = d.lemma(p.add_assoc, &[left, du, dx]);
        let step2 = d.symm(left_grouped, left_nested, associated_left);
        let step3 = d.congr(left_du, middle_dv, first_eq, &|d, z| d.add(z, dx));
        let step4 = d.lemma(p.add_assoc, &[middle, dv, dx]);
        let commuted = d.lemma(p.add_comm, &[dv, dx]);
        let step5 = d.congr(dv_dx, dx_dv, commuted, &|d, z| d.add(middle, z));
        let associated_middle = d.lemma(p.add_assoc, &[middle, dx, dv]);
        let step6 = d.symm(middle_grouped_xv, middle_nested_xv, associated_middle);
        let step7 = d.congr(middle_dx, right_dy, second_eq, &|d, z| d.add(z, dv));
        let step8 = d.lemma(p.add_assoc, &[right, dy, dv]);
        let distributed_right = d.lemma(p.left_distrib, &[modulus, y, v]);
        let undistributed_right = d.symm(modulus_yv, dy_dv, distributed_right);
        let step9 = d.congr(dy_dv, modulus_yv, undistributed_right, &|d, z| {
            d.add(right, z)
        });
        let (_, equation) = d.chain(
            target_left,
            &[
                (left_nested, step1),
                (left_grouped, step2),
                (middle_grouped_vx, step3),
                (middle_nested_vx, step4),
                (middle_nested_xv, step5),
                (middle_grouped_xv, step6),
                (right_grouped, step7),
                (right_nested, step8),
                (target_right, step9),
            ],
        );
        let target_outer = d.mod_eq_outer_predicate(modulus, left, right);
        let target_inner = d.mod_eq_inner_predicate(modulus, left, right, ux);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let inner_proof = d.apply(intro, &[nat, target_inner, yv, equation]);
        let body = d.apply(intro, &[nat, target_outer, ux, inner_proof]);
        let with_eq = d.lam_fv(second_eq_fv, second_eq_ty, body);
        d.lam_fv(y_fv, nat, with_eq)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let body = d.apply(
        rec,
        &[nat, inner_predicate, inner_motive, inner_minor, inner],
    );
    let with_inner = d.lam_fv(inner_fv, inner_ty, body);
    d.lam_fv(x_fv, nat, with_inner)
}
