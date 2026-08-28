//! The executable `Nat.gcd` and its common-divisor characterization.

use super::NatPrelude;
use super::helpers::{
    and_left, and_right, apply_nat_function_equality, iff_forward, iff_reverse, transport_dvd_left,
    transport_dvd_right,
};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;

/// Bound executable remainder by its positive divisor, then use that checked
/// decrease to define Euclid's algorithm through the logic prelude's generic
/// well-founded fixpoint. This establishes computation and unfolding only;
/// the greatest-common-divisor characterization is intentionally separate.
pub(super) fn declare_executable_gcd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // mod_lt : ∀ x y, 0 < y → mod x y < y
    // Induct on y. The zero branch eliminates the impossible positivity
    // witness; the successor branch projects the checked remainder bound from
    // div_mod_exec and does not need the induction hypothesis.
    d.theorem(p.mod_lt, 2, &|d, values| {
        let (dividend, divisor) = (values[0], values[1]);
        let zero = d.zero();
        let motive = |d: &mut NatDev<'_>, candidate: ExprId| {
            let positive = d.lt(zero, candidate);
            let remainder = d.modulo(dividend, candidate);
            let bound = d.lt(remainder, candidate);
            d.arrow(positive, bound)
        };
        let base = |d: &mut NatDev<'_>| {
            let positive = d.lt(zero, zero);
            let remainder = d.modulo(dividend, zero);
            let bound = d.lt(remainder, zero);
            let positive_fv = d.fresh_fvar();
            let positive_proof = d.kernel().fvar(positive_fv);
            let impossible = d.lemma(p.not_succ_le_zero, &[zero, positive_proof]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let anon = d.kernel().anon();
            let false_motive = d
                .kernel()
                .lam(anon, false_ty, bound, crate::BinderInfo::Default);
            let level_zero = d.kernel().level_zero();
            let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let proof = d.apply(false_rec, &[false_motive, impossible]);
            d.lam_fv(positive_fv, positive, proof)
        };
        let step = |d: &mut NatDev<'_>, predecessor: ExprId, _ih: ExprId| {
            let successor = d.succ(predecessor);
            let positive = d.lt(zero, successor);
            let quotient = d.div(dividend, successor);
            let remainder = d.modulo(dividend, successor);
            let equation_ty = {
                let product = d.mul(successor, quotient);
                let reconstructed = d.add(product, remainder);
                d.eq(dividend, reconstructed)
            };
            let bound_ty = d.lt(remainder, successor);
            let relation_ty = d.const_app(p.logic.and, &[equation_ty, bound_ty]);
            let relation = d.lemma(p.div_mod_exec, &[predecessor, dividend]);
            let relation_motive = {
                let relation_fv = d.fresh_fvar();
                d.lam_fv(relation_fv, relation_ty, bound_ty)
            };
            let minor = {
                let equation_fv = d.fresh_fvar();
                let bound_fv = d.fresh_fvar();
                let bound = d.kernel().fvar(bound_fv);
                let with_bound = d.lam_fv(bound_fv, bound_ty, bound);
                d.lam_fv(equation_fv, equation_ty, with_bound)
            };
            let level_zero = d.kernel().level_zero();
            let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
            let bound = d.apply(
                and_rec,
                &[equation_ty, bound_ty, relation_motive, minor, relation],
            );
            let positive_fv = d.fresh_fvar();
            d.lam_fv(positive_fv, positive, bound)
        };
        let proof = d.induct(&motive, &base, &step, divisor);
        (motive(d, divisor), proof)
    })?;

    // gcd m n := WellFounded.fix lt_well_founded step m n, where the
    // successor branch recursively calls gcd (n % succ k) (succ k).
    let (relation, family, well_founded, step) = gcd_fix_parts(d, &p);
    let one = d.level_one();
    let fix = d.kernel().const_(p.logic.well_founded_fix, vec![one, one]);
    let value = d.apply(fix, &[nat, relation, family, well_founded, step]);
    let nat_to_nat = d.arrow(nat, nat);
    let ty = d.arrow(nat, nat_to_nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gcd,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(10),
    })?;

    // Both public equations are pointwise consequences of the checked generic
    // fixpoint equation. The RHSs reduce through Nat.rec at zero/successor.
    d.theorem(p.gcd_zero_left, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let gcd_zero = d.gcd(zero, value);
        let equation = gcd_fix_equation(d, &p, zero);
        let left_function = d.const_app(p.gcd, &[zero]);
        let identity = {
            let argument_fv = d.fresh_fvar();
            let argument = d.kernel().fvar(argument_fv);
            d.lam_fv(argument_fv, nat, argument)
        };
        let proof = apply_nat_function_equality(d, left_function, identity, equation, value);
        (d.eq(gcd_zero, value), proof)
    })?;

    d.theorem(p.gcd_succ, 2, &|d, values| {
        let (predecessor, value) = (values[0], values[1]);
        let divisor = d.succ(predecessor);
        let left = d.gcd(divisor, value);
        let remainder = d.modulo(value, divisor);
        let right = d.gcd(remainder, divisor);
        let equation = gcd_fix_equation(d, &p, divisor);
        let left_function = d.const_app(p.gcd, &[divisor]);
        let right_function = {
            let argument_fv = d.fresh_fvar();
            let argument = d.kernel().fvar(argument_fv);
            let recursive_remainder = d.modulo(argument, divisor);
            let body = d.gcd(recursive_remainder, divisor);
            d.lam_fv(argument_fv, nat, body)
        };
        let proof = apply_nat_function_equality(d, left_function, right_function, equation, value);
        (d.eq(left, right), proof)
    })?;

    Ok(())
}

/// Establish the semantic greatest-common-divisor contract over all naturals.
/// Both recursive directions follow the executable Euclidean transition and
/// consume `dvd_mod_iff`; neither direction assumes a positive common divisor.
pub(super) fn declare_gcd_semantics(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);

    let gcd_dvd_at = |d: &mut NatDev<'_>, m: ExprId, n: ExprId| {
        let common = d.gcd(m, n);
        let left = d.dvd(common, m);
        let right = d.dvd(common, n);
        d.const_app(p.logic.and, &[left, right])
    };
    let gcd_dvd_row = |d: &mut NatDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = gcd_dvd_at(d, m, n);
        d.pi_fv(n_fv, nat, body)
    };
    let gcd_dvd_family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let row = gcd_dvd_row(d, m);
        d.lam_fv(m_fv, nat, row)
    };
    let gcd_dvd_recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let related_fv = d.fresh_fvar();
        let related_ty = d.lt(predecessor, upper);
        let row = gcd_dvd_row(d, predecessor);
        let at_relation = d.pi_fv(related_fv, related_ty, row);
        d.pi_fv(predecessor_fv, nat, at_relation)
    };
    let gcd_dvd_step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = gcd_dvd_recursive_ty(d, m);
        let row = gcd_dvd_row(d, m);
        let body = d.arrow(recursive, row);
        d.lam_fv(m_fv, nat, body)
    };
    let gcd_dvd_zero_minor = {
        let recursive_fv = d.fresh_fvar();
        let zero = d.zero();
        let recursive_ty = gcd_dvd_recursive_ty(d, zero);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let common = d.gcd(zero, n);
        let equation = d.lemma(p.gcd_zero_left, &[n]);
        let n_to_common = d.symm(common, n, equation);
        let n_divides_zero = d.lemma(p.dvd_zero, &[n]);
        let n_divides_n = d.lemma(p.dvd_refl, &[n]);
        let common_divides_zero =
            transport_dvd_left(d, n, common, n_to_common, zero, n_divides_zero);
        let common_divides_n = transport_dvd_left(d, n, common, n_to_common, n, n_divides_n);
        let left_ty = d.dvd(common, zero);
        let right_ty = d.dvd(common, n);
        let pair = d.const_app(
            p.logic.and_intro,
            &[left_ty, right_ty, common_divides_zero, common_divides_n],
        );
        let with_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(recursive_fv, recursive_ty, with_n)
    };
    let gcd_dvd_succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ih_fv = d.fresh_fvar();
        let ih_ty = {
            let recursive = gcd_dvd_recursive_ty(d, predecessor);
            let row = gcd_dvd_row(d, predecessor);
            d.arrow(recursive, row)
        };
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_ty = gcd_dvd_recursive_ty(d, divisor);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let remainder = d.modulo(n, divisor);
        let positive = d.zero_lt_succ(predecessor);
        let decrease = d.lemma(p.mod_lt, &[n, divisor, positive]);
        let at_remainder = d.apply(recursive, &[remainder, decrease]);
        let recursive_pair = d.apply(at_remainder, &[divisor]);
        let recursive_common = d.gcd(remainder, divisor);
        let recursive_left_ty = d.dvd(recursive_common, remainder);
        let recursive_right_ty = d.dvd(recursive_common, divisor);
        let recursive_left = and_left(d, recursive_left_ty, recursive_right_ty, recursive_pair);
        let recursive_right = and_right(d, recursive_left_ty, recursive_right_ty, recursive_pair);
        let remainder_iff = d.lemma(
            p.dvd_mod_iff,
            &[recursive_common, predecessor, n, recursive_right],
        );
        let recursive_divides_n_ty = d.dvd(recursive_common, n);
        let remainder_forward =
            iff_forward(d, recursive_left_ty, recursive_divides_n_ty, remainder_iff);
        let recursive_divides_n = d.apply(remainder_forward, &[recursive_left]);
        let common = d.gcd(divisor, n);
        let equation = d.lemma(p.gcd_succ, &[predecessor, n]);
        let recursive_to_common = d.symm(common, recursive_common, equation);
        let common_divides_divisor = transport_dvd_left(
            d,
            recursive_common,
            common,
            recursive_to_common,
            divisor,
            recursive_right,
        );
        let common_divides_n = transport_dvd_left(
            d,
            recursive_common,
            common,
            recursive_to_common,
            n,
            recursive_divides_n,
        );
        let left_ty = d.dvd(common, divisor);
        let right_ty = d.dvd(common, n);
        let pair = d.const_app(
            p.logic.and_intro,
            &[left_ty, right_ty, common_divides_divisor, common_divides_n],
        );
        let with_n = d.lam_fv(n_fv, nat, pair);
        let with_recursive = d.lam_fv(recursive_fv, recursive_ty, with_n);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };
    let gcd_dvd_step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_ty = gcd_dvd_recursive_ty(d, m);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let selected = d.apply(
            rec,
            &[
                gcd_dvd_step_motive,
                gcd_dvd_zero_minor,
                gcd_dvd_succ_minor,
                m,
            ],
        );
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_ty, body);
        d.lam_fv(m_fv, nat, with_recursive)
    };
    let gcd_dvd_fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let gcd_dvd_all = d.apply(
        gcd_dvd_fix,
        &[nat, relation, gcd_dvd_family, well_founded, gcd_dvd_step],
    );
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let gcd_dvd_value = d.apply(gcd_dvd_all, &[m, n]);
    let gcd_dvd_body_ty = gcd_dvd_at(d, m, n);
    let gcd_dvd_decl_ty = {
        let with_n = d.pi_fv(n_fv, nat, gcd_dvd_body_ty);
        d.pi_fv(m_fv, nat, with_n)
    };
    let gcd_dvd_decl_value = {
        let with_n = d.lam_fv(n_fv, nat, gcd_dvd_value);
        d.lam_fv(m_fv, nat, with_n)
    };
    d.declare_theorem(p.gcd_dvd, gcd_dvd_decl_ty, gcd_dvd_decl_value)?;

    d.theorem(p.gcd_dvd_left, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let left_ty = d.dvd(common, m);
        let right_ty = d.dvd(common, n);
        let pair = d.lemma(p.gcd_dvd, &[m, n]);
        (left_ty, and_left(d, left_ty, right_ty, pair))
    })?;
    d.theorem(p.gcd_dvd_right, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let left_ty = d.dvd(common, m);
        let right_ty = d.dvd(common, n);
        let pair = d.lemma(p.gcd_dvd, &[m, n]);
        (right_ty, and_right(d, left_ty, right_ty, pair))
    })?;

    declare_dvd_gcd_semantics(d, &p, nat, relation, well_founded, one, zero_level)?;
    Ok(())
}

/// The relation, motive, well-foundedness witness, and Euclidean step shared by
/// `Nat.gcd` and its checked unfolding equations.
fn gcd_fix_parts(d: &mut NatDev<'_>, p: &NatPrelude) -> (ExprId, ExprId, ExprId, ExprId) {
    let nat = d.nat_ty();
    let one = d.level_one();
    let relation = d.kernel().const_(p.lt, vec![]);
    let nat_to_nat = d.arrow(nat, nat);
    let family = {
        let value_fv = d.fresh_fvar();
        d.lam_fv(value_fv, nat, nat_to_nat)
    };
    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let related_fv = d.fresh_fvar();
        let related_ty = d.lt(predecessor, upper);
        let at_relation = d.pi_fv(related_fv, related_ty, nat_to_nat);
        d.pi_fv(predecessor_fv, nat, at_relation)
    };
    let motive = {
        let upper_fv = d.fresh_fvar();
        let upper = d.kernel().fvar(upper_fv);
        let recursive = recursive_ty(d, upper);
        let result = d.arrow(recursive, nat_to_nat);
        d.lam_fv(upper_fv, nat, result)
    };
    let zero_minor = {
        let recursive_fv = d.fresh_fvar();
        let zero = d.zero();
        let recursive = recursive_ty(d, zero);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let identity = d.lam_fv(value_fv, nat, value);
        d.lam_fv(recursive_fv, recursive, identity)
    };
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ih_fv = d.fresh_fvar();
        let ih_ty = {
            let recursive = recursive_ty(d, predecessor);
            d.arrow(recursive, nat_to_nat)
        };
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_at_divisor = recursive_ty(d, divisor);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let remainder = d.modulo(value, divisor);
        let positive = d.zero_lt_succ(predecessor);
        let decrease = d.lemma(p.mod_lt, &[value, divisor, positive]);
        let recursive_gcd = d.apply(recursive, &[remainder, decrease]);
        let body = d.apply(recursive_gcd, &[divisor]);
        let with_value = d.lam_fv(value_fv, nat, body);
        let with_recursive = d.lam_fv(recursive_fv, recursive_at_divisor, with_value);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };
    let step = {
        let upper_fv = d.fresh_fvar();
        let upper = d.kernel().fvar(upper_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, upper);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let selected = d.apply(rec, &[motive, zero_minor, succ_minor, upper]);
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, body);
        d.lam_fv(upper_fv, nat, with_recursive)
    };
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    (relation, family, well_founded, step)
}

#[allow(clippy::too_many_arguments)]
fn declare_dvd_gcd_semantics(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    relation: ExprId,
    well_founded: ExprId,
    one: LevelId,
    zero_level: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    let dvd_gcd_target = |d: &mut NatDev<'_>, m: ExprId, n: ExprId, k: ExprId| {
        let common = d.gcd(m, n);
        let divides_m = d.dvd(k, m);
        let divides_n = d.dvd(k, n);
        let divides_common = d.dvd(k, common);
        let n_to_common = d.arrow(divides_n, divides_common);
        d.arrow(divides_m, n_to_common)
    };
    let dvd_gcd_row = |d: &mut NatDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = dvd_gcd_target(d, m, n, k);
        let with_k = d.pi_fv(k_fv, nat, body);
        d.pi_fv(n_fv, nat, with_k)
    };
    let family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let row = dvd_gcd_row(d, m);
        d.lam_fv(m_fv, nat, row)
    };
    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let related_fv = d.fresh_fvar();
        let related_ty = d.lt(predecessor, upper);
        let row = dvd_gcd_row(d, predecessor);
        let at_relation = d.pi_fv(related_fv, related_ty, row);
        d.pi_fv(predecessor_fv, nat, at_relation)
    };
    let step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = recursive_ty(d, m);
        let row = dvd_gcd_row(d, m);
        let body = d.arrow(recursive, row);
        d.lam_fv(m_fv, nat, body)
    };
    let zero_minor = {
        let zero = d.zero();
        let recursive_fv = d.fresh_fvar();
        let recursive = recursive_ty(d, zero);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let divides_zero_ty = d.dvd(k, zero);
        let divides_zero_fv = d.fresh_fvar();
        let divides_n_ty = d.dvd(k, n);
        let divides_n_fv = d.fresh_fvar();
        let divides_n = d.kernel().fvar(divides_n_fv);
        let common = d.gcd(zero, n);
        let equation = d.lemma(p.gcd_zero_left, &[n]);
        let n_to_common = d.symm(common, n, equation);
        let body = transport_dvd_right(d, k, n, common, n_to_common, divides_n);
        let with_divides_n = d.lam_fv(divides_n_fv, divides_n_ty, body);
        let with_divides_zero = d.lam_fv(divides_zero_fv, divides_zero_ty, with_divides_n);
        let with_k = d.lam_fv(k_fv, nat, with_divides_zero);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        d.lam_fv(recursive_fv, recursive, with_n)
    };
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ih_fv = d.fresh_fvar();
        let ih_ty = {
            let recursive = recursive_ty(d, predecessor);
            let row = dvd_gcd_row(d, predecessor);
            d.arrow(recursive, row)
        };
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, divisor);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let divides_divisor_ty = d.dvd(k, divisor);
        let divides_divisor_fv = d.fresh_fvar();
        let divides_divisor = d.kernel().fvar(divides_divisor_fv);
        let divides_n_ty = d.dvd(k, n);
        let divides_n_fv = d.fresh_fvar();
        let divides_n = d.kernel().fvar(divides_n_fv);
        let remainder = d.modulo(n, divisor);
        let divides_remainder_ty = d.dvd(k, remainder);
        let remainder_iff = d.lemma(p.dvd_mod_iff, &[k, predecessor, n, divides_divisor]);
        let dividend_to_remainder =
            iff_reverse(d, divides_remainder_ty, divides_n_ty, remainder_iff);
        let divides_remainder = d.apply(dividend_to_remainder, &[divides_n]);
        let positive = d.zero_lt_succ(predecessor);
        let decrease = d.lemma(p.mod_lt, &[n, divisor, positive]);
        let at_remainder = d.apply(recursive, &[remainder, decrease]);
        let at_divisor = d.apply(at_remainder, &[divisor]);
        let at_k = d.apply(at_divisor, &[k]);
        let recursive_proof = d.apply(at_k, &[divides_remainder, divides_divisor]);
        let recursive_common = d.gcd(remainder, divisor);
        let common = d.gcd(divisor, n);
        let equation = d.lemma(p.gcd_succ, &[predecessor, n]);
        let recursive_to_common = d.symm(common, recursive_common, equation);
        let body = transport_dvd_right(
            d,
            k,
            recursive_common,
            common,
            recursive_to_common,
            recursive_proof,
        );
        let with_divides_n = d.lam_fv(divides_n_fv, divides_n_ty, body);
        let with_divides_divisor = d.lam_fv(divides_divisor_fv, divides_divisor_ty, with_divides_n);
        let with_k = d.lam_fv(k_fv, nat, with_divides_divisor);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, with_n);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };
    let step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, m);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let selected = d.apply(rec, &[step_motive, zero_minor, succ_minor, m]);
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, body);
        d.lam_fv(m_fv, nat, with_recursive)
    };
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let all = d.apply(fix, &[nat, relation, family, well_founded, step]);
    d.theorem(p.dvd_gcd, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let proof = d.apply(all, &[m, n, k]);
        (dvd_gcd_target(d, m, n, k), proof)
    })?;

    d.theorem(p.dvd_gcd_iff, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let common = d.gcd(m, n);
        let divides_common_ty = d.dvd(k, common);
        let divides_m_ty = d.dvd(k, m);
        let divides_n_ty = d.dvd(k, n);
        let pair_ty = d.const_app(p.logic.and, &[divides_m_ty, divides_n_ty]);
        let forward = {
            let proof_fv = d.fresh_fvar();
            let proof = d.kernel().fvar(proof_fv);
            let common_divides_m = d.lemma(p.gcd_dvd_left, &[m, n]);
            let common_divides_n = d.lemma(p.gcd_dvd_right, &[m, n]);
            let divides_m = d.lemma(p.dvd_trans, &[k, common, m, proof, common_divides_m]);
            let divides_n = d.lemma(p.dvd_trans, &[k, common, n, proof, common_divides_n]);
            let pair = d.const_app(
                p.logic.and_intro,
                &[divides_m_ty, divides_n_ty, divides_m, divides_n],
            );
            d.lam_fv(proof_fv, divides_common_ty, pair)
        };
        let reverse = {
            let pair_fv = d.fresh_fvar();
            let pair = d.kernel().fvar(pair_fv);
            let divides_m = and_left(d, divides_m_ty, divides_n_ty, pair);
            let divides_n = and_right(d, divides_m_ty, divides_n_ty, pair);
            let body = d.lemma(p.dvd_gcd, &[k, m, n, divides_m, divides_n]);
            d.lam_fv(pair_fv, pair_ty, body)
        };
        let stmt = d.const_app(p.logic.iff, &[divides_common_ty, pair_ty]);
        let proof = d.const_app(
            p.logic.iff_intro,
            &[divides_common_ty, pair_ty, forward, reverse],
        );
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.ModEq.gcd_eq : ∀ m a b, modEq m a b → gcd a m = gcd b m`.
// ============================================================================

/// See [`NatPrelude::mod_eq_gcd_eq`] for the route. `modEq m a b` unfolds to
/// balanced witnesses `∃ u v, a + m*u = b + m*v`; eliminate both, then show
/// `gcd a m ∣ gcd b m` and its converse and close with `dvd_antisymm`.
///
/// Each divisibility direction is the same shape: `gcd a m` divides `a` and
/// `m` (`gcd_dvd_left`/`gcd_dvd_right`), hence `m*u` (`dvd_mul_right_of_dvd`)
/// and so `a + m*u` (`dvd_add`); transport along the witness equation to
/// `b + m*w`; reorder to `m*w + b` (`add_comm`) and peel `m*w`
/// (`dvd_add_iff_right`, reversed) to land on `gcd a m ∣ b`; finish with
/// `dvd_gcd`. The other direction is the mirror image over the symmetric
/// equation.
///
/// Requires [`declare_gcd_semantics`], [`super::modular::declare_modular_congruence`]
/// and `dvd_antisymm` (declared by `declare_dvd_antisymm`, which needs
/// `le_of_dvd` from `declare_primes` and so cannot run any earlier) to have
/// already run.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_modeq_gcd_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    d.theorem(p.mod_eq_gcd_eq, 3, &|d, v| {
        let (m, a, b) = (v[0], v[1], v[2]);
        let source = d.mod_eq(m, a, b);
        let ga = d.gcd(a, m);
        let gb = d.gcd(b, m);
        let target = d.eq(ga, gb);

        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);

        let outer_predicate = d.mod_eq_outer_predicate(m, a, b);
        let outer_motive = d
            .kernel()
            .lam(anon, source, target, crate::BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(m, a, b, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(m, a, b, u);
            let inner_motive =
                d.kernel()
                    .lam(anon, inner_source, target, crate::BinderInfo::Default);
            let inner_minor = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let mu = d.mul(m, u);
                let mw = d.mul(m, w);
                let left_sum = d.mod_eq_sum(m, a, u); // a + m*u
                let right_sum = d.mod_eq_sum(m, b, w); // b + m*w
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);

                // gcd a m ∣ gcd b m.
                let ga_dvd_a = d.lemma(p.gcd_dvd_left, &[a, m]);
                let ga_dvd_m = d.lemma(p.gcd_dvd_right, &[a, m]);
                let ga_dvd_mu = d.lemma(p.dvd_mul_right_of_dvd, &[ga, m, u, ga_dvd_m]);
                let ga_dvd_left_sum = d.lemma(p.dvd_add, &[ga, a, mu, ga_dvd_a, ga_dvd_mu]);
                let ga_dvd_right_sum =
                    transport_dvd_right(d, ga, left_sum, right_sum, equation, ga_dvd_left_sum);
                let ga_dvd_mw = d.lemma(p.dvd_mul_right_of_dvd, &[ga, m, w, ga_dvd_m]);
                let reorder_a = d.lemma(p.add_comm, &[b, mw]); // Eq (b+mw) (mw+b)
                let mw_b = d.add(mw, b);
                let ga_dvd_mw_b =
                    transport_dvd_right(d, ga, right_sum, mw_b, reorder_a, ga_dvd_right_sum);
                let split_a = d.lemma(p.dvd_add_iff_right, &[ga, mw, b, ga_dvd_mw]);
                let ga_dvd_b_ty = d.dvd(ga, b);
                let ga_dvd_mw_b_ty = d.dvd(ga, mw_b);
                let ga_dvd_b = {
                    let f = iff_reverse(d, ga_dvd_b_ty, ga_dvd_mw_b_ty, split_a);
                    d.apply(f, &[ga_dvd_mw_b])
                };
                let ga_dvd_gb = d.lemma(p.dvd_gcd, &[ga, b, m, ga_dvd_b, ga_dvd_m]);

                // gcd b m ∣ gcd a m, over the symmetric witness equation.
                let equation_rev = d.symm(left_sum, right_sum, equation);
                let gb_dvd_b = d.lemma(p.gcd_dvd_left, &[b, m]);
                let gb_dvd_m = d.lemma(p.gcd_dvd_right, &[b, m]);
                let gb_dvd_mw = d.lemma(p.dvd_mul_right_of_dvd, &[gb, m, w, gb_dvd_m]);
                let gb_dvd_right_sum = d.lemma(p.dvd_add, &[gb, b, mw, gb_dvd_b, gb_dvd_mw]);
                let gb_dvd_left_sum =
                    transport_dvd_right(d, gb, right_sum, left_sum, equation_rev, gb_dvd_right_sum);
                let gb_dvd_mu = d.lemma(p.dvd_mul_right_of_dvd, &[gb, m, u, gb_dvd_m]);
                let reorder_b = d.lemma(p.add_comm, &[a, mu]); // Eq (a+mu) (mu+a)
                let mu_a = d.add(mu, a);
                let gb_dvd_mu_a =
                    transport_dvd_right(d, gb, left_sum, mu_a, reorder_b, gb_dvd_left_sum);
                let split_b = d.lemma(p.dvd_add_iff_right, &[gb, mu, a, gb_dvd_mu]);
                let gb_dvd_a_ty = d.dvd(gb, a);
                let gb_dvd_mu_a_ty = d.dvd(gb, mu_a);
                let gb_dvd_a = {
                    let f = iff_reverse(d, gb_dvd_a_ty, gb_dvd_mu_a_ty, split_b);
                    d.apply(f, &[gb_dvd_mu_a])
                };
                let gb_dvd_ga = d.lemma(p.dvd_gcd, &[gb, a, m, gb_dvd_a, gb_dvd_m]);

                let heq = d.lemma(p.dvd_antisymm, &[ga, gb, ga_dvd_gb, gb_dvd_ga]);

                let with_equation = d.lam_fv(equation_fv, equation_ty, heq);
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
    Ok(())
}

fn gcd_fix_equation(d: &mut NatDev<'_>, p: &NatPrelude, value: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let (relation, family, well_founded, step) = gcd_fix_parts(d, p);
    let fix_eq = d
        .kernel()
        .const_(p.logic.well_founded_fix_eq, vec![one, one]);
    d.apply(fix_eq, &[nat, relation, family, well_founded, step, value])
}
