//! Bezout's identity for the executable gcd, over balanced natural parts.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

fn bezout_after_np_exists<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    mp: ExprId,
    mn: ExprId,
    np: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);
    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

pub(super) fn bezout_tail_exists<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    mp: ExprId,
    mn: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let body = bezout_after_np_exists(d, m, n, g, mp, mn, np);
    let predicate = d.lam_fv(np_fv, nat, body);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

pub(super) fn bezout_after_mp_exists<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    mp: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let body = bezout_tail_exists(d, m, n, g, mp, mn);
    let predicate = d.lam_fv(mn_fv, nat, body);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

fn bezout_mp_predicate<D: NatOps>(d: &mut D, m: ExprId, n: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let body = bezout_after_mp_exists(d, m, n, g, mp);
    d.lam_fv(mp_fv, nat, body)
}

fn left_sum(d: &mut NatDev<'_>, terms: &[ExprId]) -> ExprId {
    let mut sum = terms[0];
    for &term in &terms[1..] {
        sum = d.add(sum, term);
    }
    sum
}

fn lift_sum_equality(
    d: &mut NatDev<'_>,
    mut left: ExprId,
    mut right: ExprId,
    mut proof: ExprId,
    suffix: &[ExprId],
) -> (ExprId, ExprId, ExprId) {
    for &term in suffix {
        proof = d.congr(left, right, proof, &|d, value| d.add(value, term));
        left = d.add(left, term);
        right = d.add(right, term);
    }
    (left, right, proof)
}

fn left_sum_adjacent_swap(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    terms: &[ExprId],
    index: usize,
) -> (Vec<ExprId>, ExprId) {
    let mut swapped = terms.to_vec();
    swapped.swap(index, index + 1);
    let (prefix_left, prefix_right, prefix_proof, suffix_start) = if index == 0 {
        let a = terms[0];
        let b = terms[1];
        (d.add(a, b), d.add(b, a), d.lemma(p.add_comm, &[a, b]), 2)
    } else {
        let prefix = left_sum(d, &terms[..index]);
        let a = terms[index];
        let b = terms[index + 1];
        let prefix_a = d.add(prefix, a);
        let prefix_b = d.add(prefix, b);
        (
            d.add(prefix_a, b),
            d.add(prefix_b, a),
            d.lemma(p.add_right_comm, &[prefix, a, b]),
            index + 2,
        )
    };
    let (_, _, proof) = lift_sum_equality(
        d,
        prefix_left,
        prefix_right,
        prefix_proof,
        &terms[suffix_start..],
    );
    (swapped, proof)
}

fn prove_left_sum_permutation(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    source: &[ExprId],
    target: &[ExprId],
) -> ExprId {
    let start = left_sum(d, source);
    let mut current = source.to_vec();
    let mut current_expr = start;
    let mut proof = d.refl(start);
    for index in 0..target.len() {
        let mut found = current[index..]
            .iter()
            .position(|item| *item == target[index])
            .expect("sum permutation target must contain the same atoms")
            + index;
        while found > index {
            let (next, swap) = left_sum_adjacent_swap(d, p, &current, found - 1);
            let next_expr = left_sum(d, &next);
            proof = d.trans(start, current_expr, next_expr, proof, swap);
            current = next;
            current_expr = next_expr;
            found -= 1;
        }
    }
    proof
}

fn prove_bezout_zero_equation(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let zero = d.zero();
    let unit = d.num(1);
    let left = {
        let zero_zero = d.mul(zero, zero);
        let n_zero = d.mul(n, zero);
        let first = d.add(n, zero_zero);
        d.add(first, n_zero)
    };
    let n_one = d.mul(n, unit);
    let right = {
        let zero_zero = d.mul(zero, zero);
        d.add(zero_zero, n_one)
    };
    let left_to_n = d.refl(n);
    let right_to_n_one = d.lemma(p.zero_add, &[n_one]);
    let n_one_to_n = d.lemma(p.mul_one, &[n]);
    let right_to_n = d.trans(right, n_one, n, right_to_n_one, n_one_to_n);
    let n_to_right = d.symm(right, n, right_to_n);
    d.trans(left, n, right, left_to_n, n_to_right)
}

#[allow(clippy::too_many_arguments)]
fn prove_bezout_euclidean_update(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    divisor: ExprId,
    dividend: ExprId,
    remainder: ExprId,
    quotient: ExprId,
    common: ExprId,
    mp: ExprId,
    mn: ExprId,
    np: ExprId,
    nn: ExprId,
    division_equation: ExprId,
    recursive_equation: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let qmp = d.mul(quotient, mp);
    let qmn = d.mul(quotient, mn);
    let new_mp = d.add(np, qmn);
    let new_mn = d.add(nn, qmp);
    let new_np = mp;
    let new_nn = mn;

    let dnn = d.mul(divisor, nn);
    let d_qmp = d.mul(divisor, qmp);
    let dq = d.mul(divisor, quotient);
    let dqmp = d.mul(dq, mp);
    let dqmn = d.mul(dq, mn);
    let rmn = d.mul(remainder, mn);
    let rmp = d.mul(remainder, mp);
    let dnp = d.mul(divisor, np);
    let nmn = d.mul(dividend, mn);
    let nmp = d.mul(dividend, mp);

    let lhs = {
        let d_new_mn = d.mul(divisor, new_mn);
        let first = d.add(common, d_new_mn);
        d.add(first, nmn)
    };
    let rhs = {
        let d_new_mp = d.mul(divisor, new_mp);
        d.add(d_new_mp, nmp)
    };

    let distributed_negative = d.add(dnn, d_qmp);
    let common_distributed_negative = d.add(common, distributed_negative);
    let lhs1 = d.add(common_distributed_negative, nmn);
    let distribute_negative = d.lemma(p.left_distrib, &[divisor, nn, qmp]);
    let d_new_mn = d.mul(divisor, new_mn);
    let lhs_h1 = d.congr(
        d_new_mn,
        distributed_negative,
        distribute_negative,
        &|d, value| {
            let first = d.add(common, value);
            d.add(first, nmn)
        },
    );
    let common_dnn = d.add(common, dnn);
    let lhs2_prefix = d.add(common_dnn, d_qmp);
    let lhs2 = d.add(lhs2_prefix, nmn);
    let reassociate_negative = d.lemma(p.add_assoc, &[common, dnn, d_qmp]);
    let reassociate_negative = d.symm(
        lhs2_prefix,
        common_distributed_negative,
        reassociate_negative,
    );
    let lhs_h2 = d.congr(
        common_distributed_negative,
        lhs2_prefix,
        reassociate_negative,
        &|d, value| d.add(value, nmn),
    );
    let d_qmp_to_dqmp = {
        let assoc = d.lemma(p.mul_assoc, &[divisor, quotient, mp]);
        d.symm(dqmp, d_qmp, assoc)
    };
    let lhs3_prefix = d.add(common_dnn, dqmp);
    let lhs3 = d.add(lhs3_prefix, nmn);
    let lhs_h3 = d.congr(d_qmp, dqmp, d_qmp_to_dqmp, &|d, value| {
        let prefix = d.add(common_dnn, value);
        d.add(prefix, nmn)
    });
    let dq_plus_r = d.add(dq, remainder);
    let nmn_to_expanded = {
        let replace_n = d.congr(dividend, dq_plus_r, division_equation, &|d, value| {
            d.mul(value, mn)
        });
        let distribute = d.lemma(p.right_distrib, &[dq, remainder, mn]);
        let expanded_product = d.mul(dq_plus_r, mn);
        let expanded_sum = d.add(dqmn, rmn);
        d.trans(nmn, expanded_product, expanded_sum, replace_n, distribute)
    };
    let expanded_nmn = d.add(dqmn, rmn);
    let lhs4 = d.add(lhs3_prefix, expanded_nmn);
    let lhs_h4 = d.congr(nmn, expanded_nmn, nmn_to_expanded, &|d, value| {
        d.add(lhs3_prefix, value)
    });
    let lhs_normal = left_sum(d, &[common, dnn, dqmp, dqmn, rmn]);
    let flatten_lhs = d.lemma(p.add_assoc, &[lhs3_prefix, dqmn, rmn]);
    let lhs_h5 = d.symm(lhs_normal, lhs4, flatten_lhs);
    let (_, lhs_to_normal) = d.chain(
        lhs,
        &[
            (lhs1, lhs_h1),
            (lhs2, lhs_h2),
            (lhs3, lhs_h3),
            (lhs4, lhs_h4),
            (lhs_normal, lhs_h5),
        ],
    );

    let left_canonical_terms = [common, rmn, dnn, dqmp, dqmn];
    let left_normal_terms = [common, dnn, dqmp, dqmn, rmn];
    let lhs_permutation =
        prove_left_sum_permutation(d, p, &left_normal_terms, &left_canonical_terms);
    let left_canonical = left_sum(d, &left_canonical_terms);

    let recursive_left = left_sum(d, &[common, rmn, dnn]);
    let recursive_right = left_sum(d, &[rmp, dnp]);
    let (_, right_canonical, lifted_recursive) = lift_sum_equality(
        d,
        recursive_left,
        recursive_right,
        recursive_equation,
        &[dqmp, dqmn],
    );

    let d_qmn = d.mul(divisor, qmn);
    let distributed_positive = d.add(dnp, d_qmn);
    let rhs1 = d.add(distributed_positive, nmp);
    let distribute_positive = d.lemma(p.left_distrib, &[divisor, np, qmn]);
    let d_new_mp = d.mul(divisor, new_mp);
    let rhs_h1 = d.congr(
        d_new_mp,
        distributed_positive,
        distribute_positive,
        &|d, value| d.add(value, nmp),
    );
    let d_qmn_to_dqmn = {
        let assoc = d.lemma(p.mul_assoc, &[divisor, quotient, mn]);
        d.symm(dqmn, d_qmn, assoc)
    };
    let rhs2_left = d.add(dnp, dqmn);
    let rhs2 = d.add(rhs2_left, nmp);
    let rhs_h2 = d.congr(d_qmn, dqmn, d_qmn_to_dqmn, &|d, value| {
        let left = d.add(dnp, value);
        d.add(left, nmp)
    });
    let nmp_to_expanded = {
        let replace_n = d.congr(dividend, dq_plus_r, division_equation, &|d, value| {
            d.mul(value, mp)
        });
        let distribute = d.lemma(p.right_distrib, &[dq, remainder, mp]);
        let expanded_product = d.mul(dq_plus_r, mp);
        let expanded_sum = d.add(dqmp, rmp);
        d.trans(nmp, expanded_product, expanded_sum, replace_n, distribute)
    };
    let expanded_nmp = d.add(dqmp, rmp);
    let rhs3 = d.add(rhs2_left, expanded_nmp);
    let rhs_h3 = d.congr(nmp, expanded_nmp, nmp_to_expanded, &|d, value| {
        d.add(rhs2_left, value)
    });
    let rhs_normal_terms = [dnp, dqmn, dqmp, rmp];
    let rhs_normal = left_sum(d, &rhs_normal_terms);
    let flatten_rhs = d.lemma(p.add_assoc, &[rhs2_left, dqmp, rmp]);
    let rhs_h4 = d.symm(rhs_normal, rhs3, flatten_rhs);
    let (_, rhs_to_normal) = d.chain(
        rhs,
        &[
            (rhs1, rhs_h1),
            (rhs2, rhs_h2),
            (rhs3, rhs_h3),
            (rhs_normal, rhs_h4),
        ],
    );
    let right_canonical_terms = [rmp, dnp, dqmp, dqmn];
    let rhs_permutation =
        prove_left_sum_permutation(d, p, &rhs_normal_terms, &right_canonical_terms);
    debug_assert_eq!(right_canonical, left_sum(d, &right_canonical_terms));

    let normal_to_left_canonical = d.trans(
        lhs,
        lhs_normal,
        left_canonical,
        lhs_to_normal,
        lhs_permutation,
    );
    let through_recursive = d.trans(
        lhs,
        left_canonical,
        right_canonical,
        normal_to_left_canonical,
        lifted_recursive,
    );
    let normal_to_canonical_rhs = rhs_permutation;
    let canonical_to_normal_rhs = d.symm(rhs_normal, right_canonical, normal_to_canonical_rhs);
    let through_rhs_normal = d.trans(
        lhs,
        right_canonical,
        rhs_normal,
        through_recursive,
        canonical_to_normal_rhs,
    );
    let normal_to_rhs = d.symm(rhs, rhs_normal, rhs_to_normal);
    let proof = d.trans(lhs, rhs_normal, rhs, through_rhs_normal, normal_to_rhs);
    (new_mp, new_mn, new_np, new_nn, proof)
}

#[allow(clippy::too_many_arguments)]
fn eliminate_bezout(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    source: ExprId,
    target: ExprId,
    build: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let rec_name = d.prelude().logic.exists_rec;
    let outer_predicate = bezout_mp_predicate(d, m, n, g);
    let outer_motive_fv = d.fresh_fvar();
    let outer_ty = d.bezout_witnesses(m, n, g);
    let outer_motive = d.lam_fv(outer_motive_fv, outer_ty, target);
    let outer_minor = {
        let mp_fv = d.fresh_fvar();
        let mp = d.kernel().fvar(mp_fv);
        let after_mp_ty = bezout_after_mp_exists(d, m, n, g, mp);
        let after_mp_fv = d.fresh_fvar();
        let after_mp = d.kernel().fvar(after_mp_fv);
        let after_mp_motive_fv = d.fresh_fvar();
        let after_mp_motive = d.lam_fv(after_mp_motive_fv, after_mp_ty, target);
        let after_mp_minor = {
            let mn_fv = d.fresh_fvar();
            let mn = d.kernel().fvar(mn_fv);
            let tail_ty = bezout_tail_exists(d, m, n, g, mp, mn);
            let tail_fv = d.fresh_fvar();
            let tail = d.kernel().fvar(tail_fv);
            let tail_motive_fv = d.fresh_fvar();
            let tail_motive = d.lam_fv(tail_motive_fv, tail_ty, target);
            let tail_minor = {
                let np_fv = d.fresh_fvar();
                let np = d.kernel().fvar(np_fv);
                let nn_exists_ty = bezout_after_np_exists(d, m, n, g, mp, mn, np);
                let nn_exists_fv = d.fresh_fvar();
                let nn_exists = d.kernel().fvar(nn_exists_fv);
                let nn_motive_fv = d.fresh_fvar();
                let nn_motive = d.lam_fv(nn_motive_fv, nn_exists_ty, target);
                let nn_minor = {
                    let nn_fv = d.fresh_fvar();
                    let nn = d.kernel().fvar(nn_fv);
                    let equation_ty = d.bezout_equation(m, n, g, mp, mn, np, nn);
                    let equation_fv = d.fresh_fvar();
                    let equation = d.kernel().fvar(equation_fv);
                    let body = build(d, mp, mn, np, nn, equation);
                    let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                    d.lam_fv(nn_fv, nat, with_equation)
                };
                let nn_predicate = {
                    let nn_fv = d.fresh_fvar();
                    let nn = d.kernel().fvar(nn_fv);
                    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
                    d.lam_fv(nn_fv, nat, equation)
                };
                let rec = d.kernel().const_(rec_name, vec![one]);
                let body = d.apply(rec, &[nat, nn_predicate, nn_motive, nn_minor, nn_exists]);
                let with_exists = d.lam_fv(nn_exists_fv, nn_exists_ty, body);
                d.lam_fv(np_fv, nat, with_exists)
            };
            let np_predicate = {
                let np_fv = d.fresh_fvar();
                let np = d.kernel().fvar(np_fv);
                let body = bezout_after_np_exists(d, m, n, g, mp, mn, np);
                d.lam_fv(np_fv, nat, body)
            };
            let rec = d.kernel().const_(rec_name, vec![one]);
            let body = d.apply(rec, &[nat, np_predicate, tail_motive, tail_minor, tail]);
            let with_tail = d.lam_fv(tail_fv, tail_ty, body);
            d.lam_fv(mn_fv, nat, with_tail)
        };
        let mn_predicate = {
            let mn_fv = d.fresh_fvar();
            let mn = d.kernel().fvar(mn_fv);
            let body = bezout_tail_exists(d, m, n, g, mp, mn);
            d.lam_fv(mn_fv, nat, body)
        };
        let rec = d.kernel().const_(rec_name, vec![one]);
        let body = d.apply(
            rec,
            &[nat, mn_predicate, after_mp_motive, after_mp_minor, after_mp],
        );
        let with_after_mp = d.lam_fv(after_mp_fv, after_mp_ty, body);
        d.lam_fv(mp_fv, nat, with_after_mp)
    };
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(
        rec,
        &[nat, outer_predicate, outer_motive, outer_minor, source],
    )
}

/// Constructive, all-natural Bézout identity for the executable Euclidean gcd.
/// Four naturals encode the positive and negative parts of the two signed
/// coefficients, preserving the zero-axiom Nat lane while retaining the full
/// mathematical content needed by later Gauss and reconstruction theorems.
pub(super) fn declare_gcd_bezout(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let anon = d.anon_name();
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();

    // bezout m n g := ∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let body = d.bezout_witnesses(m, n, g);
        let with_g = d.lam_fv(g_fv, nat, body);
        let with_n = d.lam_fv(n_fv, nat, with_g);
        let value = d.lam_fv(m_fv, nat, with_n);
        let g_ty = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        let n_ty = d.kernel().pi(anon, nat, g_ty, BinderInfo::Default);
        let ty = d.kernel().pi(anon, nat, n_ty, BinderInfo::Default);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.bezout,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(12),
        })?;
    }

    let row = |d: &mut NatDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let common = d.gcd(m, n);
        let target = d.bezout(m, n, common);
        d.pi_fv(n_fv, nat, target)
    };
    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let lower_fv = d.fresh_fvar();
        let lower = d.kernel().fvar(lower_fv);
        let related_fv = d.fresh_fvar();
        let related = d.lt(lower, upper);
        let lower_row = row(d, lower);
        let body = d.pi_fv(related_fv, related, lower_row);
        d.pi_fv(lower_fv, nat, body)
    };
    let family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = row(d, m);
        d.lam_fv(m_fv, nat, body)
    };
    let step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = recursive_ty(d, m);
        let result = row(d, m);
        let body = d.arrow(recursive, result);
        d.lam_fv(m_fv, nat, body)
    };
    let zero_minor = {
        let zero = d.zero();
        let recursive_fv = d.fresh_fvar();
        let recursive = recursive_ty(d, zero);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let unit = d.num(1);
        let base_equation = prove_bezout_zero_equation(d, &p, n);
        let base = d.bezout_intro(zero, n, n, zero, zero, unit, zero, base_equation);
        let common = d.gcd(zero, n);
        let common_eq_n = d.lemma(p.gcd_zero_left, &[n]);
        let n_eq_common = d.symm(common, n, common_eq_n);
        let motive = d.eq_motive(n, &|d, value| d.bezout(zero, n, value));
        let body = d.transport(n, motive, base, common, n_eq_common);
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(recursive_fv, recursive, with_n)
    };
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ignored_ih_fv = d.fresh_fvar();
        let predecessor_recursive = recursive_ty(d, predecessor);
        let predecessor_row = row(d, predecessor);
        let ignored_ih_ty = d.arrow(predecessor_recursive, predecessor_row);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, divisor);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let remainder = d.modulo(n, divisor);
        let quotient = d.div(n, divisor);
        let decrease = d.lemma(p.mod_lt, &[predecessor, n]);
        let recursive_row = d.apply(recursive, &[remainder, decrease]);
        let recursive_proof = d.apply(recursive_row, &[divisor]);
        let recursive_common = d.gcd(remainder, divisor);
        let target_common = d.gcd(divisor, n);
        let recursive_target = d.bezout(divisor, n, recursive_common);
        let division_relation = d.lemma(p.div_mod_exec, &[predecessor, n]);
        let division_equation_ty = {
            let product = d.mul(divisor, quotient);
            let reconstructed = d.add(product, remainder);
            d.eq(n, reconstructed)
        };
        let division_bound_ty = d.lt(remainder, divisor);
        let division_equation = and_left(
            d,
            division_equation_ty,
            division_bound_ty,
            division_relation,
        );
        let transformed = eliminate_bezout(
            d,
            remainder,
            divisor,
            recursive_common,
            recursive_proof,
            recursive_target,
            &|d, mp, mn, np, nn, equation| {
                let (new_mp, new_mn, new_np, new_nn, proof) = prove_bezout_euclidean_update(
                    d,
                    &p,
                    divisor,
                    n,
                    remainder,
                    quotient,
                    recursive_common,
                    mp,
                    mn,
                    np,
                    nn,
                    division_equation,
                    equation,
                );
                d.bezout_intro(
                    divisor,
                    n,
                    recursive_common,
                    new_mp,
                    new_mn,
                    new_np,
                    new_nn,
                    proof,
                )
            },
        );
        let target_eq_recursive = d.lemma(p.gcd_succ, &[predecessor, n]);
        let recursive_eq_target = d.symm(target_common, recursive_common, target_eq_recursive);
        let motive = d.eq_motive(recursive_common, &|d, value| d.bezout(divisor, n, value));
        let body = d.transport(
            recursive_common,
            motive,
            transformed,
            target_common,
            recursive_eq_target,
        );
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, with_n);
        let with_ignored_ih = d.lam_fv(ignored_ih_fv, ignored_ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ignored_ih)
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
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let all = d.apply(fix, &[nat, relation, family, well_founded, step]);
    d.theorem(p.gcd_bezout, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let target = d.bezout(m, n, common);
        (target, d.apply(all, &[m, n]))
    })?;
    Ok(())
}
