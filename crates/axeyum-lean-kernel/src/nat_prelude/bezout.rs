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

/// `g * ((1 + a·mn) + b·nn) = (g + (g·a)·mn) + (g·b)·nn`.
fn expand_scaled_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    a: ExprId,
    b: ExprId,
    mn: ExprId,
    nn: ExprId,
) -> ExprId {
    let p = *p;
    let unit = d.num(1);
    let a_mn = d.mul(a, mn);
    let b_nn = d.mul(b, nn);
    let head = d.add(unit, a_mn);
    let whole = d.add(head, b_nn);

    // g*(head + b·nn) = g*head + g*(b·nn)
    let step_outer = d.lemma(p.left_distrib, &[g, head, b_nn]);
    let g_head = d.mul(g, head);
    let g_b_nn = d.mul(g, b_nn);
    let split = d.add(g_head, g_b_nn);

    // g*head = g*1 + g*(a·mn) = g + (g·a)·mn
    let g_unit = d.mul(g, unit);
    let g_a_mn = d.mul(g, a_mn);
    let inner_split = d.add(g_unit, g_a_mn);
    let step_inner = d.lemma(p.left_distrib, &[g, unit, a_mn]);
    let mul_one = d.lemma(p.mul_one, &[g]);
    let with_g = d.add(g, g_a_mn);
    let step_unit = d.congr(g_unit, g, mul_one, &|d, x| d.add(x, g_a_mn));
    let scaled_a = d.mul(g, a);
    let scaled_a_mn = d.mul(scaled_a, mn);
    let assoc = d.lemma(p.mul_assoc, &[g, a, mn]);
    let step_assoc = {
        let flipped = d.symm(scaled_a_mn, g_a_mn, assoc);
        d.congr(g_a_mn, scaled_a_mn, flipped, &|d, x| d.add(g, x))
    };
    let head_target = d.add(g, scaled_a_mn);
    let (_reached, head_chain) = d.chain(
        g_head,
        &[
            (inner_split, step_inner),
            (with_g, step_unit),
            (head_target, step_assoc),
        ],
    );

    // g*(b·nn) = (g·b)·nn
    let scaled_b = d.mul(g, b);
    let scaled_b_nn = d.mul(scaled_b, nn);
    let assoc_b = d.lemma(p.mul_assoc, &[g, b, nn]);
    let tail_chain = d.symm(scaled_b_nn, g_b_nn, assoc_b);

    let after_head = d.add(head_target, g_b_nn);
    let final_target = d.add(head_target, scaled_b_nn);
    let step_head = d.congr(g_head, head_target, head_chain, &|d, x| d.add(x, g_b_nn));
    let step_tail = d.congr(g_b_nn, scaled_b_nn, tail_chain, &|d, x| {
        d.add(head_target, x)
    });
    let g_whole = d.mul(g, whole);
    let (_end, chained) = d.chain(
        g_whole,
        &[
            (split, step_outer),
            (after_head, step_head),
            (final_target, step_tail),
        ],
    );
    chained
}

/// `g * (a·mp + b·np) = (g·a)·mp + (g·b)·np`.
fn expand_scaled_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    a: ExprId,
    b: ExprId,
    mp: ExprId,
    np: ExprId,
) -> ExprId {
    let p = *p;
    let a_mp = d.mul(a, mp);
    let b_np = d.mul(b, np);
    let whole = d.add(a_mp, b_np);
    let g_whole = d.mul(g, whole);
    let g_a_mp = d.mul(g, a_mp);
    let g_b_np = d.mul(g, b_np);
    let split = d.add(g_a_mp, g_b_np);
    let step_outer = d.lemma(p.left_distrib, &[g, a_mp, b_np]);

    let scaled_a = d.mul(g, a);
    let scaled_a_mp = d.mul(scaled_a, mp);
    let assoc_a = d.lemma(p.mul_assoc, &[g, a, mp]);
    let step_a = {
        let flipped = d.symm(scaled_a_mp, g_a_mp, assoc_a);
        d.congr(g_a_mp, scaled_a_mp, flipped, &|d, x| d.add(x, g_b_np))
    };
    let after_a = d.add(scaled_a_mp, g_b_np);

    let scaled_b = d.mul(g, b);
    let scaled_b_np = d.mul(scaled_b, np);
    let assoc_b = d.lemma(p.mul_assoc, &[g, b, np]);
    let step_b = {
        let flipped = d.symm(scaled_b_np, g_b_np, assoc_b);
        d.congr(g_b_np, scaled_b_np, flipped, &|d, x| d.add(scaled_a_mp, x))
    };
    let final_target = d.add(scaled_a_mp, scaled_b_np);

    let (_end, chained) = d.chain(
        g_whole,
        &[
            (split, step_outer),
            (after_a, step_a),
            (final_target, step_b),
        ],
    );
    chained
}

/// Eliminate a balanced Bézout certificate into `target`.
///
/// `minor` receives the four witnesses `(mp, mn, np, nn)` and a proof of
/// [`NatOps::bezout_equation`] for them, and must produce `target`.
///
/// The four nested predicates are rebuilt here **in the same order and from the
/// same `bezout_equation`** that [`NatOps::bezout_witnesses`] uses, so the
/// eliminator cannot drift from the introduction form. A first attempt peeled
/// the existentials with a hand-rolled recursion whose intermediate predicates
/// did not match, which is why this lives beside the builder instead.
pub(super) fn bezout_elim<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    target: ExprId,
    certificate: ExprId,
    minor: &dyn Fn(&mut D, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.prelude().logic.exists_;
    let rec_name = d.prelude().logic.exists_rec;

    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);

    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let nn_predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let nn_exists = d.apply(exists, &[nat, nn_predicate]);
    let np_predicate = d.lam_fv(np_fv, nat, nn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let np_exists = d.apply(exists, &[nat, np_predicate]);
    let mn_predicate = d.lam_fv(mn_fv, nat, np_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mn_exists = d.apply(exists, &[nat, mn_predicate]);
    let mp_predicate = d.lam_fv(mp_fv, nat, mn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mp_exists = d.apply(exists, &[nat, mp_predicate]);

    // Innermost: consume the equation itself.
    let equation_fv = d.fresh_fvar();
    let equation_proof = d.kernel().fvar(equation_fv);
    let core = minor(d, mp, mn, np, nn, equation_proof);
    let nn_minor = {
        let with_equation = d.lam_fv(equation_fv, equation, core);
        d.lam_fv(nn_fv, nat, with_equation)
    };

    let np_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, nn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, nn_predicate, motive, nn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, nn_exists, eliminated);
        d.lam_fv(np_fv, nat, with_witness)
    };

    let mn_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, np_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, np_predicate, motive, np_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, np_exists, eliminated);
        d.lam_fv(mn_fv, nat, with_witness)
    };

    let mp_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, mn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, mn_predicate, motive, mn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, mn_exists, eliminated);
        d.lam_fv(mp_fv, nat, with_witness)
    };

    let motive = d.kernel().lam(anon, mp_exists, target, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[nat, mp_predicate, motive, mp_minor, certificate])
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

    // coprime_of_bezout_one : ∀ a b, bezout a b 1 → Eq (gcd a b) 1
    //
    // A Bézout identity whose coefficient is 1 *is* coprimality, and this is the
    // direction ℚ needs: normalising num/den by g = gcd leaves cofactors whose
    // own identity has coefficient 1, and a rational's `reduced` field is
    // exactly the claim that their gcd is 1.
    //
    // `gcd a b` divides both arguments, hence all four products and both sums.
    // The identity `(1 + a·mn) + b·nn = a·mp + b·np` rearranges to `T = S + 1`,
    // and a divisor of both `S` and `S + 1` divides 1 — after ruling out the
    // divisor being zero, where `S + 1` would have to be zero.
    // bezout_of_scaled : ∀ g a b, 1 ≤ g → bezout (g*a) (g*b) g → bezout a b 1
    //
    // Divide a Bézout identity through by its own coefficient. This is the step
    // between `gcd_bezout` and coprimality of the cofactors: normalising a
    // rational leaves `a = g*a'` and `b = g*b'`, and what has to be shown about
    // the quotients is exactly the identity with `1` in place of `g`.
    //
    // Both sides are shown equal to `g * (…)` by distributivity and
    // associativity, and `mul_left_cancel_of_pos` removes the `g`.
    d.theorem(p.bezout_of_scaled, 3, &|d, values| {
        let (g, a, b) = (values[0], values[1], values[2]);
        let unit = d.num(1);
        let scaled_a = d.mul(g, a);
        let scaled_b = d.mul(g, b);
        let positive_ty = {
            let zero = d.zero();
            let one = d.succ(zero);
            d.le(one, g)
        };
        let hypothesis_ty = d.bezout(scaled_a, scaled_b, g);
        let conclusion = d.bezout(a, b, unit);
        let stmt = {
            let inner = d.arrow(hypothesis_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let certificate_fv = d.fresh_fvar();
        let certificate = d.kernel().fvar(certificate_fv);

        let body = bezout_elim(
            d,
            scaled_a,
            scaled_b,
            g,
            conclusion,
            certificate,
            &|d, mp, mn, np, nn, equation| {
                let unit = d.num(1);
                let scaled_a = d.mul(g, a);
                let scaled_b = d.mul(g, b);

                // The reduced identity, and the scaled one the hypothesis gives.
                let reduced = d.bezout_equation(a, b, unit, mp, mn, np, nn);
                let target_left = {
                    let head = {
                        let product = d.mul(a, mn);
                        d.add(unit, product)
                    };
                    let tail = d.mul(b, nn);
                    d.add(head, tail)
                };
                let target_right = {
                    let first = d.mul(a, mp);
                    let second = d.mul(b, np);
                    d.add(first, second)
                };
                let _ = reduced;

                // g * left, expanded down to the scaled identity's left side.
                let scaled_left = {
                    let head = {
                        let product = d.mul(scaled_a, mn);
                        d.add(g, product)
                    };
                    let tail = d.mul(scaled_b, nn);
                    d.add(head, tail)
                };
                let scaled_right = {
                    let first = d.mul(scaled_a, mp);
                    let second = d.mul(scaled_b, np);
                    d.add(first, second)
                };

                let expand_left = expand_scaled_left(d, &p, g, a, b, mn, nn);
                let expand_right = expand_scaled_right(d, &p, g, a, b, mp, np);

                // g*L = scaled_left = scaled_right = g*R
                let g_left = d.mul(g, target_left);
                let g_right = d.mul(g, target_right);
                let back = d.symm(g_right, scaled_right, expand_right);
                let (_reached, chained) = d.chain(
                    g_left,
                    &[
                        (scaled_left, expand_left),
                        (scaled_right, equation),
                        (g_right, back),
                    ],
                );
                let identity = d.lemma(
                    p.mul_left_cancel_of_pos,
                    &[g, target_left, target_right, positive, chained],
                );
                d.bezout_intro(a, b, unit, mp, mn, np, nn, identity)
            },
        );
        let proof = {
            let with_certificate = d.lam_fv(certificate_fv, hypothesis_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_certificate)
        };
        (stmt, proof)
    })?;

    d.theorem(p.coprime_of_bezout_one, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let unit = d.num(1);
        let common = d.gcd(a, b);
        let hypothesis_ty = d.bezout(a, b, unit);
        let conclusion = d.eq(common, unit);
        let stmt = d.arrow(hypothesis_ty, conclusion);

        let certificate_fv = d.fresh_fvar();
        let certificate = d.kernel().fvar(certificate_fv);

        let body = bezout_elim(
            d,
            a,
            b,
            unit,
            conclusion,
            certificate,
            &|d, mp, mn, np, nn, equation| {
                let unit = d.num(1);
                let common = d.gcd(a, b);
                let a_mn = d.mul(a, mn);
                let b_nn = d.mul(b, nn);
                let a_mp = d.mul(a, mp);
                let b_np = d.mul(b, np);
                let sum = d.add(a_mn, b_nn);
                let total = d.add(a_mp, b_np);

                // `(1 + a·mn) + b·nn = 1 + S = S + 1`, so `T = S + 1`.
                let left = {
                    let head = d.add(unit, a_mn);
                    d.add(head, b_nn)
                };
                let one_plus = d.add(unit, sum);
                let plus_one = d.add(sum, unit);
                let assoc = d.lemma(p.add_assoc, &[unit, a_mn, b_nn]);
                let commute = d.lemma(p.add_comm, &[unit, sum]);
                let (_reached, rearranged) =
                    d.chain(left, &[(one_plus, assoc), (plus_one, commute)]);
                let flipped = d.symm(left, total, equation);
                let total_eq = d.trans(total, left, plus_one, flipped, rearranged);

                // `gcd a b` divides both sums.
                let divides_a = d.lemma(p.gcd_dvd_left, &[a, b]);
                let divides_b = d.lemma(p.gcd_dvd_right, &[a, b]);
                let divides_sum = {
                    let first = d.lemma(p.dvd_mul_right_of_dvd, &[common, a, mn, divides_a]);
                    let second = d.lemma(p.dvd_mul_right_of_dvd, &[common, b, nn, divides_b]);
                    d.lemma(p.dvd_add, &[common, a_mn, b_nn, first, second])
                };
                let divides_total = {
                    let first = d.lemma(p.dvd_mul_right_of_dvd, &[common, a, mp, divides_a]);
                    let second = d.lemma(p.dvd_mul_right_of_dvd, &[common, b, np, divides_b]);
                    d.lemma(p.dvd_add, &[common, a_mp, b_np, first, second])
                };
                let divides_plus_one = {
                    let motive = d.eq_motive(total, &|d, x| d.dvd(common, x));
                    d.transport(total, motive, divides_total, plus_one, total_eq)
                };

                // ∀ x, dvd x S → dvd x (S+1) → x = 1, applied at `gcd a b`.
                let claim = |d: &mut NatDev<'_>, x: ExprId| {
                    let unit = d.num(1);
                    let lower = d.dvd(x, sum);
                    let upper = {
                        let shifted = d.add(sum, unit);
                        d.dvd(x, shifted)
                    };
                    let target = d.eq(x, unit);
                    let tail = d.arrow(upper, target);
                    d.arrow(lower, tail)
                };
                let at_zero = |d: &mut NatDev<'_>| {
                    let unit = d.num(1);
                    let zero = d.zero();
                    let shifted = d.add(sum, unit);
                    let lower_ty = d.dvd(zero, sum);
                    let upper_ty = d.dvd(zero, shifted);
                    let goal = d.eq(zero, unit);
                    let lower_fv = d.fresh_fvar();
                    let upper_fv = d.fresh_fvar();
                    let upper = d.kernel().fvar(upper_fv);
                    // `dvd 0 (S+1)` forces `S+1 = 0`, but `S+1` is a successor.
                    let predicate = d.dvd_predicate(zero, shifted);
                    let anon = d.anon_name();
                    let motive = d.kernel().lam(anon, upper_ty, goal, BinderInfo::Default);
                    let minor = {
                        let q_fv = d.fresh_fvar();
                        let q = d.kernel().fvar(q_fv);
                        let product = d.mul(zero, q);
                        let equality_ty = d.eq(shifted, product);
                        let e_fv = d.fresh_fvar();
                        let e = d.kernel().fvar(e_fv);
                        let collapse = d.lemma(p.zero_mul, &[q]);
                        let shifted_zero = {
                            let motive = d.eq_motive(product, &|d, x| {
                                let shifted = d.add(sum, unit);
                                d.eq(shifted, x)
                            });
                            d.transport(product, motive, e, zero, collapse)
                        };
                        // `S + 1 = succ (S + 0) = succ S`, so the equation says a
                        // successor is zero.
                        let padded = d.add(sum, zero);
                        let padded_succ = d.succ(padded);
                        let successor = d.succ(sum);
                        let step = d.lemma(p.add_succ, &[sum, zero]);
                        let tail = d.lemma(p.add_zero, &[sum]);
                        let lifted = d.congr(padded, sum, tail, &|d, x| d.succ(x));
                        let (_reached, shifted_is_succ) =
                            d.chain(shifted, &[(padded_succ, step), (successor, lifted)]);
                        let successor_zero = {
                            let motive = d.eq_motive(shifted, &|d, x| {
                                let successor = d.succ(sum);
                                d.eq(successor, x)
                            });
                            let base = d.symm(shifted, successor, shifted_is_succ);
                            d.transport(shifted, motive, base, zero, shifted_zero)
                        };
                        let reflexive = d.lemma(p.le_refl, &[successor]);
                        let upper_motive = d.eq_motive(successor, &|d, upper| {
                            let successor = d.succ(sum);
                            d.le(successor, upper)
                        });
                        let bounded =
                            d.transport(successor, upper_motive, reflexive, zero, successor_zero);
                        let contradiction = d.lemma(p.not_succ_le_zero, &[sum, bounded]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let level = d.kernel().level_zero();
                        let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
                        let anon = d.anon_name();
                        let false_motive =
                            d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
                        let body = d.apply(rec, &[false_motive, contradiction]);
                        let with_e = d.lam_fv(e_fv, equality_ty, body);
                        let nat = d.nat_ty();
                        d.lam_fv(q_fv, nat, with_e)
                    };
                    let nat = d.nat_ty();
                    let one_level = d.level_one();
                    let rec = d.kernel().const_(p.logic.exists_rec, vec![one_level]);
                    let eliminated = d.apply(rec, &[nat, predicate, motive, minor, upper]);
                    let with_upper = d.lam_fv(upper_fv, upper_ty, eliminated);
                    d.lam_fv(lower_fv, lower_ty, with_upper)
                };
                let at_succ = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| {
                    let unit = d.num(1);
                    let zero = d.zero();
                    let divisor = d.succ(k);
                    let shifted = d.add(sum, unit);
                    let lower_ty = d.dvd(divisor, sum);
                    let upper_ty = d.dvd(divisor, shifted);
                    let lower_fv = d.fresh_fvar();
                    let lower = d.kernel().fvar(lower_fv);
                    let upper_fv = d.fresh_fvar();
                    let upper = d.kernel().fvar(upper_fv);
                    let positive = {
                        let base = d.lemma(p.zero_le, &[k]);
                        d.lemma(p.le_succ_succ, &[zero, k, base])
                    };
                    let divides_one = d.lemma(
                        p.dvd_add_right_cancel_of_pos,
                        &[divisor, sum, unit, positive, lower, upper],
                    );
                    let body = d.lemma(p.eq_one_of_dvd_one, &[divisor, divides_one]);
                    let with_upper = d.lam_fv(upper_fv, upper_ty, body);
                    d.lam_fv(lower_fv, lower_ty, with_upper)
                };
                let general = d.induct(&claim, &at_zero, &at_succ, common);
                d.apply(general, &[divides_sum, divides_plus_one])
            },
        );
        let proof = d.lam_fv(certificate_fv, hypothesis_ty, body);
        (stmt, proof)
    })?;
    // gcd_cofactors_coprime : ∀ g a b, 1 ≤ g → gcd (g*a) (g*b) = g → gcd a b = 1
    //
    // The statement `Rat.normalize` needs: dividing a numerator and denominator
    // by their gcd leaves cofactors that are coprime. `gcd_bezout` supplies a
    // certificate for `gcd (g*a) (g*b)`, the hypothesis rewrites its coefficient
    // to `g`, `bezout_of_scaled` divides it through, and `coprime_of_bezout_one`
    // reads off the gcd.
    d.theorem(p.gcd_cofactors_coprime, 3, &|d, values| {
        let (g, a, b) = (values[0], values[1], values[2]);
        let unit = d.num(1);
        let scaled_a = d.mul(g, a);
        let scaled_b = d.mul(g, b);
        let common = d.gcd(scaled_a, scaled_b);
        let positive_ty = {
            let zero = d.zero();
            let one = d.succ(zero);
            d.le(one, g)
        };
        let hypothesis_ty = d.eq(common, g);
        let conclusion = {
            let cofactor = d.gcd(a, b);
            d.eq(cofactor, unit)
        };
        let stmt = {
            let inner = d.arrow(hypothesis_ty, conclusion);
            d.arrow(positive_ty, inner)
        };

        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let hypothesis_fv = d.fresh_fvar();
        let hypothesis = d.kernel().fvar(hypothesis_fv);

        let certificate = d.lemma(p.gcd_bezout, &[scaled_a, scaled_b]);
        let at_g = {
            let motive = d.eq_motive(common, &|d, x| {
                let scaled_a = d.mul(g, a);
                let scaled_b = d.mul(g, b);
                d.bezout(scaled_a, scaled_b, x)
            });
            d.transport(common, motive, certificate, g, hypothesis)
        };
        let divided = d.lemma(p.bezout_of_scaled, &[g, a, b, positive, at_g]);
        let body = d.lemma(p.coprime_of_bezout_one, &[a, b, divided]);
        let proof = {
            let with_hypothesis = d.lam_fv(hypothesis_fv, hypothesis_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_hypothesis)
        };
        (stmt, proof)
    })?;

    Ok(())
}
