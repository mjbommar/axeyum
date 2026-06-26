//! Checked popcount/set-cardinality refutations over SMT-LIB finite-set lowering.
//!
//! The SMT-LIB frontend lowers finite sets to bit-vectors and direct
//! `set.card` comparisons to exact BV popcount comparisons. This checker
//! recognizes only that lowered shape, plus bit-vector subset facts and safe
//! cardinality upper bounds for unions/intersections. It is intentionally
//! narrow: callers must re-run this matcher on the original lowered assertions
//! before accepting the certificate.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

/// A self-checking refutation of inconsistent lowered set-cardinality bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetCardinalityRefutationCertificate {
    /// The term with a popcount lower bound.
    pub subset: TermId,
    /// A syntactic or asserted superset of [`Self::subset`].
    pub superset: TermId,
    /// The lower bound on `popcount(subset)`.
    pub lower_bound: u32,
    /// The derived upper bound on `popcount(superset)`.
    pub upper_bound: u32,
}

#[derive(Debug, Default)]
struct Facts {
    lower_bounds: BTreeMap<TermId, u32>,
    upper_bounds: BTreeMap<TermId, u32>,
    subset_edges: Vec<(TermId, TermId)>,
    candidate_terms: BTreeSet<TermId>,
}

#[derive(Debug, Clone, Copy)]
enum BoundKind {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy)]
struct Bound {
    term: TermId,
    kind: BoundKind,
    value: u32,
}

#[derive(Debug, Clone, Copy)]
struct Popcount {
    set: TermId,
    count_width: u32,
}

/// Returns a certificate when the lowered finite-set cardinality constraints are
/// locally inconsistent.
#[must_use]
pub fn set_cardinality_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<SetCardinalityRefutationCertificate> {
    let mut facts = Facts::default();
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
        collect_bitvec_terms(arena, assertion, &mut facts.candidate_terms);
    }
    for conjunct in conjuncts {
        if let Some(bounds) = match_popcount_comparison(arena, conjunct) {
            for bound in bounds {
                facts.candidate_terms.insert(bound.term);
                record_bound(&mut facts, bound);
            }
        }
        if let Some(edge) = match_subset_equality(arena, conjunct) {
            facts.candidate_terms.insert(edge.0);
            facts.candidate_terms.insert(edge.1);
            facts.subset_edges.push(edge);
        }
    }
    facts.subset_edges.sort_unstable();
    facts.subset_edges.dedup();

    if facts.lower_bounds.is_empty() {
        return None;
    }

    let mut upper_memo = BTreeMap::new();
    for (&subset, &lower_bound) in &facts.lower_bounds {
        for &superset in &facts.candidate_terms {
            if !same_bv_width(arena, subset, superset)
                || !is_subset_of(arena, subset, superset, &facts.subset_edges)
            {
                continue;
            }
            let upper_bound = upper_bound_for_expr(arena, superset, &facts, &mut upper_memo)?;
            if lower_bound > upper_bound {
                return Some(SetCardinalityRefutationCertificate {
                    subset,
                    superset,
                    lower_bound,
                    upper_bound,
                });
            }
        }
    }
    None
}

fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_top_conjuncts(arena, args[0], out);
            collect_top_conjuncts(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn collect_bitvec_terms(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if matches!(arena.sort_of(term), Sort::BitVec(_)) {
        out.insert(term);
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        for &arg in &**args {
            collect_bitvec_terms(arena, arg, out);
        }
    }
}

fn record_bound(facts: &mut Facts, bound: Bound) {
    match bound.kind {
        BoundKind::Lower => {
            facts
                .lower_bounds
                .entry(bound.term)
                .and_modify(|current| *current = (*current).max(bound.value))
                .or_insert(bound.value);
        }
        BoundKind::Upper => {
            facts
                .upper_bounds
                .entry(bound.term)
                .and_modify(|current| *current = (*current).min(bound.value))
                .or_insert(bound.value);
        }
    }
}

fn match_popcount_comparison(arena: &TermArena, term: TermId) -> Option<Vec<Bound>> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if matches!(op, Op::Eq) {
        if let (Some(pc), Some(k)) = (parse_popcount(arena, *lhs), bv_const_u32(arena, *rhs))
            && k_fits_popcount(k, pc)
        {
            return Some(vec![
                Bound {
                    term: pc.set,
                    kind: BoundKind::Lower,
                    value: k,
                },
                Bound {
                    term: pc.set,
                    kind: BoundKind::Upper,
                    value: k,
                },
            ]);
        }
        if let (Some(k), Some(pc)) = (bv_const_u32(arena, *lhs), parse_popcount(arena, *rhs))
            && k_fits_popcount(k, pc)
        {
            return Some(vec![
                Bound {
                    term: pc.set,
                    kind: BoundKind::Lower,
                    value: k,
                },
                Bound {
                    term: pc.set,
                    kind: BoundKind::Upper,
                    value: k,
                },
            ]);
        }
        return None;
    }

    let direct = parse_popcount(arena, *lhs)
        .zip(bv_const_u32(arena, *rhs))
        .and_then(|(pc, k)| comparison_bound(*op, pc, k, true));
    if direct.is_some() {
        return direct.map(|bound| vec![bound]);
    }
    parse_popcount(arena, *rhs)
        .zip(bv_const_u32(arena, *lhs))
        .and_then(|(pc, k)| comparison_bound(*op, pc, k, false))
        .map(|bound| vec![bound])
}

fn comparison_bound(op: Op, pc: Popcount, k: u32, popcount_on_lhs: bool) -> Option<Bound> {
    if !k_fits_popcount(k, pc) {
        return None;
    }
    let (kind, value) = match (op, popcount_on_lhs) {
        (Op::BvUge, true) | (Op::BvUle, false) => (BoundKind::Lower, k),
        (Op::BvUgt, true) | (Op::BvUlt, false) => (BoundKind::Lower, k.checked_add(1)?),
        (Op::BvUle, true) | (Op::BvUge, false) => (BoundKind::Upper, k),
        (Op::BvUlt, true) | (Op::BvUgt, false) => (BoundKind::Upper, k.checked_sub(1)?),
        _ => return None,
    };
    Some(Bound {
        term: pc.set,
        kind,
        value,
    })
}

fn k_fits_popcount(k: u32, pc: Popcount) -> bool {
    pc.count_width < 128 && u128::from(k) < (1_u128 << pc.count_width)
}

fn parse_popcount(arena: &TermArena, term: TermId) -> Option<Popcount> {
    let Sort::BitVec(count_width) = arena.sort_of(term) else {
        return None;
    };
    let mut leaves = Vec::new();
    collect_popcount_leaves(arena, term, count_width, &mut leaves)?;
    let mut set = None;
    let mut set_width = None;
    let mut bits = BTreeSet::new();
    for (bit, bit_set) in leaves {
        let Sort::BitVec(width) = arena.sort_of(bit_set) else {
            return None;
        };
        if bit >= width {
            return None;
        }
        if set.is_some_and(|seen| seen != bit_set) || set_width.is_some_and(|seen| seen != width) {
            return None;
        }
        set = Some(bit_set);
        set_width = Some(width);
        if !bits.insert(bit) {
            return None;
        }
    }
    let set = set?;
    let set_width = set_width?;
    if bits.len() != usize::try_from(set_width).ok()?
        || bits.iter().copied().ne(0..set_width)
        || bits_for(u128::from(set_width)) > count_width
    {
        return None;
    }
    Some(Popcount { set, count_width })
}

fn collect_popcount_leaves(
    arena: &TermArena,
    term: TermId,
    count_width: u32,
    out: &mut Vec<(u32, TermId)>,
) -> Option<()> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BvAdd,
            args,
        } if args.len() == 2 => {
            collect_popcount_leaves(arena, args[0], count_width, out)?;
            collect_popcount_leaves(arena, args[1], count_width, out)
        }
        TermNode::App {
            op: Op::ZeroExt { by },
            args,
        } if args.len() == 1 && *by + 1 == count_width => {
            let TermNode::App {
                op: Op::Extract { hi, lo },
                args: extract_args,
            } = arena.node(args[0])
            else {
                return None;
            };
            let [set] = &**extract_args else {
                return None;
            };
            if hi != lo || arena.sort_of(args[0]) != Sort::BitVec(1) {
                return None;
            }
            out.push((*hi, *set));
            Some(())
        }
        _ => None,
    }
}

fn match_subset_equality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    subset_side(arena, *lhs, *rhs).or_else(|| subset_side(arena, *rhs, *lhs))
}

fn subset_side(
    arena: &TermArena,
    maybe_subset: TermId,
    maybe_intersection: TermId,
) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BvAnd,
        args,
    } = arena.node(maybe_intersection)
    else {
        return None;
    };
    let [a, b] = &**args else {
        return None;
    };
    if *a == maybe_subset && same_bv_width(arena, maybe_subset, *b) {
        Some((maybe_subset, *b))
    } else if *b == maybe_subset && same_bv_width(arena, maybe_subset, *a) {
        Some((maybe_subset, *a))
    } else {
        None
    }
}

fn is_subset_of(
    arena: &TermArena,
    subset: TermId,
    superset: TermId,
    edges: &[(TermId, TermId)],
) -> bool {
    let mut seen = BTreeSet::new();
    is_subset_of_inner(arena, subset, superset, edges, &mut seen)
}

fn is_subset_of_inner(
    arena: &TermArena,
    subset: TermId,
    superset: TermId,
    edges: &[(TermId, TermId)],
    seen: &mut BTreeSet<(TermId, TermId)>,
) -> bool {
    if subset == superset {
        return true;
    }
    if !same_bv_width(arena, subset, superset) || !seen.insert((subset, superset)) {
        return false;
    }
    if let TermNode::App { op: Op::BvOr, args } = arena.node(superset)
        && args.len() == 2
        && (is_subset_of_inner(arena, subset, args[0], edges, seen)
            || is_subset_of_inner(arena, subset, args[1], edges, seen))
    {
        return true;
    }
    if let TermNode::App {
        op: Op::BvAnd,
        args,
    } = arena.node(subset)
        && args.len() == 2
        && (is_subset_of_inner(arena, args[0], superset, edges, seen)
            || is_subset_of_inner(arena, args[1], superset, edges, seen))
    {
        return true;
    }
    edges
        .iter()
        .filter(|(lhs, _)| *lhs == subset)
        .any(|(_, rhs)| is_subset_of_inner(arena, *rhs, superset, edges, seen))
}

fn upper_bound_for_expr(
    arena: &TermArena,
    term: TermId,
    facts: &Facts,
    memo: &mut BTreeMap<TermId, Option<u32>>,
) -> Option<u32> {
    if let Some(cached) = memo.get(&term) {
        return *cached;
    }
    let mut best = match arena.sort_of(term) {
        Sort::BitVec(width) => Some(width),
        _ => None,
    };
    if let Some(&direct) = facts.upper_bounds.get(&term) {
        best = Some(best.map_or(direct, |current| current.min(direct)));
    }
    if let TermNode::App { op, args } = arena.node(term)
        && args.len() == 2
    {
        match op {
            Op::BvOr => {
                if let (Some(lhs), Some(rhs)) = (
                    upper_bound_for_expr(arena, args[0], facts, memo),
                    upper_bound_for_expr(arena, args[1], facts, memo),
                ) && let Some(sum) = lhs.checked_add(rhs)
                {
                    best = Some(best.map_or(sum, |current| current.min(sum)));
                }
            }
            Op::BvAnd => {
                let lhs = upper_bound_for_expr(arena, args[0], facts, memo);
                let rhs = upper_bound_for_expr(arena, args[1], facts, memo);
                let intersect = match (lhs, rhs) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                };
                if let Some(bound) = intersect {
                    best = Some(best.map_or(bound, |current| current.min(bound)));
                }
            }
            _ => {}
        }
    }
    memo.insert(term, best);
    best
}

fn same_bv_width(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    matches!(
        (arena.sort_of(lhs), arena.sort_of(rhs)),
        (Sort::BitVec(a), Sort::BitVec(b)) if a == b
    )
}

fn bv_const_u32(arena: &TermArena, term: TermId) -> Option<u32> {
    let TermNode::BvConst { value, .. } = arena.node(term) else {
        return None;
    };
    u32::try_from(*value).ok()
}

fn bits_for(n: u128) -> u32 {
    (128 - n.leading_zeros()).max(1)
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::set_cardinality_refutation;

    #[test]
    fn recognizes_card_6_subset_union_overflow() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sets__card-6.smt2"
        );
        let script = parse_script(text).expect("parse card-6");
        let cert = set_cardinality_refutation(&script.arena, &script.assertions)
            .expect("card-6 has a local cardinality contradiction");
        assert_eq!(cert.lower_bound, 5);
        assert_eq!(cert.upper_bound, 4);
    }

    #[test]
    fn recognizes_union_upper_bound_smaller_than_operand_lower_bound() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__sets__card.smt2"
        );
        let script = parse_script(text).expect("parse card");
        let cert = set_cardinality_refutation(&script.arena, &script.assertions)
            .expect("card has a local cardinality contradiction");
        assert_eq!(cert.lower_bound, 5);
        assert_eq!(cert.upper_bound, 4);
    }

    #[test]
    fn rejects_tight_satisfiable_subset_union_bound() {
        let text = r"
        (set-logic QF_UFLIAFS)
        (declare-sort E 0)
        (declare-fun A () (Set E))
        (declare-fun B () (Set E))
        (declare-fun C () (Set E))
        (assert
          (and
            (set.subset C (set.union A B))
            (>= (set.card C) 4)
            (<= (set.card A) 2)
            (<= (set.card B) 2)))
        (check-sat)
        ";
        let script = parse_script(text).expect("parse satisfiable tight bound");
        assert!(set_cardinality_refutation(&script.arena, &script.assertions).is_none());
    }
}
