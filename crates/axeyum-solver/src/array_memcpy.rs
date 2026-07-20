//! Small fixed-length memcpy refutations.
//!
//! This covers the generated two-byte memory-copy obligation:
//! under no-overlap and no-wrap guards for `[src, src + 2)` and
//! `[dst, dst + 2)`, every `j < 2` read from the copied destination equals the
//! original source read. The recognizer is deliberately narrow and re-checks the
//! original guarded assertion shape before accepting.

use axeyum_ir::{ArraySortKey, Op, Sort, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

const MEMCPY_LEN: u128 = 2;

/// A checked refutation of a guarded two-byte memcpy disequality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoByteMemcpyRefutationCertificate {
    /// The original top-level assertion carrying all guards and the disequality.
    pub assertion: TermId,
    /// Original memory array before the copy.
    pub base_array: TermId,
    /// Memory array after the two destination stores.
    pub copied_array: TermId,
    /// Source pointer.
    pub src: TermId,
    /// Destination pointer.
    pub dst: TermId,
    /// Quantified-by-finite-domain read offset guarded by `j < 2`.
    pub index: TermId,
    /// Bit width of memory addresses.
    pub index_width: u32,
    /// Bit width of memory elements.
    pub element_width: u32,
}

/// Returns a certificate when a top-level guarded BV1 assertion demands that a
/// two-byte non-overlapping memcpy fails at some `j < 2`.
#[must_use]
pub fn two_byte_memcpy_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TwoByteMemcpyRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let Some(bit) = match_negated_bv1_zero_equality(arena, assertion) else {
            continue;
        };
        let mut operands = Vec::new();
        collect_bv_and_operands(arena, bit, &mut operands);

        let mut no_wrap_guards = Vec::new();
        let mut no_overlap_guards = Vec::new();
        let mut bound_guards = Vec::new();
        let mut disequalities = Vec::new();
        for operand in operands {
            if let Some(guard) = match_no_wrap_guard(arena, operand) {
                no_wrap_guards.push(guard);
            }
            if let Some(guard) = match_no_overlap_guard(arena, operand) {
                no_overlap_guards.push(guard);
            }
            if let Some(guard) = match_index_bound_guard(arena, operand) {
                bound_guards.push(guard);
            }
            if let Some(diseq) = match_negated_eq_bit(arena, operand) {
                disequalities.push(diseq);
            }
        }

        for (lhs, rhs) in disequalities {
            if let Some(cert) = match_memcpy_failure(
                arena,
                assertion,
                lhs,
                rhs,
                &no_wrap_guards,
                &no_overlap_guards,
                &bound_guards,
            ) {
                return Some(cert);
            }
            if let Some(cert) = match_memcpy_failure(
                arena,
                assertion,
                rhs,
                lhs,
                &no_wrap_guards,
                &no_overlap_guards,
                &bound_guards,
            ) {
                return Some(cert);
            }
        }
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NoWrapGuard {
    base: TermId,
    width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NoOverlapGuard {
    first_base: TermId,
    second_base: TermId,
    width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoundGuard {
    index: TermId,
    width: u32,
}

fn match_memcpy_failure(
    arena: &TermArena,
    assertion: TermId,
    source_read: TermId,
    copied_read: TermId,
    no_wrap_guards: &[NoWrapGuard],
    no_overlap_guards: &[NoOverlapGuard],
    bound_guards: &[BoundGuard],
) -> Option<TwoByteMemcpyRefutationCertificate> {
    let (base_array, source_index) = match_select(arena, source_read)?;
    let (copied_array, copied_index) = match_select(arena, copied_read)?;
    let (src, dst, index, index_width) = match_common_offset(arena, source_index, copied_index)?;
    if !has_bound_guard(bound_guards, index, index_width)
        || !has_no_wrap_guard(no_wrap_guards, src, index_width)
        || !has_no_wrap_guard(no_wrap_guards, dst, index_width)
        || !has_no_overlap_guard(no_overlap_guards, src, dst, index_width)
    {
        return None;
    }

    let element_width = match_two_byte_copy(arena, copied_array, base_array, src, dst)?;
    if !array_sort_matches(arena, base_array, index_width, element_width)
        || arena.sort_of(base_array) != arena.sort_of(copied_array)
    {
        return None;
    }

    Some(TwoByteMemcpyRefutationCertificate {
        assertion,
        base_array,
        copied_array,
        src,
        dst,
        index,
        index_width,
        element_width,
    })
}

fn match_common_offset(
    arena: &TermArena,
    source_index: TermId,
    copied_index: TermId,
) -> Option<(TermId, TermId, TermId, u32)> {
    let source_terms = match_add_pair(arena, source_index)?;
    let copied_terms = match_add_pair(arena, copied_index)?;
    for (source_base, source_offset) in [
        (source_terms.0, source_terms.1),
        (source_terms.1, source_terms.0),
    ] {
        for (copied_base, copied_offset) in [
            (copied_terms.0, copied_terms.1),
            (copied_terms.1, copied_terms.0),
        ] {
            if source_offset == copied_offset {
                let Sort::BitVec(width) = arena.sort_of(source_base) else {
                    return None;
                };
                if arena.sort_of(copied_base) == Sort::BitVec(width)
                    && arena.sort_of(source_offset) == Sort::BitVec(width)
                {
                    return Some((source_base, copied_base, source_offset, width));
                }
            }
        }
    }
    None
}

fn match_two_byte_copy(
    arena: &TermArena,
    copied_array: TermId,
    base_array: TermId,
    src: TermId,
    dst: TermId,
) -> Option<u32> {
    let (first_store, second_index, second_value) = match_store(arena, copied_array)?;
    let (store_base, first_index, first_value) = match_store(arena, first_store)?;
    if store_base != base_array
        || !is_term_plus_const(arena, first_index, dst, 0)
        || !is_select_plus_const(arena, first_value, base_array, src, 0)
        || !is_term_plus_const(arena, second_index, dst, 1)
        || (!is_select_plus_const(arena, second_value, base_array, src, 1)
            && !is_select_plus_const(arena, second_value, first_store, src, 1))
    {
        return None;
    }
    let Sort::BitVec(element_width) = arena.sort_of(first_value) else {
        return None;
    };
    if arena.sort_of(second_value) == Sort::BitVec(element_width) {
        Some(element_width)
    } else {
        None
    }
}

fn match_negated_bv1_zero_equality(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*inner) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if is_bv_const(arena, *lhs, 1, 0) && arena.sort_of(*rhs) == Sort::BitVec(1) {
        Some(*rhs)
    } else if is_bv_const(arena, *rhs, 1, 0) && arena.sort_of(*lhs) == Sort::BitVec(1) {
        Some(*lhs)
    } else {
        None
    }
}

fn collect_bv_and_operands(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BvAnd,
            args,
        } if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
            collect_bv_and_operands(arena, args[0], out);
            collect_bv_and_operands(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn match_no_wrap_guard(arena: &TermArena, term: TermId) -> Option<NoWrapGuard> {
    let inner = match_bvnot(arena, term)?;
    let cond = match_bool_as_bv1(arena, inner)?;
    let (lhs, rhs) = match_bvult(arena, cond)?;
    let (base, width, offset) = match_term_plus_const(arena, lhs)?;
    if base == rhs && offset == MEMCPY_LEN {
        Some(NoWrapGuard { base, width })
    } else {
        None
    }
}

fn match_no_overlap_guard(arena: &TermArena, term: TermId) -> Option<NoOverlapGuard> {
    let inner = match_bvnot(arena, term)?;
    let TermNode::App {
        op: Op::BvAnd,
        args,
    } = arena.node(inner)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    let lhs = match_range_ult(arena, *lhs)?;
    let rhs = match_range_ult(arena, *rhs)?;
    if lhs.left_base == rhs.right_base && lhs.right_base == rhs.left_base && lhs.width == rhs.width
    {
        Some(NoOverlapGuard {
            first_base: lhs.left_base,
            second_base: lhs.right_base,
            width: lhs.width,
        })
    } else {
        None
    }
}

#[derive(Debug, Clone, Copy)]
struct RangeUlt {
    left_base: TermId,
    right_base: TermId,
    width: u32,
}

fn match_range_ult(arena: &TermArena, term: TermId) -> Option<RangeUlt> {
    let cond = match_bool_as_bv1(arena, term)?;
    let (lhs, rhs) = match_bvult(arena, cond)?;
    let (right_base, width, offset) = match_term_plus_const(arena, rhs)?;
    if offset == MEMCPY_LEN && arena.sort_of(lhs) == Sort::BitVec(width) {
        Some(RangeUlt {
            left_base: lhs,
            right_base,
            width,
        })
    } else {
        None
    }
}

fn match_index_bound_guard(arena: &TermArena, term: TermId) -> Option<BoundGuard> {
    let cond = match_bool_as_bv1(arena, term)?;
    let (lhs, rhs) = match_bvult(arena, cond)?;
    let TermNode::BvConst { width, value } = arena.node(rhs) else {
        return None;
    };
    if *value == MEMCPY_LEN && arena.sort_of(lhs) == Sort::BitVec(*width) {
        Some(BoundGuard {
            index: lhs,
            width: *width,
        })
    } else {
        None
    }
}

fn match_negated_eq_bit(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    if let Some(inner) = match_bvnot(arena, term) {
        let cond = match_bool_as_bv1(arena, inner)?;
        return match_eq(arena, cond);
    }
    let (cond, then_term, else_term) = match_ite(arena, term)?;
    if is_bv_const(arena, then_term, 1, 0) && is_bv_const(arena, else_term, 1, 1) {
        match_eq(arena, cond)
    } else {
        None
    }
}

fn match_bool_as_bv1(arena: &TermArena, term: TermId) -> Option<TermId> {
    let (cond, then_term, else_term) = match_ite(arena, term)?;
    if is_bv_const(arena, then_term, 1, 1) && is_bv_const(arena, else_term, 1, 0) {
        Some(cond)
    } else {
        None
    }
}

fn match_bvult(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BvUlt,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn match_eq(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if arena.sort_of(*lhs) == arena.sort_of(*rhs) {
        Some((*lhs, *rhs))
    } else {
        None
    }
}

fn match_select(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::Select,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [array, index] = &**args else {
        return None;
    };
    Some((*array, *index))
}

fn match_store(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [array, index, value] = &**args else {
        return None;
    };
    Some((*array, *index, *value))
}

fn match_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [cond, then_term, else_term] = &**args else {
        return None;
    };
    Some((*cond, *then_term, *else_term))
}

fn match_bvnot(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BvNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    Some(*inner)
}

fn match_add_pair(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BvAdd,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn match_term_plus_const(arena: &TermArena, term: TermId) -> Option<(TermId, u32, u128)> {
    let (lhs, rhs) = match_add_pair(arena, term)?;
    match_term_plus_const_side(arena, lhs, rhs)
        .or_else(|| match_term_plus_const_side(arena, rhs, lhs))
}

fn match_term_plus_const_side(
    arena: &TermArena,
    constant: TermId,
    base: TermId,
) -> Option<(TermId, u32, u128)> {
    let TermNode::BvConst { width, value } = arena.node(constant) else {
        return None;
    };
    if arena.sort_of(base) == Sort::BitVec(*width) {
        Some((base, *width, *value))
    } else {
        None
    }
}

fn is_term_plus_const(arena: &TermArena, term: TermId, base: TermId, offset: u128) -> bool {
    if offset == 0 && term == base {
        return true;
    }
    match_term_plus_const(arena, term)
        .is_some_and(|(found_base, _, found_offset)| found_base == base && found_offset == offset)
}

fn is_select_plus_const(
    arena: &TermArena,
    term: TermId,
    array: TermId,
    base: TermId,
    offset: u128,
) -> bool {
    match_select(arena, term).is_some_and(|(read_array, index)| {
        read_array == array && is_term_plus_const(arena, index, base, offset)
    })
}

fn has_bound_guard(guards: &[BoundGuard], index: TermId, width: u32) -> bool {
    guards
        .iter()
        .any(|guard| guard.index == index && guard.width == width)
}

fn has_no_wrap_guard(guards: &[NoWrapGuard], base: TermId, width: u32) -> bool {
    guards
        .iter()
        .any(|guard| guard.base == base && guard.width == width)
}

fn has_no_overlap_guard(guards: &[NoOverlapGuard], src: TermId, dst: TermId, width: u32) -> bool {
    guards.iter().any(|guard| {
        guard.width == width
            && ((guard.first_base == src && guard.second_base == dst)
                || (guard.first_base == dst && guard.second_base == src))
    })
}

fn array_sort_matches(
    arena: &TermArena,
    array: TermId,
    index_width: u32,
    element_width: u32,
) -> bool {
    matches!(
        arena.sort_of(array),
        Sort::Array {
            index: ArraySortKey::BitVec(found_index),
            element: ArraySortKey::BitVec(found_element),
        } if found_index == index_width && found_element == element_width
    )
}

fn is_bv_const(arena: &TermArena, term: TermId, expected_width: u32, expected_value: u128) -> bool {
    matches!(
        arena.node(term),
        TermNode::BvConst { width, value }
            if *width == expected_width && *value == expected_value
    )
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::*;

    #[test]
    fn refutes_two_byte_memcpy_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__memcpy02.smt2"
        );
        let script = parse_script(text).expect("parse memcpy02");
        let cert = two_byte_memcpy_refutation(&script.arena, &script.assertions)
            .expect("memcpy02 is a guarded two-byte memcpy contradiction");
        assert_eq!(cert.index_width, 32);
        assert_eq!(cert.element_width, 8);
    }
}
