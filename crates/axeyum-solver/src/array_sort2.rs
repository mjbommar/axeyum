//! Small two-element array sorting refutations.
//!
//! This recognizes the generated length-2 bubble-sort and selection-sort proof
//! obligations: the output cells are a conditional permutation of the two
//! original cells, the output is asserted sorted, and an arbitrary original read
//! guarded to the two-cell range is asserted different from both output cells.
//! The checker re-matches the exact generated shape before accepting the
//! certificate.

use axeyum_ir::{ArraySortKey, Op, Sort, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

const SORT_LEN: u128 = 2;

/// A checked refutation of a guarded two-element bubble-sort membership failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoElementBubbleSortCertificate {
    /// The original top-level assertion carrying the sortedness and membership
    /// failure bits.
    pub assertion: TermId,
    /// Original memory array before sorting.
    pub base_array: TermId,
    /// First index in the two-element range.
    pub start: TermId,
    /// Arbitrary read index guarded into `[start, start + 2)`.
    pub index: TermId,
    /// Output value at `start`.
    pub low_value: TermId,
    /// Output value at `start + 1`.
    pub high_value: TermId,
    /// Bit width of memory indices.
    pub index_width: u32,
    /// Bit width of memory elements.
    pub element_width: u32,
}

/// A checked refutation of a guarded two-element selection-sort membership
/// failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoElementSelectionSortCertificate {
    /// The original top-level assertion carrying the sortedness and membership
    /// failure bits.
    pub assertion: TermId,
    /// Original memory array before sorting.
    pub base_array: TermId,
    /// First index in the two-element range.
    pub start: TermId,
    /// Arbitrary read index guarded into `[start, start + 2)`.
    pub index: TermId,
    /// Output value at `start`.
    pub low_value: TermId,
    /// Output value at `start + 1`.
    pub high_value: TermId,
    /// Bit width of memory indices.
    pub index_width: u32,
    /// Bit width of memory elements.
    pub element_width: u32,
}

/// Returns a certificate when a top-level guarded BV1 assertion demands that a
/// length-2 bubble sort loses the original element read at an in-range index.
#[must_use]
pub fn two_element_bubble_sort_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TwoElementBubbleSortCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let bit = match_negated_bv1_zero_equality(arena, assertion)?;
        let inner = match_bvnot(arena, bit)?;
        let mut operands = Vec::new();
        collect_bv_and_operands(arena, inner, &mut operands);

        let sorted_pairs = operands
            .iter()
            .filter_map(|&operand| match_not_ult_bit(arena, operand))
            .collect::<Vec<_>>();
        let bad_terms = operands
            .iter()
            .filter_map(|&operand| match_bvnot(arena, operand))
            .collect::<Vec<_>>();

        for bad in bad_terms {
            if let Some(cert) = match_bad_membership(arena, assertion, bad, sorted_pairs.as_slice())
            {
                return Some(cert);
            }
        }
    }
    None
}

/// Returns a certificate when a top-level guarded BV1 assertion demands that a
/// length-2 selection sort loses the original element read at an in-range index.
#[must_use]
pub fn two_element_selection_sort_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TwoElementSelectionSortCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let bit = match_negated_bv1_zero_equality(arena, assertion)?;
        let inner = match_bvnot(arena, bit)?;
        let mut operands = Vec::new();
        collect_bv_and_operands(arena, inner, &mut operands);

        let sorted_pairs = operands
            .iter()
            .filter_map(|&operand| match_not_ult_bit(arena, operand))
            .collect::<Vec<_>>();
        let bad_terms = operands
            .iter()
            .filter_map(|&operand| match_bvnot(arena, operand))
            .collect::<Vec<_>>();

        for bad in bad_terms {
            if let Some(cert) =
                match_bad_selection_membership(arena, assertion, bad, sorted_pairs.as_slice())
            {
                return Some(cert);
            }
        }
    }
    None
}

fn match_bad_membership(
    arena: &TermArena,
    assertion: TermId,
    bad: TermId,
    sorted_pairs: &[(TermId, TermId)],
) -> Option<TwoElementBubbleSortCertificate> {
    let mut operands = Vec::new();
    collect_bv_and_operands(arena, bad, &mut operands);
    let range = match_range_guard(arena, &operands)?;
    let neqs = operands
        .iter()
        .filter_map(|&operand| match_neq_read(arena, operand))
        .collect::<Vec<_>>();
    if neqs.len() != 2
        || neqs[0].base_array != neqs[1].base_array
        || neqs[0].index != neqs[1].index
        || neqs[0].index != range.index
    {
        return None;
    }

    for &(high, low) in sorted_pairs {
        if !same_pair((neqs[0].value, neqs[1].value), (low, high)) {
            continue;
        }
        if let Some((base_array, element_width)) =
            match_bubble_outputs(arena, low, high, range.start)
        {
            if base_array != neqs[0].base_array
                || !array_sort_matches(arena, base_array, range.width, element_width)
            {
                continue;
            }
            return Some(TwoElementBubbleSortCertificate {
                assertion,
                base_array,
                start: range.start,
                index: range.index,
                low_value: low,
                high_value: high,
                index_width: range.width,
                element_width,
            });
        }
    }
    None
}

fn match_bad_selection_membership(
    arena: &TermArena,
    assertion: TermId,
    bad: TermId,
    sorted_pairs: &[(TermId, TermId)],
) -> Option<TwoElementSelectionSortCertificate> {
    let mut operands = Vec::new();
    collect_bv_and_operands(arena, bad, &mut operands);
    let range = match_range_guard(arena, &operands)?;
    let neqs = operands
        .iter()
        .filter_map(|&operand| match_neq_read(arena, operand))
        .collect::<Vec<_>>();
    if neqs.len() != 2
        || neqs[0].base_array != neqs[1].base_array
        || neqs[0].index != neqs[1].index
        || neqs[0].index != range.index
    {
        return None;
    }

    for &(high, low) in sorted_pairs {
        if !same_pair((neqs[0].value, neqs[1].value), (low, high)) {
            continue;
        }
        if let Some((base_array, element_width)) =
            match_selection_outputs(arena, low, high, range.start)
        {
            if base_array != neqs[0].base_array
                || !array_sort_matches(arena, base_array, range.width, element_width)
            {
                continue;
            }
            return Some(TwoElementSelectionSortCertificate {
                assertion,
                base_array,
                start: range.start,
                index: range.index,
                low_value: low,
                high_value: high,
                index_width: range.width,
                element_width,
            });
        }
    }
    None
}

#[derive(Debug, Clone, Copy)]
struct RangeGuard {
    start: TermId,
    index: TermId,
    width: u32,
}

#[derive(Debug, Clone, Copy)]
struct NeqRead {
    base_array: TermId,
    index: TermId,
    value: TermId,
}

fn match_range_guard(arena: &TermArena, operands: &[TermId]) -> Option<RangeGuard> {
    let mut lowers = Vec::new();
    let mut uppers = Vec::new();
    for &operand in operands {
        if let Some(lower) = match_lower_range_guard(arena, operand) {
            lowers.push(lower);
        }
        if let Some(upper) = match_upper_range_guard(arena, operand) {
            uppers.push(upper);
        }
    }

    for lower in lowers {
        for upper in &uppers {
            if lower.start == upper.start
                && lower.index == upper.index
                && lower.width == upper.width
            {
                return Some(lower);
            }
        }
    }
    None
}

fn match_lower_range_guard(arena: &TermArena, term: TermId) -> Option<RangeGuard> {
    let inner = match_bvnot(arena, term)?;
    let cond = match_bool_as_bv1(arena, inner)?;
    let (index, start) = match_bvult(arena, cond)?;
    match_range_guard_terms(arena, index, start)
}

fn match_upper_range_guard(arena: &TermArena, term: TermId) -> Option<RangeGuard> {
    let cond = match_bool_as_bv1(arena, term)?;
    let (index, upper) = match_bvult(arena, cond)?;
    let (start, width, offset) = match_term_plus_const(arena, upper)?;
    if offset == SORT_LEN {
        match_range_guard_terms(arena, index, start).filter(|guard| guard.width == width)
    } else {
        None
    }
}

fn match_range_guard_terms(arena: &TermArena, index: TermId, start: TermId) -> Option<RangeGuard> {
    let Sort::BitVec(width) = arena.sort_of(index) else {
        return None;
    };
    if arena.sort_of(start) == Sort::BitVec(width) {
        Some(RangeGuard {
            start,
            index,
            width,
        })
    } else {
        None
    }
}

fn match_neq_read(arena: &TermArena, term: TermId) -> Option<NeqRead> {
    let inner = match_bvnot(arena, term)?;
    let cond = match_bool_as_bv1(arena, inner)?;
    let (lhs, rhs) = match_eq(arena, cond)?;
    match_neq_read_side(arena, lhs, rhs).or_else(|| match_neq_read_side(arena, rhs, lhs))
}

fn match_neq_read_side(arena: &TermArena, read: TermId, value: TermId) -> Option<NeqRead> {
    let (base_array, index) = match_select(arena, read)?;
    Some(NeqRead {
        base_array,
        index,
        value,
    })
}

fn match_bubble_outputs(
    arena: &TermArena,
    low: TermId,
    high: TermId,
    start: TermId,
) -> Option<(TermId, u32)> {
    let (cond, first_value, second_value) = match_ite(arena, high)?;
    let (base_array, first_index) = match_select(arena, first_value)?;
    let (second_base, second_index) = match_select(arena, second_value)?;
    if second_base != base_array
        || first_index != start
        || !is_term_plus_const(arena, second_index, start, 1)
        || !matches_sort(arena, first_value, second_value)
        || !match_swap_condition(arena, cond, first_value, second_value)
    {
        return None;
    }

    let Sort::BitVec(element_width) = arena.sort_of(first_value) else {
        return None;
    };
    let pattern = BubbleOutputPattern {
        base_array,
        start,
        cond,
        low_value: second_value,
        high_value: first_value,
        high,
    };
    if is_ite(arena, low, cond, second_value, first_value)
        || matches_sorted_low_read(arena, low, &pattern)
    {
        Some((base_array, element_width))
    } else {
        None
    }
}

struct BubbleOutputPattern {
    base_array: TermId,
    start: TermId,
    cond: TermId,
    low_value: TermId,
    high_value: TermId,
    high: TermId,
}

fn matches_sorted_low_read(arena: &TermArena, low: TermId, pattern: &BubbleOutputPattern) -> bool {
    let Some((sorted_array, read_index)) = match_select(arena, low) else {
        return false;
    };
    if read_index != pattern.start {
        return false;
    }
    let Some((first_store, second_index, second_value)) = match_store(arena, sorted_array) else {
        return false;
    };
    let Some((store_base, first_index, first_value)) = match_store(arena, first_store) else {
        return false;
    };
    store_base == pattern.base_array
        && first_index == pattern.start
        && is_term_plus_const(arena, second_index, pattern.start, 1)
        && second_value == pattern.high
        && is_ite(
            arena,
            first_value,
            pattern.cond,
            pattern.low_value,
            pattern.high_value,
        )
}

fn match_selection_outputs(
    arena: &TermArena,
    low: TermId,
    high: TermId,
    start: TermId,
) -> Option<(TermId, u32)> {
    let (sorted_array, low_index) = match_select(arena, low)?;
    let (high_array, high_index) = match_select(arena, high)?;
    if sorted_array != high_array
        || low_index != start
        || !is_term_plus_const(arena, high_index, start, 1)
    {
        return None;
    }

    let (first_store, second_store_index, second_store_value) = match_store(arena, sorted_array)?;
    let (base_array, first_store_index, first_store_value) = match_store(arena, first_store)?;
    if first_store_index != start {
        return None;
    }
    let (first_read_array, first_read_index) = match_select(arena, second_store_value)?;
    let (selected_array, selected_index) = match_select(arena, first_store_value)?;
    if first_read_array != base_array
        || first_read_index != start
        || selected_array != base_array
        || selected_index != second_store_index
        || !matches_sort(arena, first_store_value, second_store_value)
        || !match_selection_min_index(
            arena,
            selected_index,
            base_array,
            start,
            high_index,
            second_store_value,
        )
    {
        return None;
    }

    let Sort::BitVec(element_width) = arena.sort_of(second_store_value) else {
        return None;
    };
    Some((base_array, element_width))
}

fn match_selection_min_index(
    arena: &TermArena,
    min_index: TermId,
    base_array: TermId,
    start: TermId,
    second_index: TermId,
    first_value: TermId,
) -> bool {
    let Some((cond, then_index, else_index)) = match_ite(arena, min_index) else {
        return false;
    };
    then_index == second_index
        && else_index == start
        && selection_condition_matches(arena, cond, base_array, second_index, first_value)
}

fn selection_condition_matches(
    arena: &TermArena,
    cond: TermId,
    base_array: TermId,
    second_index: TermId,
    first_value: TermId,
) -> bool {
    let Some((lhs, rhs)) = match_eq(arena, cond) else {
        return false;
    };
    selection_condition_side(arena, lhs, rhs, base_array, second_index, first_value)
        || selection_condition_side(arena, rhs, lhs, base_array, second_index, first_value)
}

fn selection_condition_side(
    arena: &TermArena,
    one: TermId,
    test: TermId,
    base_array: TermId,
    second_index: TermId,
    first_value: TermId,
) -> bool {
    if !is_bv_const(arena, one, 1, 1) {
        return false;
    }
    let Some((lhs, rhs)) = match_bool_as_bv1(arena, test).and_then(|term| match_bvult(arena, term))
    else {
        return false;
    };
    rhs == first_value
        && match_select(arena, lhs)
            .is_some_and(|(array, index)| array == base_array && index == second_index)
}

fn match_swap_condition(
    arena: &TermArena,
    cond: TermId,
    first_value: TermId,
    second_value: TermId,
) -> bool {
    let Some((lhs, rhs)) = match_eq(arena, cond) else {
        return false;
    };
    (is_bv_const(arena, lhs, 1, 1) && is_ult_as_bv1(arena, rhs, second_value, first_value))
        || (is_bv_const(arena, rhs, 1, 1) && is_ult_as_bv1(arena, lhs, second_value, first_value))
}

fn is_ult_as_bv1(arena: &TermArena, term: TermId, lhs: TermId, rhs: TermId) -> bool {
    match_bool_as_bv1(arena, term)
        .and_then(|cond| match_bvult(arena, cond))
        .is_some_and(|(found_lhs, found_rhs)| found_lhs == lhs && found_rhs == rhs)
}

fn match_not_ult_bit(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let inner = match_bvnot(arena, term)?;
    let cond = match_bool_as_bv1(arena, inner)?;
    match_bvult(arena, cond)
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

fn match_term_plus_const(arena: &TermArena, term: TermId) -> Option<(TermId, u32, u128)> {
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
    match_term_plus_const_side(arena, *lhs, *rhs)
        .or_else(|| match_term_plus_const_side(arena, *rhs, *lhs))
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

fn is_ite(
    arena: &TermArena,
    term: TermId,
    cond: TermId,
    then_term: TermId,
    else_term: TermId,
) -> bool {
    match_ite(arena, term).is_some_and(|(found_cond, found_then, found_else)| {
        found_cond == cond && found_then == then_term && found_else == else_term
    })
}

fn same_pair(lhs: (TermId, TermId), rhs: (TermId, TermId)) -> bool {
    (lhs.0 == rhs.0 && lhs.1 == rhs.1) || (lhs.0 == rhs.1 && lhs.1 == rhs.0)
}

fn matches_sort(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    arena.sort_of(lhs) == arena.sort_of(rhs)
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
    fn refutes_two_element_bubble_sort_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__bubsort002un.smt2"
        );
        let script = parse_script(text).expect("parse bubsort002un");
        let cert = two_element_bubble_sort_refutation(&script.arena, &script.assertions)
            .expect("bubsort002un is a guarded two-element bubble-sort contradiction");
        assert_eq!(cert.index_width, 32);
        assert_eq!(cert.element_width, 8);
    }

    #[test]
    fn refutes_two_element_selection_sort_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__selsort002un.smt2"
        );
        let script = parse_script(text).expect("parse selsort002un");
        let cert = two_element_selection_sort_refutation(&script.arena, &script.assertions)
            .expect("selsort002un is a guarded two-element selection-sort contradiction");
        assert_eq!(cert.index_width, 32);
        assert_eq!(cert.element_width, 8);
    }
}
