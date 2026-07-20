//! Small XOR-swap array permutation refutations.
//!
//! This covers generated memory obligations where a two-cell ordinary swap is
//! compared with the standard three-assignment XOR swap. The recognizer is
//! intentionally narrow: it re-matches generated swap nests and checks the exact
//! XOR dataflow before accepting the disequality as impossible.

use axeyum_ir::{ArraySortKey, Op, Sort, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// A checked refutation of a two-stage ordinary-swap versus XOR-swap
/// disequality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoCellXorSwapCertificate {
    /// The original top-level assertion demanding the two arrays differ.
    pub assertion: TermId,
    /// Common base array before the first swap.
    pub base_array: TermId,
    /// Address of the first two-cell swap.
    pub first_start: TermId,
    /// Address of the second two-cell swap.
    pub second_start: TermId,
    /// Final ordinary-swap array term.
    pub normal_array: TermId,
    /// Final XOR-swap array term.
    pub xor_array: TermId,
    /// Bit width of memory indices.
    pub index_width: u32,
    /// Bit width of memory elements.
    pub element_width: u32,
}

/// A checked refutation of a guarded length-2 XOR-swap round trip.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoByteXorSwapRoundtripCertificate {
    /// The original top-level assertion carrying the guard and final memory
    /// disequality.
    pub assertion: TermId,
    /// Original memory array.
    pub base_array: TermId,
    /// Final memory array after four generated XOR swaps.
    pub final_array: TermId,
    /// First byte-sequence start.
    pub first_start: TermId,
    /// Second byte-sequence start.
    pub second_start: TermId,
    /// Bit width of memory indices.
    pub index_width: u32,
    /// Bit width of memory elements.
    pub element_width: u32,
}

/// Returns a certificate when a top-level assertion demands that two nested
/// ordinary swaps differ from the corresponding two nested XOR swaps.
#[must_use]
pub fn two_cell_xor_swap_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TwoCellXorSwapCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let (lhs, rhs) = match_array_disequality_assertion(arena, assertion)?;
        if let Some(cert) = match_two_stage_swap_identity(arena, assertion, lhs, rhs) {
            return Some(cert);
        }
        if let Some(cert) = match_two_stage_swap_identity(arena, assertion, rhs, lhs) {
            return Some(cert);
        }
    }
    None
}

/// Returns a certificate when a guarded top-level assertion demands that
/// swapping two disjoint length-2 byte ranges twice with generated XOR swaps
/// changes memory.
#[must_use]
pub fn two_byte_xor_swap_roundtrip_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TwoByteXorSwapRoundtripCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let bit = match_negated_bv1_zero_equality(arena, assertion)?;
        let mut operands = Vec::new();
        collect_bv_and_operands(arena, bit, &mut operands);
        let guards = operands
            .iter()
            .filter_map(|&operand| match_two_byte_no_overlap_guard(arena, operand))
            .collect::<Vec<_>>();
        let disequalities = operands
            .iter()
            .filter_map(|&operand| match_array_diseq_bit(arena, operand))
            .collect::<Vec<_>>();

        for (lhs, rhs) in disequalities {
            if let Some(cert) = match_xor_swap_roundtrip(arena, assertion, lhs, rhs, &guards) {
                return Some(cert);
            }
            if let Some(cert) = match_xor_swap_roundtrip(arena, assertion, rhs, lhs, &guards) {
                return Some(cert);
            }
        }
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SwapShape {
    base_array: TermId,
    start: TermId,
    index_width: u32,
    element_width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PairSwapShape {
    base_array: TermId,
    first_index: TermId,
    second_index: TermId,
    index_width: u32,
    element_width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NoOverlapGuard {
    first_start: TermId,
    second_start: TermId,
    index_width: u32,
}

fn match_two_stage_swap_identity(
    arena: &TermArena,
    assertion: TermId,
    normal_array: TermId,
    xor_array: TermId,
) -> Option<TwoCellXorSwapCertificate> {
    let normal_second = match_normal_swap(arena, normal_array)?;
    let xor_second = match_xor_swap(arena, xor_array)?;
    if normal_second.start != xor_second.start
        || normal_second.index_width != xor_second.index_width
        || normal_second.element_width != xor_second.element_width
    {
        return None;
    }

    let normal_first = match_normal_swap(arena, normal_second.base_array)?;
    let xor_first = match_xor_swap(arena, xor_second.base_array)?;
    if normal_first.base_array != xor_first.base_array
        || normal_first.start != xor_first.start
        || normal_first.index_width != xor_first.index_width
        || normal_first.index_width != normal_second.index_width
        || normal_first.element_width != xor_first.element_width
        || normal_first.element_width != normal_second.element_width
        || !array_sort_matches(
            arena,
            normal_first.base_array,
            normal_first.index_width,
            normal_first.element_width,
        )
    {
        return None;
    }

    Some(TwoCellXorSwapCertificate {
        assertion,
        base_array: normal_first.base_array,
        first_start: normal_first.start,
        second_start: normal_second.start,
        normal_array,
        xor_array,
        index_width: normal_first.index_width,
        element_width: normal_first.element_width,
    })
}

fn match_xor_swap_roundtrip(
    arena: &TermArena,
    assertion: TermId,
    base_array: TermId,
    final_array: TermId,
    guards: &[NoOverlapGuard],
) -> Option<TwoByteXorSwapRoundtripCertificate> {
    let fourth = match_xor_swap_pair(arena, final_array)?;
    let third = match_xor_swap_pair(arena, fourth.base_array)?;
    let second = match_xor_swap_pair(arena, third.base_array)?;
    let first = match_xor_swap_pair(arena, second.base_array)?;

    if first.base_array != base_array
        || third.first_index != first.first_index
        || third.second_index != first.second_index
        || fourth.first_index != second.first_index
        || fourth.second_index != second.second_index
        || first.index_width != second.index_width
        || first.index_width != third.index_width
        || first.index_width != fourth.index_width
        || first.element_width != second.element_width
        || first.element_width != third.element_width
        || first.element_width != fourth.element_width
        || !is_plus_const(
            arena,
            second.first_index,
            first.first_index,
            1,
            first.index_width,
        )
        || !is_plus_const(
            arena,
            second.second_index,
            first.second_index,
            1,
            first.index_width,
        )
        || !has_no_overlap_guard(
            guards,
            first.first_index,
            first.second_index,
            first.index_width,
        )
        || !array_sort_matches(arena, base_array, first.index_width, first.element_width)
    {
        return None;
    }

    Some(TwoByteXorSwapRoundtripCertificate {
        assertion,
        base_array,
        final_array,
        first_start: first.first_index,
        second_start: first.second_index,
        index_width: first.index_width,
        element_width: first.element_width,
    })
}

fn match_normal_swap(arena: &TermArena, term: TermId) -> Option<SwapShape> {
    let (after_first, final_index, final_value) = match_store(arena, term)?;
    let (base_array, first_index, first_value) = match_store(arena, after_first)?;
    let Sort::BitVec(index_width) = arena.sort_of(final_index) else {
        return None;
    };
    if index_width == 0
        || !is_plus_const(arena, first_index, final_index, 1, index_width)
        || !is_select(arena, first_value, base_array, final_index)
        || !is_select_plus_const(arena, final_value, base_array, final_index, 1, index_width)
    {
        return None;
    }
    let Sort::BitVec(element_width) = arena.sort_of(first_value) else {
        return None;
    };
    if arena.sort_of(final_value) != Sort::BitVec(element_width)
        || !array_sort_matches(arena, base_array, index_width, element_width)
    {
        return None;
    }
    Some(SwapShape {
        base_array,
        start: final_index,
        index_width,
        element_width,
    })
}

fn match_xor_swap_pair(arena: &TermArena, term: TermId) -> Option<PairSwapShape> {
    let (after_second, final_index, final_value) = match_store(arena, term)?;
    let (after_first, second_index, second_value) = match_store(arena, after_second)?;
    let (base_array, first_index, first_value) = match_store(arena, after_first)?;
    let Sort::BitVec(index_width) = arena.sort_of(first_index) else {
        return None;
    };
    if index_width == 0 || final_index != first_index {
        return None;
    }

    let (lhs, rhs) = match_xor_pair(arena, first_value)?;
    let (x, y) = if is_select(arena, lhs, base_array, first_index)
        && is_select(arena, rhs, base_array, second_index)
    {
        (lhs, rhs)
    } else if is_select(arena, rhs, base_array, first_index)
        && is_select(arena, lhs, base_array, second_index)
    {
        (rhs, lhs)
    } else {
        return None;
    };
    if !is_xor_of(arena, second_value, y, first_value)
        || !is_xor_of(arena, final_value, first_value, second_value)
    {
        return None;
    }

    let Sort::BitVec(element_width) = arena.sort_of(x) else {
        return None;
    };
    if arena.sort_of(second_index) != Sort::BitVec(index_width)
        || arena.sort_of(y) != Sort::BitVec(element_width)
        || arena.sort_of(first_value) != Sort::BitVec(element_width)
        || arena.sort_of(second_value) != Sort::BitVec(element_width)
        || arena.sort_of(final_value) != Sort::BitVec(element_width)
        || !array_sort_matches(arena, base_array, index_width, element_width)
    {
        return None;
    }

    Some(PairSwapShape {
        base_array,
        first_index,
        second_index,
        index_width,
        element_width,
    })
}

fn match_xor_swap(arena: &TermArena, term: TermId) -> Option<SwapShape> {
    let (after_second, final_index, final_value) = match_store(arena, term)?;
    let (after_first, second_index, second_value) = match_store(arena, after_second)?;
    let (base_array, first_index, first_value) = match_store(arena, after_first)?;
    let Sort::BitVec(index_width) = arena.sort_of(first_index) else {
        return None;
    };
    if index_width == 0
        || final_index != first_index
        || !is_plus_const(arena, second_index, first_index, 1, index_width)
    {
        return None;
    }

    let (lhs, rhs) = match_xor_pair(arena, first_value)?;
    let (x, y) = if is_select(arena, lhs, base_array, first_index)
        && is_select_plus_const(arena, rhs, base_array, first_index, 1, index_width)
    {
        (lhs, rhs)
    } else if is_select(arena, rhs, base_array, first_index)
        && is_select_plus_const(arena, lhs, base_array, first_index, 1, index_width)
    {
        (rhs, lhs)
    } else {
        return None;
    };
    if !is_xor_of(arena, second_value, y, first_value)
        || !is_xor_of(arena, final_value, first_value, second_value)
    {
        return None;
    }

    let Sort::BitVec(element_width) = arena.sort_of(x) else {
        return None;
    };
    if arena.sort_of(y) != Sort::BitVec(element_width)
        || arena.sort_of(first_value) != Sort::BitVec(element_width)
        || arena.sort_of(second_value) != Sort::BitVec(element_width)
        || arena.sort_of(final_value) != Sort::BitVec(element_width)
        || !array_sort_matches(arena, base_array, index_width, element_width)
    {
        return None;
    }

    Some(SwapShape {
        base_array,
        start: first_index,
        index_width,
        element_width,
    })
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

fn match_array_disequality_assertion(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let bit = match_negated_bv1_zero_equality(arena, term)?;
    let eq_bit = match_bvnot(arena, bit)?;
    match_array_eq_ite(arena, eq_bit)
}

fn match_array_diseq_bit(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let eq_bit = match_bvnot(arena, term)?;
    match_array_eq_ite(arena, eq_bit)
}

fn match_two_byte_no_overlap_guard(arena: &TermArena, term: TermId) -> Option<NoOverlapGuard> {
    let (first_branch, second_branch) = match_bvor_pair(arena, term)?;
    match_two_byte_no_overlap_branches(arena, first_branch, second_branch)
        .or_else(|| match_two_byte_no_overlap_branches(arena, second_branch, first_branch))
}

fn match_two_byte_no_overlap_branches(
    arena: &TermArena,
    first_branch: TermId,
    second_branch: TermId,
) -> Option<NoOverlapGuard> {
    let first_terms = bvand_terms(arena, first_branch);
    let second_terms = bvand_terms(arena, second_branch);
    let first_cmp = first_terms
        .iter()
        .find_map(|&term| match_not_ult_plus_len(arena, term, 2))?;
    let second_cmp = second_terms
        .iter()
        .find_map(|&term| match_not_ult_plus_len(arena, term, 2))?;

    if first_cmp.lhs != second_cmp.start
        || second_cmp.lhs != first_cmp.start
        || first_cmp.width != second_cmp.width
        || !branch_has_no_wrap(arena, &first_terms, first_cmp.start, first_cmp.width, 2)
        || !branch_has_no_wrap(arena, &first_terms, first_cmp.lhs, first_cmp.width, 2)
        || !branch_has_no_wrap(arena, &second_terms, first_cmp.start, first_cmp.width, 2)
        || !branch_has_no_wrap(arena, &second_terms, first_cmp.lhs, first_cmp.width, 2)
    {
        return None;
    }

    Some(NoOverlapGuard {
        first_start: first_cmp.start,
        second_start: first_cmp.lhs,
        index_width: first_cmp.width,
    })
}

#[derive(Debug, Clone, Copy)]
struct NotUltPlusLen {
    lhs: TermId,
    start: TermId,
    width: u32,
}

fn match_not_ult_plus_len(arena: &TermArena, term: TermId, len: u128) -> Option<NotUltPlusLen> {
    let inner = match_bvnot(arena, term)?;
    let (cond, then_term, else_term) = match_ite(arena, inner)?;
    if !is_bv_const(arena, then_term, 1, 1) || !is_bv_const(arena, else_term, 1, 0) {
        return None;
    }
    let TermNode::App {
        op: Op::BvUlt,
        args,
    } = arena.node(cond)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    let Sort::BitVec(width) = arena.sort_of(*lhs) else {
        return None;
    };
    let start = match_plus_const_base(arena, *rhs, len, width)?;
    Some(NotUltPlusLen {
        lhs: *lhs,
        start,
        width,
    })
}

fn branch_has_no_wrap(
    arena: &TermArena,
    branch_terms: &[TermId],
    start: TermId,
    width: u32,
    len: u128,
) -> bool {
    branch_terms.iter().any(|&term| {
        match_no_wrap_plus_len(arena, term, len).is_some_and(|guard| guard == (start, width))
    })
}

fn match_no_wrap_plus_len(arena: &TermArena, term: TermId, len: u128) -> Option<(TermId, u32)> {
    let inner = match_bvnot(arena, term)?;
    let TermNode::App {
        op: Op::Extract { hi, lo },
        args,
    } = arena.node(inner)
    else {
        return None;
    };
    let [sum] = &**args else {
        return None;
    };
    if hi != lo {
        return None;
    }
    let TermNode::App {
        op: Op::BvAdd,
        args,
    } = arena.node(*sum)
    else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    match_no_wrap_add_side(arena, *lhs, *rhs, len, *hi)
        .or_else(|| match_no_wrap_add_side(arena, *rhs, *lhs, len, *hi))
}

fn match_no_wrap_add_side(
    arena: &TermArena,
    extended_start: TermId,
    extended_len: TermId,
    len: u128,
    width: u32,
) -> Option<(TermId, u32)> {
    let start = match_zero_extend_one(arena, extended_start, width)?;
    if is_extended_const(arena, extended_len, width, len) {
        Some((start, width))
    } else {
        None
    }
}

fn is_extended_const(arena: &TermArena, term: TermId, width: u32, value: u128) -> bool {
    if is_bv_const(arena, term, width + 1, value) {
        return true;
    }
    let TermNode::App {
        op: Op::Concat,
        args,
    } = arena.node(term)
    else {
        return false;
    };
    let [high, low] = &**args else {
        return false;
    };
    is_bv_const(arena, *high, 1, 0) && is_bv_const(arena, *low, width, value)
}

fn match_zero_extend_one(arena: &TermArena, term: TermId, width: u32) -> Option<TermId> {
    let TermNode::App {
        op: Op::Concat,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [high, low] = &**args else {
        return None;
    };
    if is_bv_const(arena, *high, 1, 0) && arena.sort_of(*low) == Sort::BitVec(width) {
        Some(*low)
    } else {
        None
    }
}

fn match_bvor_pair(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    if let TermNode::App { op: Op::BvOr, args } = arena.node(term) {
        let [lhs, rhs] = &**args else {
            return None;
        };
        return Some((*lhs, *rhs));
    }

    let (not_lhs, not_rhs) = match_not_and(arena, term)?;
    Some((match_bvnot(arena, not_lhs)?, match_bvnot(arena, not_rhs)?))
}

fn bvand_terms(arena: &TermArena, term: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    collect_bv_and_operands(arena, term, &mut out);
    out
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

fn match_array_eq_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let (cond, then_term, else_term) = match_ite(arena, term)?;
    if !is_bv_const(arena, then_term, 1, 1) || !is_bv_const(arena, else_term, 1, 0) {
        return None;
    }
    let TermNode::App { op: Op::Eq, args } = arena.node(cond) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if matches!(arena.sort_of(*lhs), Sort::Array { .. })
        && arena.sort_of(*lhs) == arena.sort_of(*rhs)
    {
        Some((*lhs, *rhs))
    } else {
        None
    }
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

fn is_select(arena: &TermArena, term: TermId, array: TermId, index: TermId) -> bool {
    match_select(arena, term)
        .is_some_and(|(found_array, found_index)| found_array == array && found_index == index)
}

fn is_select_plus_const(
    arena: &TermArena,
    term: TermId,
    array: TermId,
    index: TermId,
    offset: u128,
    width: u32,
) -> bool {
    match_select(arena, term).is_some_and(|(found_array, found_index)| {
        found_array == array && is_plus_const(arena, found_index, index, offset, width)
    })
}

fn is_plus_const(arena: &TermArena, term: TermId, base: TermId, offset: u128, width: u32) -> bool {
    match_plus_const_base(arena, term, offset, width) == Some(base)
}

fn match_plus_const_base(
    arena: &TermArena,
    term: TermId,
    offset: u128,
    width: u32,
) -> Option<TermId> {
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
    if is_bv_const(arena, *lhs, width, offset) && arena.sort_of(*rhs) == Sort::BitVec(width) {
        Some(*rhs)
    } else if is_bv_const(arena, *rhs, width, offset) && arena.sort_of(*lhs) == Sort::BitVec(width)
    {
        Some(*lhs)
    } else {
        None
    }
}

fn match_xor_pair(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    if let TermNode::App {
        op: Op::BvXor,
        args,
    } = arena.node(term)
    {
        let [lhs, rhs] = &**args else {
            return None;
        };
        return Some((*lhs, *rhs));
    }

    let (lhs, rhs) = match_bvand(arena, term)?;
    match_encoded_xor_parts(arena, lhs, rhs).or_else(|| match_encoded_xor_parts(arena, rhs, lhs))
}

fn match_encoded_xor_parts(
    arena: &TermArena,
    or_part: TermId,
    nand_part: TermId,
) -> Option<(TermId, TermId)> {
    let (not_lhs, not_rhs) = match_not_and(arena, or_part)?;
    let lhs = match_bvnot(arena, not_lhs)?;
    let rhs = match_bvnot(arena, not_rhs)?;
    let nand = match_not_and(arena, nand_part)?;
    if same_unordered_pair((lhs, rhs), nand) {
        Some((lhs, rhs))
    } else {
        None
    }
}

fn match_not_and(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let inner = match_bvnot(arena, term)?;
    match_bvand(arena, inner)
}

fn match_bvand(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BvAnd,
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

fn match_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [cond, then_term, else_term] = &**args else {
        return None;
    };
    Some((*cond, *then_term, *else_term))
}

fn is_xor_of(arena: &TermArena, term: TermId, lhs: TermId, rhs: TermId) -> bool {
    match_xor_pair(arena, term).is_some_and(|pair| same_unordered_pair(pair, (lhs, rhs)))
}

fn same_unordered_pair(lhs: (TermId, TermId), rhs: (TermId, TermId)) -> bool {
    (lhs.0 == rhs.0 && lhs.1 == rhs.1) || (lhs.0 == rhs.1 && lhs.1 == rhs.0)
}

fn has_no_overlap_guard(
    guards: &[NoOverlapGuard],
    first_start: TermId,
    second_start: TermId,
    index_width: u32,
) -> bool {
    guards.iter().any(|guard| {
        guard.index_width == index_width
            && ((guard.first_start == first_start && guard.second_start == second_start)
                || (guard.first_start == second_start && guard.second_start == first_start))
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
            index: ArraySortKey::BitVec(i),
            element: ArraySortKey::BitVec(e),
        } if i == index_width && e == element_width
    )
}

fn is_bv_const(arena: &TermArena, term: TermId, width: u32, value: u128) -> bool {
    matches!(
        arena.node(term),
        TermNode::BvConst { width: w, value: v } if *w == width && *v == value
    )
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::*;

    #[test]
    fn refutes_two_cell_xor_swap_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__dubreva002ue.smt2"
        );
        let script = parse_script(text).expect("parse dubreva002ue");
        let cert = two_cell_xor_swap_refutation(&script.arena, &script.assertions)
            .expect("two-cell XOR swap refutes dubreva002ue");
        assert_eq!(cert.index_width, 32);
        assert_eq!(cert.element_width, 8);
    }

    #[test]
    fn refutes_two_byte_xor_swap_roundtrip_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__swapmem002ue.smt2"
        );
        let script = parse_script(text).expect("parse swapmem002ue");
        let cert = two_byte_xor_swap_roundtrip_refutation(&script.arena, &script.assertions)
            .expect("two-byte XOR-swap roundtrip refutes swapmem002ue");
        assert_eq!(cert.index_width, 32);
        assert_eq!(cert.element_width, 8);
    }
}
