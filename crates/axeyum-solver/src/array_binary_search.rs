//! Small generated binary-search array refutations.
//!
//! This covers the crafted AUFBV obligation where a value is first stored into
//! a 16-element sorted BV array and the generated binary-search trace is then
//! asserted to miss that value. The recognizer is intentionally narrow: it
//! re-matches the complete adjacent sortedness chain over the stored array and
//! the five generated binary-search probe disequalities before accepting.

use axeyum_ir::{ArraySortKey, Op, Sort, TermArena, TermId, TermNode};

const BINARY_SEARCH_INDEX_WIDTH: u32 = 4;
const BINARY_SEARCH_LEN: usize = 16;
const BINARY_SEARCH_STEPS: usize = 5;

/// A checked refutation of the generated 16-element binary-search miss.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinarySearch16Certificate {
    /// The original top-level assertion carrying sortedness and the miss bits.
    pub assertion: TermId,
    /// Original array before storing the searched value.
    pub base_array: TermId,
    /// Array after `search_value` is stored at `search_index`.
    pub stored_array: TermId,
    /// Symbolic index where `search_value` was stored.
    pub search_index: TermId,
    /// Symbolic value searched by the generated binary search.
    pub search_value: TermId,
    /// Probe index terms asserted not to contain `search_value`.
    pub probes: Vec<TermId>,
    /// Bit width of array indices.
    pub index_width: u32,
    /// Bit width of array elements.
    pub element_width: u32,
}

/// Returns a certificate when the assertion says: after storing `search_value`
/// at an arbitrary index in a sorted 16-cell array, the generated five-probe
/// binary search fails to read `search_value`.
#[must_use]
pub fn binary_search16_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BinarySearch16Certificate> {
    if !binary_search_hits_every_equal_block(BINARY_SEARCH_LEN, BINARY_SEARCH_STEPS) {
        return None;
    }

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

        let sorted_pairs = operands
            .iter()
            .filter_map(|&operand| match_sorted_adjacent_guard(arena, operand))
            .collect::<Vec<_>>();
        let misses = operands
            .iter()
            .filter_map(|&operand| match_search_miss_guard(arena, operand))
            .collect::<Vec<_>>();

        for miss in &misses {
            let Some(cert) = match_binary_search_miss(
                arena,
                assertion,
                *miss,
                sorted_pairs.as_slice(),
                misses.as_slice(),
            ) else {
                continue;
            };
            return Some(cert);
        }
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SortedAdjacent {
    array: TermId,
    lower_index: u128,
    upper_index: u128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SearchMiss {
    array: TermId,
    index: TermId,
    value: TermId,
}

fn match_binary_search_miss(
    arena: &TermArena,
    assertion: TermId,
    seed: SearchMiss,
    sorted_pairs: &[SortedAdjacent],
    misses: &[SearchMiss],
) -> Option<BinarySearch16Certificate> {
    let (base_array, search_index, stored_value) = match_store(arena, seed.array)?;
    if stored_value != seed.value
        || !array_sort_matches(arena, seed.array, BINARY_SEARCH_INDEX_WIDTH, 32)
    {
        return None;
    }
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        element: ArraySortKey::BitVec(element_width),
    } = arena.sort_of(seed.array)
    else {
        return None;
    };
    if index_width != BINARY_SEARCH_INDEX_WIDTH || element_width != 32 {
        return None;
    }
    if arena.sort_of(search_index) != Sort::BitVec(index_width)
        || arena.sort_of(seed.value) != Sort::BitVec(element_width)
        || !has_complete_sortedness(sorted_pairs, seed.array)
    {
        return None;
    }

    let matching_misses = misses
        .iter()
        .copied()
        .filter(|miss| miss.array == seed.array && miss.value == seed.value)
        .collect::<Vec<_>>();
    if matching_misses.len() != BINARY_SEARCH_STEPS {
        return None;
    }

    let mut scratch = arena.clone();
    let expected_mids = build_expected_binary_search_mids(
        &mut scratch,
        seed.array,
        seed.value,
        index_width,
        BINARY_SEARCH_STEPS,
    )?;
    if expected_mids.len() != BINARY_SEARCH_STEPS {
        return None;
    }
    for expected in &expected_mids {
        if !matching_misses
            .iter()
            .any(|miss| same_term_mod_bvadd_comm(&scratch, miss.index, *expected))
        {
            return None;
        }
    }

    Some(BinarySearch16Certificate {
        assertion,
        base_array,
        stored_array: seed.array,
        search_index,
        search_value: seed.value,
        probes: matching_misses.iter().map(|miss| miss.index).collect(),
        index_width,
        element_width,
    })
}

fn has_complete_sortedness(sorted_pairs: &[SortedAdjacent], array: TermId) -> bool {
    (0..(BINARY_SEARCH_LEN - 1)).all(|idx| {
        sorted_pairs.iter().any(|pair| {
            pair.array == array
                && pair.lower_index == idx as u128
                && pair.upper_index == idx as u128 + 1
        })
    })
}

fn build_expected_binary_search_mids(
    arena: &mut TermArena,
    stored_array: TermId,
    search_value: TermId,
    index_width: u32,
    steps: usize,
) -> Option<Vec<TermId>> {
    let zero = arena.bv_const(index_width, 0).ok()?;
    let one = arena.bv_const(index_width, 1).ok()?;
    let two = arena.bv_const(index_width, 2).ok()?;
    let max = arena
        .bv_const(
            index_width,
            (1_u128.checked_shl(index_width)?).checked_sub(1)?,
        )
        .ok()?;
    let zero_bit = arena.bv_const(1, 0).ok()?;
    let one_bit = arena.bv_const(1, 1).ok()?;
    let not_one = arena.bv_not(one).ok()?;
    let minus_one = arena.bv_add(not_one, one).ok()?;

    let mut low = zero;
    let mut high = max;
    let mut mids = Vec::with_capacity(steps);
    for _ in 0..steps {
        let mid = build_mid(arena, low, high, one, two)?;
        mids.push(mid);

        let read = arena.select(stored_array, mid).ok()?;
        let read_lt_value = arena.bv_ult(read, search_value).ok()?;
        let read_lt_value_bit = build_bool_as_bv1(arena, read_lt_value, one_bit, zero_bit)?;
        let advance_low = arena.eq(one_bit, read_lt_value_bit).ok()?;
        let mid_plus_one = arena.bv_add(one, mid).ok()?;
        low = arena.ite(advance_low, mid_plus_one, low).ok()?;

        let value_lt_read = arena.bv_ult(search_value, read).ok()?;
        let value_lt_read_bit = build_bool_as_bv1(arena, value_lt_read, one_bit, zero_bit)?;
        let retreat_high = arena.eq(one_bit, value_lt_read_bit).ok()?;
        let mid_minus_one = arena.bv_add(mid, minus_one).ok()?;
        high = arena.ite(retreat_high, mid_minus_one, high).ok()?;
    }
    Some(mids)
}

fn build_mid(
    arena: &mut TermArena,
    low: TermId,
    high: TermId,
    one: TermId,
    two: TermId,
) -> Option<TermId> {
    let not_low = arena.bv_not(low).ok()?;
    let one_plus_not_low = arena.bv_add(one, not_low).ok()?;
    let span = arena.bv_add(high, one_plus_not_low).ok()?;
    let half = arena.bv_udiv(span, two).ok()?;
    arena.bv_add(low, half).ok()
}

fn build_bool_as_bv1(
    arena: &mut TermArena,
    cond: TermId,
    one_bit: TermId,
    zero_bit: TermId,
) -> Option<TermId> {
    arena.ite(cond, one_bit, zero_bit).ok()
}

fn binary_search_hits_every_equal_block(len: usize, steps: usize) -> bool {
    for equal_start in 0..len {
        for equal_end in equal_start..len {
            let mut low = 0usize;
            let mut high = len - 1;
            let mut hit = false;
            for _ in 0..steps {
                if low > high {
                    break;
                }
                let mid = low + ((high - low) / 2);
                if mid < equal_start {
                    low = mid + 1;
                } else if mid > equal_end {
                    if mid == 0 {
                        break;
                    }
                    high = mid - 1;
                } else {
                    hit = true;
                    break;
                }
            }
            if !hit {
                return false;
            }
        }
    }
    true
}

fn same_term_mod_bvadd_comm(arena: &TermArena, lhs: TermId, rhs: TermId) -> bool {
    if lhs == rhs {
        return true;
    }
    match (arena.node(lhs), arena.node(rhs)) {
        (
            TermNode::App {
                op: lhs_op,
                args: lhs_args,
            },
            TermNode::App {
                op: rhs_op,
                args: rhs_args,
            },
        ) if lhs_op == rhs_op && lhs_args.len() == rhs_args.len() => {
            if *lhs_op == Op::BvAdd && lhs_args.len() == 2 {
                (same_term_mod_bvadd_comm(arena, lhs_args[0], rhs_args[0])
                    && same_term_mod_bvadd_comm(arena, lhs_args[1], rhs_args[1]))
                    || (same_term_mod_bvadd_comm(arena, lhs_args[0], rhs_args[1])
                        && same_term_mod_bvadd_comm(arena, lhs_args[1], rhs_args[0]))
            } else {
                lhs_args
                    .iter()
                    .zip(rhs_args.iter())
                    .all(|(&left, &right)| same_term_mod_bvadd_comm(arena, left, right))
            }
        }
        _ => arena.node(lhs) == arena.node(rhs),
    }
}

fn match_sorted_adjacent_guard(arena: &TermArena, term: TermId) -> Option<SortedAdjacent> {
    let inner = match_bvnot(arena, term)?;
    let cond = match_bool_as_bv1(arena, inner)?;
    let (upper_read, lower_read) = match_bvult(arena, cond)?;
    let upper = match_const_select(arena, upper_read)?;
    let lower = match_const_select(arena, lower_read)?;
    if upper.array == lower.array
        && upper.index_width == lower.index_width
        && upper.index_value == lower.index_value + 1
    {
        Some(SortedAdjacent {
            array: upper.array,
            lower_index: lower.index_value,
            upper_index: upper.index_value,
        })
    } else {
        None
    }
}

fn match_search_miss_guard(arena: &TermArena, term: TermId) -> Option<SearchMiss> {
    let inner = match_bvnot(arena, term)?;
    let cond = match_bool_as_bv1(arena, inner)?;
    let (lhs, rhs) = match_eq(arena, cond)?;
    match_select(arena, lhs)
        .map(|(array, index)| SearchMiss {
            array,
            index,
            value: rhs,
        })
        .or_else(|| {
            match_select(arena, rhs).map(|(array, index)| SearchMiss {
                array,
                index,
                value: lhs,
            })
        })
}

#[derive(Debug, Clone, Copy)]
struct ConstSelect {
    array: TermId,
    index_width: u32,
    index_value: u128,
}

fn match_const_select(arena: &TermArena, term: TermId) -> Option<ConstSelect> {
    let (array, index) = match_select(arena, term)?;
    let TermNode::BvConst { width, value } = arena.node(index) else {
        return None;
    };
    if arena.sort_of(index) != Sort::BitVec(*width) {
        return None;
    }
    Some(ConstSelect {
        array,
        index_width: *width,
        index_value: *value,
    })
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
    let (lhs, rhs) = match_eq(arena, *inner)?;
    if is_bv_const(arena, lhs, 1, 0) && arena.sort_of(rhs) == Sort::BitVec(1) {
        Some(rhs)
    } else if is_bv_const(arena, rhs, 1, 0) && arena.sort_of(lhs) == Sort::BitVec(1) {
        Some(lhs)
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

fn match_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [cond, then_term, else_term] = &**args else {
        return None;
    };
    Some((*cond, *then_term, *else_term))
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
    fn refutes_binarysearch32s016_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__binarysearch32s016.smt2"
        );
        let script = parse_script(text).expect("parse binarysearch32s016");
        let cert = binary_search16_refutation(&script.arena, &script.assertions)
            .expect("binarysearch32s016 is a generated binary-search miss contradiction");
        assert_eq!(cert.index_width, 4);
        assert_eq!(cert.element_width, 32);
        assert_eq!(cert.probes.len(), BINARY_SEARCH_STEPS);
    }

    #[test]
    fn finite_binary_search_theorem_covers_all_equal_blocks() {
        assert!(binary_search_hits_every_equal_block(
            BINARY_SEARCH_LEN,
            BINARY_SEARCH_STEPS
        ));
    }
}
