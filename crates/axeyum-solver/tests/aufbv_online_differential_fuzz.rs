//! Deterministic differential gate for canonical online array+EUF+BV combination.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_auto, check_qf_aufbv_online_cdclt,
    check_with_arrays_and_functions,
};
#[cfg(feature = "z3")]
use z3::ast::{Array, BV, Bool, Dynamic};
#[cfg(feature = "z3")]
use z3::{FuncDecl, SatResult, Solver, Sort as Z3Sort};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn verdict(result: &CheckResult) -> Verdict {
    match result {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

#[derive(Debug, Clone, Copy)]
enum ScalarKind {
    Bool,
    Bv3,
}

impl ScalarKind {
    fn ir_sort(self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::Bv3 => Sort::BitVec(3),
        }
    }

    fn ir_var(self, arena: &mut TermArena, name: &str) -> TermId {
        match self {
            Self::Bool => arena.bool_var(name).unwrap(),
            Self::Bv3 => arena.bv_var(name, 3).unwrap(),
        }
    }

    fn ir_value(self, arena: &mut TermArena, one: bool) -> TermId {
        match self {
            Self::Bool => arena.bool_const(one),
            Self::Bv3 => arena.bv_const(3, u128::from(one)).unwrap(),
        }
    }

    #[cfg(feature = "z3")]
    fn z3_sort(self) -> Z3Sort {
        match self {
            Self::Bool => Z3Sort::bool(),
            Self::Bv3 => Z3Sort::bitvector(3),
        }
    }

    #[cfg(feature = "z3")]
    fn z3_var(self, name: &str) -> Dynamic {
        match self {
            Self::Bool => Dynamic::from_ast(&Bool::new_const(name)),
            Self::Bv3 => Dynamic::from_ast(&BV::new_const(name, 3)),
        }
    }

    #[cfg(feature = "z3")]
    fn z3_value(self, one: bool) -> Dynamic {
        match self {
            Self::Bool => Dynamic::from_ast(&Bool::from_bool(one)),
            Self::Bv3 => Dynamic::from_ast(&BV::from_u64(u64::from(one), 3)),
        }
    }
}

fn finite_scalar_shape(seed: u64) -> (ScalarKind, ScalarKind) {
    match (seed / 12) % 3 {
        0 => (ScalarKind::Bool, ScalarKind::Bool),
        1 => (ScalarKind::Bool, ScalarKind::Bv3),
        _ => (ScalarKind::Bv3, ScalarKind::Bool),
    }
}

fn finite_scalar_expected(seed: u64) -> Verdict {
    match seed % 12 {
        1 | 3 | 5 | 7 | 9 => Verdict::Sat,
        _ => Verdict::Unsat,
    }
}

fn build_finite_scalar_array_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let (index_kind, element_kind) = finite_scalar_shape(seed);
    let array = arena
        .array_var_with_sorts("finite_a", index_kind.ir_sort(), element_kind.ir_sort())
        .unwrap();
    let other = arena
        .array_var_with_sorts("finite_b", index_kind.ir_sort(), element_kind.ir_sort())
        .unwrap();
    let third = arena
        .array_var_with_sorts("finite_c", index_kind.ir_sort(), element_kind.ir_sort())
        .unwrap();
    let x = index_kind.ir_var(arena, "finite_x");
    let y = index_kind.ir_var(arena, "finite_y");
    let index_zero = index_kind.ir_value(arena, false);
    let index_one = index_kind.ir_value(arena, true);
    let value_zero = element_kind.ir_value(arena, false);
    let value_one = element_kind.ir_value(arena, true);
    let read_x = arena.select(array, x).unwrap();
    let read_y = arena.select(array, y).unwrap();
    let other_read_x = arena.select(other, x).unwrap();
    let third_read_one = arena.select(third, index_one).unwrap();
    let same_indices = arena.eq(x, y).unwrap();
    let different_indices = arena.not(same_indices).unwrap();
    let same_reads = arena.eq(read_x, read_y).unwrap();
    let different_reads = arena.not(same_reads).unwrap();
    let read_x_zero = arena.eq(read_x, value_zero).unwrap();
    let stored_source_is_one = arena.eq(read_x, value_one).unwrap();
    let other_index_is_one = arena.eq(read_y, value_one).unwrap();
    let stored = arena.store(array, x, value_zero).unwrap();
    let stored_read_y = arena.select(stored, y).unwrap();
    let stored_read_y_zero = arena.eq(stored_read_y, value_zero).unwrap();
    let stored_read_y_not_zero = arena.not(stored_read_y_zero).unwrap();
    let stored_read_y_one = arena.eq(stored_read_y, value_one).unwrap();
    let arrays_equal = arena.eq(array, other).unwrap();
    let arrays_different = arena.not(arrays_equal).unwrap();
    let other_third_equal = arena.eq(other, third).unwrap();
    let array_third_equal = arena.eq(array, third).unwrap();
    let array_third_different = arena.not(array_third_equal).unwrap();
    let cross_reads_equal = arena.eq(read_x, other_read_x).unwrap();
    let cross_reads_different = arena.not(cross_reads_equal).unwrap();
    let stored_equals_array = arena.eq(stored, array).unwrap();
    let stored_differs_array = arena.not(stored_equals_array).unwrap();
    let constant = arena
        .const_array_with_index_sort(index_kind.ir_sort(), value_zero)
        .unwrap();
    let constant_read_one = arena.select(constant, index_one).unwrap();
    let constant_read_is_zero = arena.eq(constant_read_one, value_zero).unwrap();
    let constant_read_not_zero = arena.not(constant_read_is_zero).unwrap();
    let array_read_zero = arena.select(array, index_zero).unwrap();
    let array_read_zero_is_zero = arena.eq(array_read_zero, value_zero).unwrap();
    let read_x_not_zero = arena.not(read_x_zero).unwrap();
    let array_or_index_equal = arena.or(arrays_equal, same_indices).unwrap();

    match seed % 12 {
        0 => vec![same_indices, different_reads],
        1 => vec![different_indices, read_x_zero, other_index_is_one],
        2 => vec![same_indices, stored_read_y_not_zero],
        3 => vec![different_indices, stored_read_y_one],
        4 => vec![arrays_equal, cross_reads_different],
        5 => vec![arrays_different, cross_reads_equal],
        6 => vec![
            arrays_equal,
            other_third_equal,
            array_third_different,
            read_x_zero,
        ],
        7 => vec![
            arrays_equal,
            other_third_equal,
            array_read_zero_is_zero,
            arena.eq(third_read_one, value_one).unwrap(),
        ],
        8 => vec![stored_equals_array, read_x_not_zero],
        9 => vec![stored_differs_array, stored_source_is_one],
        10 => vec![constant_read_not_zero, read_x_zero],
        _ => vec![
            array_or_index_equal,
            arrays_different,
            different_indices,
            read_x_zero,
        ],
    }
}

fn assert_sat_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult, seed: u64) {
    if let CheckResult::Sat(model) = result {
        let assignment = model.to_assignment();
        assert!(
            assertions
                .iter()
                .all(|&term| eval(arena, term, &assignment) == Ok(Value::Bool(true))),
            "finite scalar SAT model failed replay at seed {seed}: {model:?}"
        );
    }
}

#[cfg(feature = "z3")]
fn z3_finite_scalar_verdict(seed: u64) -> Verdict {
    let (index_kind, element_kind) = finite_scalar_shape(seed);
    let index_sort = index_kind.z3_sort();
    let element_sort = element_kind.z3_sort();
    let array = Array::new_const("finite_a", &index_sort, &element_sort);
    let other = Array::new_const("finite_b", &index_sort, &element_sort);
    let third = Array::new_const("finite_c", &index_sort, &element_sort);
    let x = index_kind.z3_var("finite_x");
    let y = index_kind.z3_var("finite_y");
    let index_zero = index_kind.z3_value(false);
    let index_one = index_kind.z3_value(true);
    let value_zero = element_kind.z3_value(false);
    let value_one = element_kind.z3_value(true);
    let read_x = array.select(&x);
    let read_y = array.select(&y);
    let other_read_x = other.select(&x);
    let third_read_one = third.select(&index_one);
    let same_indices = x.eq(&y);
    let different_indices = same_indices.not();
    let different_reads = read_x.eq(&read_y).not();
    let read_x_zero = read_x.eq(&value_zero);
    let stored_source_is_one = read_x.eq(&value_one);
    let other_index_is_one = read_y.eq(&value_one);
    let stored = array.store(&x, &value_zero);
    let stored_read_y = stored.select(&y);
    let stored_read_y_not_zero = stored_read_y.eq(&value_zero).not();
    let stored_read_y_one = stored_read_y.eq(&value_one);
    let arrays_equal = array.eq(&other);
    let arrays_different = arrays_equal.not();
    let other_third_equal = other.eq(&third);
    let array_third_different = array.eq(&third).not();
    let cross_reads_equal = read_x.eq(&other_read_x);
    let cross_reads_different = cross_reads_equal.not();
    let stored_equals_array = stored.eq(&array);
    let stored_differs_array = stored_equals_array.not();
    let constant = Array::const_array(&index_sort, &value_zero);
    let constant_read_not_zero = constant.select(&index_one).eq(&value_zero).not();

    let assertions = match seed % 12 {
        0 => vec![same_indices, different_reads],
        1 => vec![different_indices, read_x_zero, other_index_is_one],
        2 => vec![same_indices, stored_read_y_not_zero],
        3 => vec![different_indices, stored_read_y_one],
        4 => vec![arrays_equal, cross_reads_different],
        5 => vec![arrays_different, cross_reads_equal],
        6 => vec![
            arrays_equal,
            other_third_equal,
            array_third_different,
            read_x_zero,
        ],
        7 => vec![
            arrays_equal,
            other_third_equal,
            array.select(&index_zero).eq(&value_zero),
            third_read_one.eq(&value_one),
        ],
        8 => vec![stored_equals_array, read_x_zero.not()],
        9 => vec![stored_differs_array, stored_source_is_one],
        10 => vec![constant_read_not_zero, read_x_zero],
        _ => vec![
            Bool::or(&[arrays_equal, same_indices]),
            arrays_different,
            different_indices,
            read_x_zero,
        ],
    };
    let solver = Solver::new();
    for assertion in assertions {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

fn build_cross_equality_case(
    case: u64,
    arena: &mut TermArena,
    width: u32,
    array: TermId,
    other_array: TermId,
    stored: TermId,
) -> Vec<TermId> {
    let third_array = arena.array_var("c", width, width).unwrap();
    let fourth_array = arena.array_var("d", width, width).unwrap();
    let arrays_equal = arena.eq(array, other_array).unwrap();
    let other_equals_third = arena.eq(other_array, third_array).unwrap();
    let array_equals_third = arena.eq(array, third_array).unwrap();
    match case {
        16 => vec![
            arrays_equal,
            other_equals_third,
            arena.not(array_equals_third).unwrap(),
        ],
        17 => {
            let third_equals_fourth = arena.eq(third_array, fourth_array).unwrap();
            vec![arrays_equal, arena.not(third_equals_fourth).unwrap()]
        }
        18 => {
            let stored_equals_other = arena.eq(stored, other_array).unwrap();
            let stored_equals_third = arena.eq(stored, third_array).unwrap();
            vec![
                stored_equals_other,
                other_equals_third,
                arena.not(stored_equals_third).unwrap(),
            ]
        }
        _ => {
            let first_index = arena.bv_const(width, 1).unwrap();
            let second_index = arena.bv_const(width, 2).unwrap();
            let first_value = arena.bv_const(width, 3).unwrap();
            let second_value = arena.bv_const(width, 4).unwrap();
            let first_read = arena.select(array, first_index).unwrap();
            let second_read = arena.select(third_array, second_index).unwrap();
            vec![
                arrays_equal,
                other_equals_third,
                arena.eq(first_read, first_value).unwrap(),
                arena.eq(second_read, second_value).unwrap(),
            ]
        }
    }
}

#[cfg(feature = "z3")]
fn z3_cross_equality_case(
    case: u64,
    width: u32,
    array: &Array,
    other_array: &Array,
    third_array: &Array,
    fourth_array: &Array,
    stored: &Array,
) -> Vec<Bool> {
    let arrays_equal = array.eq(other_array);
    let other_equals_third = other_array.eq(third_array);
    match case {
        16 => vec![
            arrays_equal,
            other_equals_third,
            array.eq(third_array).not(),
        ],
        17 => vec![arrays_equal, third_array.eq(fourth_array).not()],
        18 => vec![
            stored.eq(other_array),
            other_equals_third,
            stored.eq(third_array).not(),
        ],
        _ => {
            let first_index = BV::from_u64(1, width);
            let second_index = BV::from_u64(2, width);
            let first_value = BV::from_u64(3, width);
            let second_value = BV::from_u64(4, width);
            vec![
                arrays_equal,
                other_equals_third,
                array.select(&first_index).as_bv().unwrap().eq(first_value),
                third_array
                    .select(&second_index)
                    .as_bv()
                    .unwrap()
                    .eq(second_value),
            ]
        }
    }
}

fn build_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let width = 3 + u32::try_from(seed % 2).unwrap();
    let modulus = 1u128 << width;
    let first_value = u128::from(seed % u64::try_from(modulus).unwrap());
    let second_value = (first_value + 1) % modulus;
    let array = arena.array_var("a", width, width).unwrap();
    let other_array = arena.array_var("b", width, width).unwrap();
    let function = arena
        .declare_fun("f", &[Sort::BitVec(width)], Sort::BitVec(width))
        .unwrap();
    let x = arena.bv_var("x", width).unwrap();
    let y = arena.bv_var("y", width).unwrap();
    let offset = arena.bv_const(width, 1).unwrap();
    let first = arena.bv_const(width, first_value).unwrap();
    let second = arena.bv_const(width, second_value).unwrap();
    let read_x = arena.select(array, x).unwrap();
    let read_y = arena.select(array, y).unwrap();
    let other_read_x = arena.select(other_array, x).unwrap();
    let f_read_x = arena.apply(function, &[read_x]).unwrap();
    let f_read_y = arena.apply(function, &[read_y]).unwrap();
    let nested_x = arena.apply(function, &[f_read_x]).unwrap();
    let nested_y = arena.apply(function, &[f_read_y]).unwrap();
    let f_x = arena.apply(function, &[x]).unwrap();
    let f_y = arena.apply(function, &[y]).unwrap();
    let read_f_x = arena.select(array, f_x).unwrap();
    let other_read_f_y = arena.select(other_array, f_y).unwrap();
    let same_xy = arena.eq(x, y).unwrap();
    let different_xy = arena.not(same_xy).unwrap();
    let same_reads = arena.eq(read_x, read_y).unwrap();
    let different_reads = arena.not(same_reads).unwrap();
    let read_x_first = arena.eq(read_x, first).unwrap();
    let read_y_second = arena.eq(read_y, second).unwrap();
    let f_x_first = arena.eq(f_read_x, first).unwrap();
    let f_y_second = arena.eq(f_read_y, second).unwrap();
    let transformed_x = if seed & 1 == 0 {
        arena.bv_add(x, offset).unwrap()
    } else {
        arena.bv_xor(x, offset).unwrap()
    };
    let transformed_y = if seed & 1 == 0 {
        arena.bv_add(y, offset).unwrap()
    } else {
        arena.bv_xor(y, offset).unwrap()
    };
    let same_transformed = arena.eq(transformed_x, transformed_y).unwrap();
    let stored = arena.store(array, x, first).unwrap();
    let stored_read_y = arena.select(stored, y).unwrap();
    let stored_read_is_first = arena.eq(stored_read_y, first).unwrap();
    let stored_read_is_not_first = arena.not(stored_read_is_first).unwrap();
    let same_nested = arena.eq(nested_x, nested_y).unwrap();
    let different_nested = arena.not(same_nested).unwrap();
    let arrays_equal = arena.eq(array, other_array).unwrap();
    let arrays_different = arena.not(arrays_equal).unwrap();
    let cross_reads_equal = arena.eq(read_x, other_read_x).unwrap();
    let cross_reads_different = arena.not(cross_reads_equal).unwrap();
    let uf_cross_reads_equal = arena.eq(read_f_x, other_read_f_y).unwrap();
    let uf_cross_reads_different = arena.not(uf_cross_reads_equal).unwrap();
    let stored_equals_base = arena.eq(stored, array).unwrap();
    let stored_equals_other = arena.eq(stored, other_array).unwrap();
    let stored_self_equal = arena.eq(stored, stored).unwrap();
    let stored_self_different = arena.not(stored_self_equal).unwrap();

    match seed % 20 {
        0 => vec![same_xy, different_reads],
        1 => vec![different_xy, read_x_first, read_y_second],
        2 => vec![same_xy, arena.bv_ult(f_read_x, f_read_y).unwrap()],
        3 => vec![
            different_xy,
            read_x_first,
            read_y_second,
            f_x_first,
            f_y_second,
        ],
        4 => vec![same_transformed, stored_read_is_not_first],
        5 => vec![different_xy, arena.eq(stored_read_y, second).unwrap()],
        6 => vec![
            arena.or(same_xy, same_reads).unwrap(),
            different_xy,
            different_reads,
        ],
        7 => vec![same_xy, different_nested],
        8 => vec![arrays_equal, cross_reads_different],
        9 => vec![arrays_different],
        10 => vec![stored_equals_base, arena.not(read_x_first).unwrap()],
        11 => vec![arrays_equal, same_xy, uf_cross_reads_different],
        12 => vec![
            arena.or(arrays_equal, same_xy).unwrap(),
            arrays_different,
            different_xy,
        ],
        13 => vec![stored_equals_other],
        14 => vec![stored_self_different],
        15 => vec![arrays_different, cross_reads_equal],
        case => build_cross_equality_case(case, arena, width, array, other_array, stored),
    }
}

fn build_structural_store_parent_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let width = 3;
    let left_array = arena.array_var("store_parent_a", width, width).unwrap();
    let peer_array = arena.array_var("store_parent_b", width, width).unwrap();
    let transitive_array = arena.array_var("store_parent_c", width, width).unwrap();
    let function = arena
        .declare_fun(
            "store_parent_f",
            &[Sort::BitVec(width)],
            Sort::BitVec(width),
        )
        .unwrap();
    let write_left = arena.bv_var("store_parent_x", width).unwrap();
    let write_peer = arena.bv_var("store_parent_y", width).unwrap();
    let read_index = arena.bv_var("store_parent_k", width).unwrap();
    let value = arena.bv_var("store_parent_value", width).unwrap();
    let other_value = arena.bv_var("store_parent_other_value", width).unwrap();
    let left_function_index = arena.apply(function, &[write_left]).unwrap();
    let peer_function_index = arena.apply(function, &[write_peer]).unwrap();
    let left_store = arena.store(left_array, write_left, value).unwrap();
    let peer_store_distinct = arena.store(peer_array, write_peer, other_value).unwrap();
    let peer_store_matched = arena.store(peer_array, write_left, value).unwrap();
    let transitive_store_matched = arena.store(transitive_array, write_left, value).unwrap();
    let left_store_function_index = arena.store(left_array, left_function_index, value).unwrap();
    let peer_store_function_index = arena
        .store(peer_array, peer_function_index, other_value)
        .unwrap();
    let left_read = arena.select(left_store, read_index).unwrap();
    let peer_distinct_read = arena.select(peer_store_distinct, read_index).unwrap();
    let peer_matched_read = arena.select(peer_store_matched, read_index).unwrap();
    let transitive_matched_read = arena.select(transitive_store_matched, read_index).unwrap();
    let left_function_read = arena.select(left_store_function_index, read_index).unwrap();
    let peer_function_read = arena.select(peer_store_function_index, read_index).unwrap();
    let left_index_read = arena.select(left_store, write_left).unwrap();
    let peer_index_read = arena.select(left_store, write_peer).unwrap();
    let left_peer_equal = arena.eq(left_array, peer_array).unwrap();
    let peer_transitive_equal = arena.eq(peer_array, transitive_array).unwrap();
    let left_transitive_equal = arena.eq(left_array, transitive_array).unwrap();
    let left_peer_distinct = arena.not(left_peer_equal).unwrap();
    let same_indices = arena.eq(write_left, write_peer).unwrap();
    let same_values = arena.eq(value, other_value).unwrap();
    let store_reads_equal = arena.eq(left_read, peer_distinct_read).unwrap();
    let store_reads_differ = arena.not(store_reads_equal).unwrap();
    let shared_reads_equal = arena.eq(left_read, peer_matched_read).unwrap();
    let shared_reads_differ = arena.not(shared_reads_equal).unwrap();
    let transitive_reads_equal = arena.eq(left_read, transitive_matched_read).unwrap();
    let transitive_reads_differ = arena.not(transitive_reads_equal).unwrap();
    let uf_reads_equal = arena.eq(left_function_read, peer_function_read).unwrap();
    let uf_reads_differ = arena.not(uf_reads_equal).unwrap();
    let same_parent_reads_equal = arena.eq(left_index_read, peer_index_read).unwrap();
    let same_parent_reads_differ = arena.not(same_parent_reads_equal).unwrap();
    let branch = arena.or(left_peer_equal, left_transitive_equal).unwrap();

    match seed % 8 {
        0 => vec![
            left_peer_equal,
            same_indices,
            same_values,
            store_reads_differ,
        ],
        1 => vec![same_indices, same_parent_reads_differ],
        2 => vec![store_reads_differ],
        3 => vec![branch, shared_reads_differ],
        4 => vec![
            left_peer_equal,
            peer_transitive_equal,
            transitive_reads_differ,
        ],
        5 => vec![left_peer_equal, same_indices, same_values, uf_reads_differ],
        6 => vec![
            left_peer_equal,
            same_indices,
            same_values,
            store_reads_equal,
        ],
        _ => vec![left_peer_distinct, shared_reads_equal],
    }
}

fn build_dynamic_row_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let width = 3;
    let base_array = arena.array_var("dynamic_row_a", width, width).unwrap();
    let row_function = arena
        .declare_fun("dynamic_row_f", &[Sort::BitVec(width)], Sort::BitVec(width))
        .unwrap();
    let write_index = arena.bv_var("dynamic_row_x", width).unwrap();
    let peer_index = arena.bv_var("dynamic_row_y", width).unwrap();
    let read_index = arena.bv_var("dynamic_row_k", width).unwrap();
    let stored_value = arena.bv_var("dynamic_row_v", width).unwrap();
    let shadow_value = arena.bv_var("dynamic_row_w", width).unwrap();
    let fallback = arena.bool_var("dynamic_row_guard").unwrap();
    let function_write = arena.apply(row_function, &[write_index]).unwrap();
    let function_peer = arena.apply(row_function, &[peer_index]).unwrap();
    let first_store = arena.store(base_array, write_index, stored_value).unwrap();
    let nested_store = arena.store(first_store, peer_index, shadow_value).unwrap();
    let shadow_store = arena.store(first_store, write_index, shadow_value).unwrap();
    let function_store = arena
        .store(base_array, function_write, stored_value)
        .unwrap();
    let hit_read = arena.select(first_store, write_index).unwrap();
    let peer_read = arena.select(first_store, peer_index).unwrap();
    let base_peer_read = arena.select(base_array, peer_index).unwrap();
    let nested_read = arena.select(nested_store, read_index).unwrap();
    let base_read = arena.select(base_array, read_index).unwrap();
    let function_read = arena.select(function_store, function_peer).unwrap();
    let shadow_read = arena.select(shadow_store, write_index).unwrap();
    let same_indices = arena.eq(write_index, peer_index).unwrap();
    let different_indices = arena.not(same_indices).unwrap();
    let read_hits_write = arena.eq(read_index, write_index).unwrap();
    let read_misses_write = arena.not(read_hits_write).unwrap();
    let read_hits_peer = arena.eq(read_index, peer_index).unwrap();
    let read_misses_peer = arena.not(read_hits_peer).unwrap();
    let hit_is_value = arena.eq(hit_read, stored_value).unwrap();
    let bad_hit = arena.not(hit_is_value).unwrap();
    let peer_is_base = arena.eq(peer_read, base_peer_read).unwrap();
    let bad_miss = arena.not(peer_is_base).unwrap();
    let base_peer_is_value = arena.eq(base_peer_read, stored_value).unwrap();
    let base_peer_differs = arena.not(base_peer_is_value).unwrap();
    let peer_is_value = arena.eq(peer_read, stored_value).unwrap();
    let repairable_choice = arena.or(peer_is_value, fallback).unwrap();
    let nested_is_base = arena.eq(nested_read, base_read).unwrap();
    let bad_nested_miss = arena.not(nested_is_base).unwrap();
    let function_is_value = arena.eq(function_read, stored_value).unwrap();
    let bad_function_hit = arena.not(function_is_value).unwrap();
    let shadow_is_value = arena.eq(shadow_read, shadow_value).unwrap();
    let bad_shadow_hit = arena.not(shadow_is_value).unwrap();
    let branch = arena.or(same_indices, fallback).unwrap();
    let peer_differs_from_value = arena.not(peer_is_value).unwrap();

    match seed % 8 {
        0 => vec![bad_hit],
        1 => vec![different_indices, bad_miss],
        2 => vec![different_indices, base_peer_differs, repairable_choice],
        3 => vec![read_misses_write, read_misses_peer, bad_nested_miss],
        4 => vec![different_indices, peer_is_base],
        5 => vec![same_indices, bad_function_hit],
        6 => vec![bad_shadow_hit],
        _ => vec![branch, peer_differs_from_value],
    }
}

fn build_dynamic_interface_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let width = 3;
    let array_a = arena.array_var("dynamic_iface_a", width, width).unwrap();
    let array_b = arena.array_var("dynamic_iface_b", width, width).unwrap();
    let array_c = arena.array_var("dynamic_iface_c", width, width).unwrap();
    let function_f = arena
        .declare_fun(
            "dynamic_iface_f",
            &[Sort::BitVec(width)],
            Sort::BitVec(width),
        )
        .unwrap();
    let function_g = arena
        .declare_fun(
            "dynamic_iface_g",
            &[Sort::BitVec(width)],
            Sort::BitVec(width),
        )
        .unwrap();
    let x = arena.bv_var("dynamic_iface_x", width).unwrap();
    let y = arena.bv_var("dynamic_iface_y", width).unwrap();
    let k = arena.bv_var("dynamic_iface_k", width).unwrap();
    let value = arena.bv_var("dynamic_iface_v", width).unwrap();
    let fallback = arena.bool_var("dynamic_iface_guard").unwrap();
    let fx = arena.apply(function_f, &[x]).unwrap();
    let fy = arena.apply(function_f, &[y]).unwrap();
    let gfx = arena.apply(function_g, &[fx]).unwrap();
    let gfy = arena.apply(function_g, &[fy]).unwrap();
    let a_at_x = arena.select(array_a, x).unwrap();
    let a_at_y = arena.select(array_a, y).unwrap();
    let a_at_k = arena.select(array_a, k).unwrap();
    let b_at_k = arena.select(array_b, k).unwrap();
    let store_a = arena.store(array_a, x, value).unwrap();
    let store_b = arena.store(array_b, y, value).unwrap();
    let updated_value_at_k = arena.select(store_a, k).unwrap();
    let peer_value_at_k = arena.select(store_b, k).unwrap();
    let same_xy = arena.eq(x, y).unwrap();
    let f_strict = arena.bv_ult(fx, fy).unwrap();
    let g_strict = arena.bv_ult(gfx, gfy).unwrap();
    let nested_choice = arena.or(f_strict, fallback).unwrap();
    let same_base_reads = arena.eq(a_at_x, a_at_y).unwrap();
    let different_base_reads = arena.not(same_base_reads).unwrap();
    let a_eq_b = arena.eq(array_a, array_b).unwrap();
    let a_eq_c = arena.eq(array_a, array_c).unwrap();
    let parent_choice = arena.or(a_eq_b, a_eq_c).unwrap();
    let same_parent_reads = arena.eq(a_at_k, b_at_k).unwrap();
    let different_parent_reads = arena.not(same_parent_reads).unwrap();
    let same_store_reads = arena.eq(updated_value_at_k, peer_value_at_k).unwrap();
    let different_store_reads = arena.not(same_store_reads).unwrap();
    let store_equals_base = arena.eq(store_a, array_a).unwrap();
    let base_read_at_x = arena.select(array_a, x).unwrap();
    let base_read_is_value = arena.eq(base_read_at_x, value).unwrap();
    let base_read_differs = arena.not(base_read_is_value).unwrap();
    let read_strict = arena.bv_ult(a_at_x, a_at_y).unwrap();
    let read_choice = arena.or(read_strict, fallback).unwrap();
    let f_of_a_at_x = arena.apply(function_f, &[a_at_x]).unwrap();
    let f_of_a_at_y = arena.apply(function_f, &[a_at_y]).unwrap();
    let f_read_strict = arena.bv_ult(f_of_a_at_x, f_of_a_at_y).unwrap();
    let replay_choice = arena.or(f_strict, fallback).unwrap();

    match seed % 8 {
        0 => vec![same_xy, f_strict],
        1 => vec![same_xy, nested_choice, g_strict],
        2 => vec![same_xy, different_base_reads],
        3 => vec![parent_choice, different_parent_reads],
        4 => vec![a_eq_b, same_xy, different_store_reads],
        5 => vec![store_equals_base, base_read_differs],
        6 => vec![same_xy, read_choice, f_read_strict],
        _ => vec![same_xy, replay_choice],
    }
}

#[cfg(feature = "z3")]
fn z3_verdict(seed: u64) -> Verdict {
    let width = 3 + u32::try_from(seed % 2).unwrap();
    let modulus = 1u128 << width;
    let first_value = u128::from(seed % u64::try_from(modulus).unwrap());
    let second_value = (first_value + 1) % modulus;
    let bv_sort = Z3Sort::bitvector(width);
    let array = Array::new_const("a", &bv_sort, &bv_sort);
    let function = FuncDecl::new("f", &[&bv_sort], &bv_sort);
    let x = BV::new_const("x", width);
    let y = BV::new_const("y", width);
    let offset = BV::from_u64(1, width);
    let first = BV::from_u64(u64::try_from(first_value).unwrap(), width);
    let second = BV::from_u64(u64::try_from(second_value).unwrap(), width);
    let other_array = Array::new_const("b", &bv_sort, &bv_sort);
    let third_array = Array::new_const("c", &bv_sort, &bv_sort);
    let fourth_array = Array::new_const("d", &bv_sort, &bv_sort);
    let read_x = array.select(&x).as_bv().unwrap();
    let read_y = array.select(&y).as_bv().unwrap();
    let other_read_x = other_array.select(&x).as_bv().unwrap();
    let f_read_x = function.apply(&[&read_x]).as_bv().unwrap();
    let f_read_y = function.apply(&[&read_y]).as_bv().unwrap();
    let nested_x = function.apply(&[&f_read_x]).as_bv().unwrap();
    let nested_y = function.apply(&[&f_read_y]).as_bv().unwrap();
    let f_x = function.apply(&[&x]).as_bv().unwrap();
    let f_y = function.apply(&[&y]).as_bv().unwrap();
    let read_f_x = array.select(&f_x).as_bv().unwrap();
    let other_read_f_y = other_array.select(&f_y).as_bv().unwrap();
    let same_xy = x.eq(&y);
    let different_xy = same_xy.not();
    let same_reads = read_x.eq(&read_y);
    let different_reads = same_reads.not();
    let transformed_x = if seed & 1 == 0 {
        x.bvadd(&offset)
    } else {
        x.bvxor(&offset)
    };
    let transformed_y = if seed & 1 == 0 {
        y.bvadd(&offset)
    } else {
        y.bvxor(&offset)
    };
    let same_transformed = transformed_x.eq(&transformed_y);
    let stored_read_y = array.store(&x, &first).select(&y).as_bv().unwrap();
    let stored = array.store(&x, &first);
    let arrays_equal = array.eq(&other_array);
    let arrays_different = arrays_equal.not();

    let assertions: Vec<Bool> = match seed % 20 {
        0 => vec![same_xy, different_reads],
        1 => vec![different_xy, read_x.eq(&first), read_y.eq(&second)],
        2 => vec![same_xy, f_read_x.bvult(&f_read_y)],
        3 => vec![
            different_xy,
            read_x.eq(&first),
            read_y.eq(&second),
            f_read_x.eq(&first),
            f_read_y.eq(&second),
        ],
        4 => vec![same_transformed, stored_read_y.eq(&first).not()],
        5 => vec![different_xy, stored_read_y.eq(&second)],
        6 => vec![
            Bool::or(&[same_xy, same_reads]),
            different_xy,
            different_reads,
        ],
        7 => vec![same_xy, nested_x.eq(&nested_y).not()],
        8 => vec![arrays_equal, read_x.eq(&other_read_x).not()],
        9 => vec![arrays_different],
        10 => vec![stored.eq(&array), read_x.eq(&first).not()],
        11 => vec![arrays_equal, same_xy, read_f_x.eq(&other_read_f_y).not()],
        12 => vec![
            Bool::or(&[arrays_equal, same_xy]),
            arrays_different,
            different_xy,
        ],
        13 => vec![stored.eq(&other_array)],
        14 => vec![stored.eq(&stored).not()],
        15 => vec![arrays_different, read_x.eq(&other_read_x)],
        case => z3_cross_equality_case(
            case,
            width,
            &array,
            &other_array,
            &third_array,
            &fourth_array,
            &stored,
        ),
    };
    let solver = Solver::new();
    for assertion in assertions {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[cfg(feature = "z3")]
fn z3_structural_store_parent_verdict(seed: u64) -> Verdict {
    let width = 3;
    let bv_sort = Z3Sort::bitvector(width);
    let left_array = Array::new_const("store_parent_a", &bv_sort, &bv_sort);
    let peer_array = Array::new_const("store_parent_b", &bv_sort, &bv_sort);
    let transitive_array = Array::new_const("store_parent_c", &bv_sort, &bv_sort);
    let function = FuncDecl::new("store_parent_f", &[&bv_sort], &bv_sort);
    let write_left = BV::new_const("store_parent_x", width);
    let write_peer = BV::new_const("store_parent_y", width);
    let read_index = BV::new_const("store_parent_k", width);
    let value = BV::new_const("store_parent_value", width);
    let other_value = BV::new_const("store_parent_other_value", width);
    let left_function_index = function.apply(&[&write_left]).as_bv().unwrap();
    let peer_function_index = function.apply(&[&write_peer]).as_bv().unwrap();
    let left_store = left_array.store(&write_left, &value);
    let peer_store_distinct = peer_array.store(&write_peer, &other_value);
    let peer_store_matched = peer_array.store(&write_left, &value);
    let transitive_store_matched = transitive_array.store(&write_left, &value);
    let left_store_function_index = left_array.store(&left_function_index, &value);
    let peer_store_function_index = peer_array.store(&peer_function_index, &other_value);
    let left_read = left_store.select(&read_index).as_bv().unwrap();
    let peer_distinct_read = peer_store_distinct.select(&read_index).as_bv().unwrap();
    let peer_matched_read = peer_store_matched.select(&read_index).as_bv().unwrap();
    let transitive_matched_read = transitive_store_matched
        .select(&read_index)
        .as_bv()
        .unwrap();
    let left_function_read = left_store_function_index
        .select(&read_index)
        .as_bv()
        .unwrap();
    let peer_function_read = peer_store_function_index
        .select(&read_index)
        .as_bv()
        .unwrap();
    let left_index_read = left_store.select(&write_left).as_bv().unwrap();
    let peer_index_read = left_store.select(&write_peer).as_bv().unwrap();
    let left_peer_equal = left_array.eq(&peer_array);
    let peer_transitive_equal = peer_array.eq(&transitive_array);
    let left_transitive_equal = left_array.eq(&transitive_array);
    let same_indices = write_left.eq(&write_peer);
    let same_values = value.eq(&other_value);

    let assertions = match seed % 8 {
        0 => vec![
            left_peer_equal,
            same_indices,
            same_values,
            left_read.eq(&peer_distinct_read).not(),
        ],
        1 => vec![same_indices, left_index_read.eq(&peer_index_read).not()],
        2 => vec![left_read.eq(&peer_distinct_read).not()],
        3 => vec![
            Bool::or(&[left_peer_equal, left_transitive_equal]),
            left_read.eq(&peer_matched_read).not(),
        ],
        4 => vec![
            left_peer_equal,
            peer_transitive_equal,
            left_read.eq(&transitive_matched_read).not(),
        ],
        5 => vec![
            left_peer_equal,
            same_indices,
            same_values,
            left_function_read.eq(&peer_function_read).not(),
        ],
        6 => vec![
            left_peer_equal,
            same_indices,
            same_values,
            left_read.eq(&peer_distinct_read),
        ],
        _ => vec![left_peer_equal.not(), left_read.eq(&peer_matched_read)],
    };
    let solver = Solver::new();
    for assertion in assertions {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[cfg(feature = "z3")]
fn z3_dynamic_row_verdict(seed: u64) -> Verdict {
    let width = 3;
    let bv_sort = Z3Sort::bitvector(width);
    let base_array = Array::new_const("dynamic_row_a", &bv_sort, &bv_sort);
    let row_function = FuncDecl::new("dynamic_row_f", &[&bv_sort], &bv_sort);
    let write_index = BV::new_const("dynamic_row_x", width);
    let peer_index = BV::new_const("dynamic_row_y", width);
    let read_index = BV::new_const("dynamic_row_k", width);
    let stored_value = BV::new_const("dynamic_row_v", width);
    let shadow_value = BV::new_const("dynamic_row_w", width);
    let fallback = Bool::new_const("dynamic_row_guard");
    let function_write = row_function.apply(&[&write_index]).as_bv().unwrap();
    let function_peer = row_function.apply(&[&peer_index]).as_bv().unwrap();
    let first_store = base_array.store(&write_index, &stored_value);
    let nested_store = first_store.store(&peer_index, &shadow_value);
    let shadow_store = first_store.store(&write_index, &shadow_value);
    let function_store = base_array.store(&function_write, &stored_value);
    let hit_read = first_store.select(&write_index).as_bv().unwrap();
    let peer_read = first_store.select(&peer_index).as_bv().unwrap();
    let base_peer_read = base_array.select(&peer_index).as_bv().unwrap();
    let nested_read = nested_store.select(&read_index).as_bv().unwrap();
    let base_read = base_array.select(&read_index).as_bv().unwrap();
    let function_read = function_store.select(&function_peer).as_bv().unwrap();
    let shadow_read = shadow_store.select(&write_index).as_bv().unwrap();
    let same_indices = write_index.eq(&peer_index);
    let different_indices = same_indices.not();
    let read_misses_write = read_index.eq(&write_index).not();
    let read_misses_peer = read_index.eq(&peer_index).not();
    let peer_is_base = peer_read.eq(&base_peer_read);
    let peer_is_value = peer_read.eq(&stored_value);

    let assertions = match seed % 8 {
        0 => vec![hit_read.eq(&stored_value).not()],
        1 => vec![different_indices, peer_is_base.not()],
        2 => vec![
            different_indices,
            base_peer_read.eq(&stored_value).not(),
            Bool::or(&[peer_is_value, fallback]),
        ],
        3 => vec![
            read_misses_write,
            read_misses_peer,
            nested_read.eq(&base_read).not(),
        ],
        4 => vec![different_indices, peer_is_base],
        5 => vec![same_indices, function_read.eq(&stored_value).not()],
        6 => vec![shadow_read.eq(&shadow_value).not()],
        _ => vec![Bool::or(&[same_indices, fallback]), peer_is_value.not()],
    };
    let solver = Solver::new();
    for assertion in assertions {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[cfg(feature = "z3")]
fn z3_dynamic_interface_verdict(seed: u64) -> Verdict {
    let width = 3;
    let bv_sort = Z3Sort::bitvector(width);
    let array_a = Array::new_const("dynamic_iface_a", &bv_sort, &bv_sort);
    let array_b = Array::new_const("dynamic_iface_b", &bv_sort, &bv_sort);
    let array_c = Array::new_const("dynamic_iface_c", &bv_sort, &bv_sort);
    let function_f = FuncDecl::new("dynamic_iface_f", &[&bv_sort], &bv_sort);
    let function_g = FuncDecl::new("dynamic_iface_g", &[&bv_sort], &bv_sort);
    let x = BV::new_const("dynamic_iface_x", width);
    let y = BV::new_const("dynamic_iface_y", width);
    let k = BV::new_const("dynamic_iface_k", width);
    let value = BV::new_const("dynamic_iface_v", width);
    let fallback = Bool::new_const("dynamic_iface_guard");
    let fx = function_f.apply(&[&x]).as_bv().unwrap();
    let fy = function_f.apply(&[&y]).as_bv().unwrap();
    let gfx = function_g.apply(&[&fx]).as_bv().unwrap();
    let gfy = function_g.apply(&[&fy]).as_bv().unwrap();
    let a_at_x = array_a.select(&x).as_bv().unwrap();
    let a_at_y = array_a.select(&y).as_bv().unwrap();
    let a_at_k = array_a.select(&k).as_bv().unwrap();
    let b_at_k = array_b.select(&k).as_bv().unwrap();
    let store_a = array_a.store(&x, &value);
    let store_b = array_b.store(&y, &value);
    let updated_value_at_k = store_a.select(&k).as_bv().unwrap();
    let peer_value_at_k = store_b.select(&k).as_bv().unwrap();
    let same_xy = x.eq(&y);
    let f_strict = fx.bvult(&fy);
    let g_strict = gfx.bvult(&gfy);
    let nested_choice = Bool::or(&[f_strict.clone(), fallback.clone()]);
    let different_base_reads = a_at_x.eq(&a_at_y).not();
    let a_eq_b = array_a.eq(&array_b);
    let a_eq_c = array_a.eq(&array_c);
    let parent_choice = Bool::or(&[a_eq_b.clone(), a_eq_c]);
    let different_parent_reads = a_at_k.eq(&b_at_k).not();
    let different_store_reads = updated_value_at_k.eq(&peer_value_at_k).not();
    let store_equals_base = store_a.eq(&array_a);
    let base_read_differs = array_a.select(&x).eq(&value).not();
    let read_choice = Bool::or(&[a_at_x.bvult(&a_at_y), fallback.clone()]);
    let f_of_a_at_x = function_f.apply(&[&a_at_x]).as_bv().unwrap();
    let f_of_a_at_y = function_f.apply(&[&a_at_y]).as_bv().unwrap();
    let f_read_strict = f_of_a_at_x.bvult(&f_of_a_at_y);
    let replay_choice = Bool::or(&[f_strict.clone(), fallback]);

    let assertions = match seed % 8 {
        0 => vec![same_xy, f_strict],
        1 => vec![same_xy, nested_choice, g_strict],
        2 => vec![same_xy, different_base_reads],
        3 => vec![parent_choice, different_parent_reads],
        4 => vec![a_eq_b, same_xy, different_store_reads],
        5 => vec![store_equals_base, base_read_differs],
        6 => vec![same_xy, read_choice, f_read_strict],
        _ => vec![same_xy, replay_choice],
    };
    let solver = Solver::new();
    for assertion in assertions {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[test]
fn finite_scalar_arrays_match_analytic_oracle_and_front_door() {
    for seed in 0..128 {
        let expected = finite_scalar_expected(seed);
        let mut online_arena = TermArena::new();
        let online_assertions = build_finite_scalar_array_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&online),
            expected,
            "online/analytic disagreement at finite scalar seed {seed}: {online:?}"
        );
        assert_sat_replays(&online_arena, &online_assertions, &online, seed);

        let mut front_arena = TermArena::new();
        let front_assertions = build_finite_scalar_array_case(seed, &mut front_arena);
        let front = check_auto(
            &mut front_arena,
            &front_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&front),
            expected,
            "front-door/analytic disagreement at finite scalar seed {seed}: {front:?}"
        );
        assert_sat_replays(&front_arena, &front_assertions, &front, seed);
    }
}

#[cfg(feature = "z3")]
#[test]
fn finite_scalar_arrays_match_z3_matrix() {
    for seed in 0..128 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_finite_scalar_array_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        let z3 = z3_finite_scalar_verdict(seed);

        assert_eq!(
            verdict(&online),
            z3,
            "online/Z3 disagreement at finite scalar seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}

#[test]
fn structural_store_parents_match_eager_and_front_door() {
    for seed in 0..128 {
        let mut eager_arena = TermArena::new();
        let eager_assertions = build_structural_store_parent_case(seed, &mut eager_arena);
        let eager = check_with_arrays_and_functions(
            &mut SatBvBackend::new(),
            &mut eager_arena,
            &eager_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_ne!(
            verdict(&eager),
            Verdict::Unknown,
            "eager structural-store seed {seed}: {eager:?}"
        );

        let mut online_arena = TermArena::new();
        let online_assertions = build_structural_store_parent_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&online),
            verdict(&eager),
            "online/eager structural-store disagreement at seed {seed}: online={online:?}, eager={eager:?}"
        );
        assert_sat_replays(&online_arena, &online_assertions, &online, seed);

        let mut front_arena = TermArena::new();
        let front_assertions = build_structural_store_parent_case(seed, &mut front_arena);
        let front = check_auto(
            &mut front_arena,
            &front_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&front),
            verdict(&eager),
            "front-door/eager structural-store disagreement at seed {seed}: front={front:?}, eager={eager:?}"
        );
        assert_sat_replays(&front_arena, &front_assertions, &front, seed);
    }
}

#[cfg(feature = "z3")]
#[test]
fn structural_store_parents_match_z3_matrix() {
    for seed in 0..128 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_structural_store_parent_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        let z3 = z3_structural_store_parent_verdict(seed);

        assert_eq!(
            verdict(&online),
            z3,
            "online/Z3 structural-store disagreement at seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}

#[test]
fn dynamic_row_insertion_matches_eager_and_front_door() {
    for seed in 0..128 {
        let mut eager_arena = TermArena::new();
        let eager_assertions = build_dynamic_row_case(seed, &mut eager_arena);
        let eager = check_with_arrays_and_functions(
            &mut SatBvBackend::new(),
            &mut eager_arena,
            &eager_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_ne!(
            verdict(&eager),
            Verdict::Unknown,
            "eager dynamic-ROW seed {seed}: {eager:?}"
        );

        let mut online_arena = TermArena::new();
        let online_assertions = build_dynamic_row_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&online),
            verdict(&eager),
            "online/eager dynamic-ROW disagreement at seed {seed}: online={online:?}, eager={eager:?}"
        );
        assert_sat_replays(&online_arena, &online_assertions, &online, seed);

        let mut front_arena = TermArena::new();
        let front_assertions = build_dynamic_row_case(seed, &mut front_arena);
        let front = check_auto(
            &mut front_arena,
            &front_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&front),
            verdict(&eager),
            "front-door/eager dynamic-ROW disagreement at seed {seed}: front={front:?}, eager={eager:?}"
        );
        assert_sat_replays(&front_arena, &front_assertions, &front, seed);
    }
}

#[cfg(feature = "z3")]
#[test]
fn dynamic_row_insertion_matches_z3_matrix() {
    for seed in 0..128 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_dynamic_row_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        let z3 = z3_dynamic_row_verdict(seed);

        assert_eq!(
            verdict(&online),
            z3,
            "online/Z3 dynamic-ROW disagreement at seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}

#[test]
fn dynamic_interface_insertion_matches_eager_and_front_door() {
    for seed in 0..128 {
        let mut eager_arena = TermArena::new();
        let eager_assertions = build_dynamic_interface_case(seed, &mut eager_arena);
        let eager = check_with_arrays_and_functions(
            &mut SatBvBackend::new(),
            &mut eager_arena,
            &eager_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_ne!(
            verdict(&eager),
            Verdict::Unknown,
            "eager dynamic-interface seed {seed}: {eager:?}"
        );

        let mut online_arena = TermArena::new();
        let online_assertions = build_dynamic_interface_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&online),
            verdict(&eager),
            "online/eager dynamic-interface disagreement at seed {seed}: online={online:?}, eager={eager:?}"
        );
        assert_sat_replays(&online_arena, &online_assertions, &online, seed);

        let mut front_arena = TermArena::new();
        let front_assertions = build_dynamic_interface_case(seed, &mut front_arena);
        let front = check_auto(
            &mut front_arena,
            &front_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&front),
            verdict(&eager),
            "front-door/eager dynamic-interface disagreement at seed {seed}: front={front:?}, eager={eager:?}"
        );
        assert_sat_replays(&front_arena, &front_assertions, &front, seed);
    }
}

#[cfg(feature = "z3")]
#[test]
fn dynamic_interface_insertion_matches_z3_matrix() {
    for seed in 0..128 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_dynamic_interface_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        let z3 = z3_dynamic_interface_verdict(seed);

        assert_eq!(
            verdict(&online),
            z3,
            "online/Z3 dynamic-interface disagreement at seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}

#[test]
fn online_aufbv_matches_eager_pure_rust_matrix() {
    for seed in 0..256 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        let mut eager_arena = TermArena::new();
        let eager_assertions = build_case(seed, &mut eager_arena);
        let eager = check_with_arrays_and_functions(
            &mut SatBvBackend::new(),
            &mut eager_arena,
            &eager_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        assert_ne!(
            verdict(&online),
            Verdict::Unknown,
            "online seed {seed}: {online:?}"
        );
        assert_eq!(
            verdict(&online),
            verdict(&eager),
            "online/eager disagreement at seed {seed}: online={online:?}, eager={eager:?}"
        );
    }
}

#[test]
fn front_door_aufbv_matches_eager_matrix() {
    for seed in 0..256 {
        let mut front_arena = TermArena::new();
        let front_assertions = build_case(seed, &mut front_arena);
        let front = check_auto(
            &mut front_arena,
            &front_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        let mut eager_arena = TermArena::new();
        let eager_assertions = build_case(seed, &mut eager_arena);
        let eager = check_with_arrays_and_functions(
            &mut SatBvBackend::new(),
            &mut eager_arena,
            &eager_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        assert_eq!(
            verdict(&front),
            verdict(&eager),
            "front-door/eager disagreement at seed {seed}: front={front:?}, eager={eager:?}"
        );
    }
}

#[cfg(feature = "z3")]
#[test]
fn online_aufbv_matches_z3_matrix() {
    for seed in 0..256 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_case(seed, &mut online_arena);
        let online = check_qf_aufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        let z3 = z3_verdict(seed);

        assert_eq!(
            verdict(&online),
            z3,
            "online/Z3 disagreement at seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}
