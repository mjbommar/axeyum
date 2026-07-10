//! Deterministic differential gate for canonical online array+EUF+BV combination.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_auto, check_qf_aufbv_online_cdclt,
    check_with_arrays_and_functions,
};
#[cfg(feature = "z3")]
use z3::ast::{Array, BV, Bool};
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

    match seed % 16 {
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
        _ => vec![arrays_different, cross_reads_equal],
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

    let assertions: Vec<Bool> = match seed % 16 {
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
        _ => vec![arrays_different, read_x.eq(&other_read_x)],
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
