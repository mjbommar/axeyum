//! Deterministic differential gate for canonical online EUF+BV combination.

use axeyum_ir::{Sort, TermArena, TermId};
#[cfg(feature = "z3")]
use axeyum_solver::Z3Backend;
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_auto, check_qf_ufbv_online_cdclt,
    check_with_function_elimination,
};

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
    let k_value = u128::from((seed % u64::try_from(modulus - 1).unwrap()) + 1);
    let c1_value = u128::from(seed % u64::try_from(modulus).unwrap());
    let c2_value = (c1_value + 1) % modulus;
    let unary_function = arena
        .declare_fun("f", &[Sort::BitVec(width)], Sort::BitVec(width))
        .unwrap();
    let binary_function = arena
        .declare_fun(
            "g",
            &[Sort::BitVec(width), Sort::BitVec(width)],
            Sort::BitVec(width),
        )
        .unwrap();
    let x_term = arena.bv_var("x", width).unwrap();
    let y_term = arena.bv_var("y", width).unwrap();
    let z_term = arena.bv_var("z", width).unwrap();
    let offset = arena.bv_const(width, k_value).unwrap();
    let first_value = arena.bv_const(width, c1_value).unwrap();
    let second_value = arena.bv_const(width, c2_value).unwrap();
    let transformed_x = if seed & 1 == 0 {
        arena.bv_add(x_term, offset).unwrap()
    } else {
        arena.bv_xor(x_term, offset).unwrap()
    };
    let transformed_y = if seed & 1 == 0 {
        arena.bv_add(y_term, offset).unwrap()
    } else {
        arena.bv_xor(y_term, offset).unwrap()
    };
    let same_transformed = arena.eq(transformed_x, transformed_y).unwrap();
    let different_transformed = arena.not(same_transformed).unwrap();
    let same_xy = arena.eq(x_term, y_term).unwrap();
    let different_xy = arena.not(same_xy).unwrap();
    let fx = arena.apply(unary_function, &[x_term]).unwrap();
    let fy = arena.apply(unary_function, &[y_term]).unwrap();
    let same_f = arena.eq(fx, fy).unwrap();
    let different_f = arena.not(same_f).unwrap();
    let ffx = arena.apply(unary_function, &[fx]).unwrap();
    let ffy = arena.apply(unary_function, &[fy]).unwrap();
    let same_nested = arena.eq(ffx, ffy).unwrap();
    let different_nested = arena.not(same_nested).unwrap();
    let gxz = arena.apply(binary_function, &[x_term, z_term]).unwrap();
    let gyz = arena.apply(binary_function, &[y_term, z_term]).unwrap();
    let same_binary = arena.eq(gxz, gyz).unwrap();
    let different_binary = arena.not(same_binary).unwrap();
    let first_result_pinned = arena.eq(fx, first_value).unwrap();
    let second_result_pinned = arena.eq(fy, second_value).unwrap();

    match seed % 8 {
        // Invertible BV operation implies x=y, then congruence refutes f(x)!=f(y).
        0 => vec![same_transformed, different_f],
        // The SAT companion: distinct transformed values permit distinct inputs/results.
        1 => vec![different_transformed, different_f],
        // Congruent results cannot be in strict unsigned order.
        2 => vec![same_xy, arena.bv_ult(fx, fy).unwrap()],
        // Distinct inputs can take distinct pinned function values.
        3 => vec![different_xy, first_result_pinned, second_result_pinned],
        // Binary congruence shares one argument and receives the other via interface EQ.
        4 => vec![same_xy, different_binary],
        // Congruence closes through two nested applications.
        5 => vec![same_xy, different_nested],
        // Boolean structure requires at least one equality, then refutes both choices.
        6 => vec![
            arena.or(same_xy, same_f).unwrap(),
            different_xy,
            different_f,
        ],
        // A satisfiable binary/unary mix with no forced alias.
        _ => vec![
            different_xy,
            first_result_pinned,
            second_result_pinned,
            same_binary,
        ],
    }
}

#[test]
fn online_ufbv_matches_eager_pure_rust_matrix() {
    for seed in 0..512 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_case(seed, &mut online_arena);
        let online = check_qf_ufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        let mut eager_arena = TermArena::new();
        let eager_assertions = build_case(seed, &mut eager_arena);
        let eager = check_with_function_elimination(
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
fn front_door_ufbv_matches_eager_matrix() {
    for seed in 0..512 {
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
        let eager = check_with_function_elimination(
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
fn online_ufbv_matches_z3_matrix() {
    for seed in 0..512 {
        let mut online_arena = TermArena::new();
        let online_assertions = build_case(seed, &mut online_arena);
        let online = check_qf_ufbv_online_cdclt(
            &mut online_arena,
            &online_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        let mut z3_arena = TermArena::new();
        let z3_assertions = build_case(seed, &mut z3_arena);
        let z3 = check_with_function_elimination(
            &mut Z3Backend::new(),
            &mut z3_arena,
            &z3_assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        assert_eq!(
            verdict(&online),
            verdict(&z3),
            "online/Z3 disagreement at seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}
