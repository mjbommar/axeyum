//! Differential and front-door gates for ADR-0084 array-valued UF results.
#![cfg(feature = "full")]

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId, Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto, check_qf_aufbv_online_cdclt};
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

fn expected(seed: u64) -> Verdict {
    match seed % 12 {
        0 | 2 | 5 | 7 | 8 | 9 => Verdict::Unsat,
        _ => Verdict::Sat,
    }
}

fn build_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(3),
        element: ArraySortKey::BitVec(3),
    };
    let function = arena
        .declare_fun("array_result_f", &[Sort::BitVec(3)], array_sort)
        .unwrap();
    let scalar_function = arena
        .declare_fun("array_key_g", &[array_sort], Sort::BitVec(3))
        .unwrap();
    let x = arena.bv_var("array_result_x", 3).unwrap();
    let y = arena.bv_var("array_result_y", 3).unwrap();
    let array = arena
        .array_var_with_sorts("array_result_a", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let fx = arena.apply(function, &[x]).unwrap();
    let fy = arena.apply(function, &[y]).unwrap();
    let zero = arena.bv_const(3, 0).unwrap();
    let one_index = arena.bv_const(3, 1).unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let two = arena.bv_const(3, 2).unwrap();
    let left_zero_read = arena.select(fx, zero).unwrap();
    let left_one_read = arena.select(fx, one_index).unwrap();
    let right_zero_read = arena.select(fy, zero).unwrap();
    let right_one_read = arena.select(fy, one_index).unwrap();
    let array_zero = arena.select(array, zero).unwrap();
    let same_args = arena.eq(x, y).unwrap();
    let different_args = arena.not(same_args).unwrap();
    let same_zero_reads = arena.eq(left_zero_read, right_zero_read).unwrap();
    let different_zero_reads = arena.not(same_zero_reads).unwrap();
    let left_zero_is_one = arena.eq(left_zero_read, one).unwrap();
    let left_zero_is_two = arena.eq(left_zero_read, two).unwrap();
    let left_one_is_two = arena.eq(left_one_read, two).unwrap();
    let right_one_is_two = arena.eq(right_one_read, two).unwrap();
    let arrays_equal = arena.eq(fx, array).unwrap();
    let arrays_different = arena.not(arrays_equal).unwrap();
    let same_array_read = arena.eq(left_zero_read, array_zero).unwrap();
    let different_array_read = arena.not(same_array_read).unwrap();

    match seed % 12 {
        0 => vec![left_zero_is_one, left_zero_is_two],
        1 => vec![left_zero_is_one, left_one_is_two],
        2 => vec![same_args, different_zero_reads],
        3 => vec![different_args, different_zero_reads],
        4 => vec![same_args, left_zero_is_one, right_one_is_two],
        5 => vec![arrays_equal, different_array_read],
        6 => vec![arrays_different, same_array_read],
        7 => {
            let stored = arena.store(fx, zero, one).unwrap();
            let read = arena.select(stored, zero).unwrap();
            let hit = arena.eq(read, one).unwrap();
            vec![arena.not(hit).unwrap()]
        }
        8 => {
            let condition = arena.bool_var("array_result_condition").unwrap();
            let chosen = arena.ite(condition, fx, array).unwrap();
            let chosen_read = arena.select(chosen, zero).unwrap();
            let same = arena.eq(chosen_read, left_zero_read).unwrap();
            vec![condition, arena.not(same).unwrap()]
        }
        9 => {
            let same_results = arena.eq(fx, fy).unwrap();
            vec![same_args, arena.not(same_results).unwrap()]
        }
        10 => vec![different_args, arena.eq(fx, fy).unwrap()],
        _ => {
            let gx = arena.apply(scalar_function, &[fx]).unwrap();
            let gy = arena.apply(scalar_function, &[fy]).unwrap();
            vec![
                different_args,
                left_zero_is_one,
                arena.eq(right_zero_read, two).unwrap(),
                arena.eq(gx, one).unwrap(),
                arena.eq(gy, two).unwrap(),
            ]
        }
    }
}

fn assert_sat_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult, seed: u64) {
    let CheckResult::Sat(model) = result else {
        return;
    };
    let assignment = model.to_assignment();
    for &assertion in assertions {
        assert_eq!(
            eval(arena, assertion, &assignment),
            Ok(Value::Bool(true)),
            "seed {seed} failed replay at assertion #{assertion:?}"
        );
    }
}

#[test]
fn analytic_and_front_door_matrix_decides_and_replays() {
    for seed in 0..96 {
        let expected = expected(seed);

        let mut direct_arena = TermArena::new();
        let direct_assertions = build_case(seed, &mut direct_arena);
        let direct = check_qf_aufbv_online_cdclt(
            &mut direct_arena,
            &direct_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&direct),
            expected,
            "canonical array-valued UF seed {seed}: {direct:?}"
        );
        assert_sat_replays(&direct_arena, &direct_assertions, &direct, seed);

        let mut front_arena = TermArena::new();
        let front_assertions = build_case(seed, &mut front_arena);
        let front = check_auto(
            &mut front_arena,
            &front_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&front),
            expected,
            "front-door array-valued UF seed {seed}: {front:?}"
        );
        assert_sat_replays(&front_arena, &front_assertions, &front, seed);
    }
}

#[test]
fn smtlib_front_door_decides_array_valued_application() {
    let text = r"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 3)) (Array (_ BitVec 3) (_ BitVec 3)))
        (declare-fun x () (_ BitVec 3))
        (assert (= (select (f x) (_ bv0 3)) (_ bv5 3)))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("array-valued UF script parses");
    let assertions = script.checked_flat_view().to_vec();
    let result = check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_sat_replays(&script.arena, &assertions, &result, 0);
}

#[cfg(feature = "z3")]
fn z3_verdict(seed: u64) -> Verdict {
    let bv_sort = Z3Sort::bitvector(3);
    let array_sort = Z3Sort::array(&bv_sort, &bv_sort);
    let function = FuncDecl::new("array_result_f", &[&bv_sort], &array_sort);
    let scalar_function = FuncDecl::new("array_key_g", &[&array_sort], &bv_sort);
    let x = BV::new_const("array_result_x", 3);
    let y = BV::new_const("array_result_y", 3);
    let array = Array::new_const("array_result_a", &bv_sort, &bv_sort);
    let fx = function.apply(&[&x]).as_array().unwrap();
    let fy = function.apply(&[&y]).as_array().unwrap();
    let zero = BV::from_u64(0, 3);
    let one_index = BV::from_u64(1, 3);
    let one = BV::from_u64(1, 3);
    let two = BV::from_u64(2, 3);
    let left_zero_read = fx.select(&zero).as_bv().unwrap();
    let left_one_read = fx.select(&one_index).as_bv().unwrap();
    let right_zero_read = fy.select(&zero).as_bv().unwrap();
    let right_one_read = fy.select(&one_index).as_bv().unwrap();
    let array_zero = array.select(&zero).as_bv().unwrap();
    let same_args = x.eq(&y);
    let different_args = same_args.not();
    let different_zero_reads = left_zero_read.eq(&right_zero_read).not();
    let arrays_equal = fx.eq(&array);
    let arrays_different = arrays_equal.not();

    let assertions: Vec<Bool> = match seed % 12 {
        0 => vec![left_zero_read.eq(&one), left_zero_read.eq(&two)],
        1 => vec![left_zero_read.eq(&one), left_one_read.eq(&two)],
        2 => vec![same_args, different_zero_reads],
        3 => vec![different_args, different_zero_reads],
        4 => vec![same_args, left_zero_read.eq(&one), right_one_read.eq(&two)],
        5 => vec![arrays_equal, left_zero_read.eq(&array_zero).not()],
        6 => vec![arrays_different, left_zero_read.eq(&array_zero)],
        7 => vec![fx.store(&zero, &one).select(&zero).eq(&one).not()],
        8 => {
            let condition = Bool::new_const("array_result_condition");
            let chosen = condition.ite(&fx, &array);
            vec![
                condition,
                chosen
                    .select(&zero)
                    .as_bv()
                    .unwrap()
                    .eq(&left_zero_read)
                    .not(),
            ]
        }
        9 => vec![same_args, fx.eq(&fy).not()],
        10 => vec![different_args, fx.eq(&fy)],
        _ => {
            let gx = scalar_function.apply(&[&fx]).as_bv().unwrap();
            let gy = scalar_function.apply(&[&fy]).as_bv().unwrap();
            vec![
                different_args,
                left_zero_read.eq(&one),
                right_zero_read.eq(&two),
                gx.eq(&one),
                gy.eq(&two),
            ]
        }
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
#[test]
fn canonical_matrix_matches_z3() {
    for seed in 0..96 {
        let mut arena = TermArena::new();
        let assertions = build_case(seed, &mut arena);
        let online =
            check_qf_aufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap();
        let z3 = z3_verdict(seed);
        assert_eq!(
            verdict(&online),
            z3,
            "canonical/Z3 array-valued UF seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}
