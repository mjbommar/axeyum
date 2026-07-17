//! Differential and replay gates for ADR-0085 structural array-class equations.
#![cfg(feature = "full")]

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId, Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SolverConfig, UnknownKind, check_auto, check_qf_aufbv_online_cdclt,
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

fn expected(seed: u64) -> Verdict {
    match seed % 16 {
        2 | 4 | 6 | 9 | 10 | 15 => Verdict::Unsat,
        _ => Verdict::Sat,
    }
}

#[allow(clippy::too_many_lines)]
fn build_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(3),
        element: ArraySortKey::BitVec(3),
    };
    let array_function = arena
        .declare_fun("structural_f", &[Sort::BitVec(3)], array_sort)
        .unwrap();
    let scalar_function = arena
        .declare_fun("structural_g", &[array_sort], Sort::BitVec(3))
        .unwrap();
    let x = arena.bv_var("structural_x", 3).unwrap();
    let condition = arena.bool_var("structural_condition").unwrap();
    let second_condition = arena.bool_var("structural_condition_2").unwrap();
    let a = arena
        .array_var_with_sorts("structural_a", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let b = arena
        .array_var_with_sorts("structural_b", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let d = arena
        .array_var_with_sorts("structural_d", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let zero = arena.bv_const(3, 0).unwrap();
    let one_index = arena.bv_const(3, 1).unwrap();
    let two_index = arena.bv_const(3, 2).unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let two = arena.bv_const(3, 2).unwrap();
    let store_a = arena.store(a, zero, one).unwrap();
    let store_b_one = arena.store(b, zero, one).unwrap();
    let store_b_two = arena.store(b, zero, two).unwrap();
    let const_one = arena.const_array(3, one).unwrap();
    let chosen = arena.ite(condition, a, b).unwrap();
    let nested = arena.ite(second_condition, chosen, d).unwrap();
    let fx = arena.apply(array_function, &[x]).unwrap();

    let arrays_equal = |arena: &mut TermArena, lhs, rhs| arena.eq(lhs, rhs).unwrap();
    let arrays_differ = |arena: &mut TermArena, lhs, rhs| {
        let same = arena.eq(lhs, rhs).unwrap();
        arena.not(same).unwrap()
    };
    let read_is = |arena: &mut TermArena, array, index, value| {
        let read = arena.select(array, index).unwrap();
        arena.eq(read, value).unwrap()
    };

    match seed % 16 {
        0 => vec![arrays_equal(arena, store_a, d)],
        1 => vec![
            arrays_equal(arena, store_a, d),
            read_is(arena, a, one_index, two),
            read_is(arena, d, one_index, two),
            read_is(arena, d, two_index, one),
        ],
        2 => vec![
            arrays_equal(arena, store_a, d),
            read_is(arena, d, zero, two),
        ],
        3 => vec![
            arrays_equal(arena, store_a, store_b_one),
            read_is(arena, a, one_index, two),
            read_is(arena, b, one_index, two),
        ],
        4 => vec![arrays_equal(arena, store_a, store_b_two)],
        5 => vec![arrays_equal(arena, d, const_one)],
        6 => vec![
            arrays_equal(arena, d, const_one),
            read_is(arena, d, zero, two),
        ],
        7 => vec![
            condition,
            arrays_equal(arena, chosen, d),
            read_is(arena, a, zero, one),
        ],
        8 => vec![
            arena.not(condition).unwrap(),
            arrays_equal(arena, chosen, d),
        ],
        9 => vec![
            condition,
            arrays_equal(arena, chosen, d),
            arrays_differ(arena, a, d),
        ],
        10 => vec![
            arena.not(condition).unwrap(),
            arrays_equal(arena, chosen, d),
            arrays_differ(arena, b, d),
        ],
        11 => vec![
            condition,
            arrays_equal(arena, chosen, d),
            arrays_differ(arena, b, d),
        ],
        12 => vec![
            condition,
            arena.not(second_condition).unwrap(),
            arrays_equal(arena, nested, d),
            arrays_differ(arena, a, d),
        ],
        13 => vec![
            arrays_equal(arena, fx, store_a),
            read_is(arena, fx, one_index, two),
            read_is(arena, a, one_index, two),
        ],
        14 => vec![arrays_equal(arena, fx, const_one)],
        _ => {
            let gx = arena.apply(scalar_function, &[fx]).unwrap();
            let gs = arena.apply(scalar_function, &[store_a]).unwrap();
            vec![
                arrays_equal(arena, fx, store_a),
                arena.eq(gx, one).unwrap(),
                arena.eq(gs, two).unwrap(),
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
            "structural seed {seed} failed replay at assertion #{assertion:?}"
        );
    }
}

#[test]
fn analytic_and_front_door_matrix_decides_and_replays() {
    for seed in 0..64 {
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
            "canonical structural seed {seed}: {direct:?}"
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
            "front-door structural seed {seed}: {front:?}"
        );
        assert_sat_replays(&front_arena, &front_assertions, &front, seed);
    }
}

#[test]
fn store_equality_projects_a_total_replaying_model() {
    let mut arena = TermArena::new();
    let assertions = build_case(0, &mut arena);
    let result =
        check_qf_aufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_sat_replays(&arena, &assertions, &result, 0);
}

#[test]
fn selected_ite_equality_reaches_the_egraph() {
    let mut arena = TermArena::new();
    let assertions = build_case(9, &mut arena);
    let result =
        check_qf_aufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn ite_equality_expansion_cap_declines() {
    let mut arena = TermArena::new();
    let condition = arena.bool_var("expansion_cap_condition").unwrap();
    let array = arena
        .array_var_with_sorts("expansion_cap_array", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let target = arena
        .array_var_with_sorts("expansion_cap_target", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let mut tree = array;
    for _ in 0..9 {
        tree = arena.ite(condition, tree, tree).unwrap();
    }
    let assertion = arena.eq(tree, target).unwrap();
    let result =
        check_qf_aufbv_online_cdclt(&mut arena, &[assertion], &SolverConfig::default()).unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("over-cap ITE equality expansion should decline, got {result:?}");
    };
    assert_eq!(reason.kind, UnknownKind::ResourceLimit);
    assert!(reason.detail.contains("256 leaves"), "reason={reason:?}");
}

#[test]
fn ite_equality_depth_cap_declines() {
    let mut arena = TermArena::new();
    let condition = arena.bool_var("expansion_depth_condition").unwrap();
    let array = arena
        .array_var_with_sorts("expansion_depth_array", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let target = arena
        .array_var_with_sorts("expansion_depth_target", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let mut tree = array;
    for _ in 0..257 {
        tree = arena.ite(condition, tree, array).unwrap();
    }
    let assertion = arena.eq(tree, target).unwrap();
    let result =
        check_qf_aufbv_online_cdclt(&mut arena, &[assertion], &SolverConfig::default()).unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("over-depth ITE equality expansion should decline, got {result:?}");
    };
    assert_eq!(reason.kind, UnknownKind::ResourceLimit);
    assert!(reason.detail.contains("depth 256"), "reason={reason:?}");
}

#[test]
fn bool_components_project_while_int_components_decline() {
    let mut bool_arena = TermArena::new();
    let base = bool_arena
        .array_var_with_sorts("bool_structural_base", Sort::Bool, Sort::Bool)
        .unwrap();
    let target = bool_arena
        .array_var_with_sorts("bool_structural_target", Sort::Bool, Sort::Bool)
        .unwrap();
    let false_index = bool_arena.bool_const(false);
    let true_value = bool_arena.bool_const(true);
    let stored = bool_arena.store(base, false_index, true_value).unwrap();
    let assertion = bool_arena.eq(stored, target).unwrap();
    let result =
        check_qf_aufbv_online_cdclt(&mut bool_arena, &[assertion], &SolverConfig::default())
            .unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_sat_replays(&bool_arena, &[assertion], &result, 0);

    let mut int_arena = TermArena::new();
    let int_base = int_arena
        .array_var_with_sorts("int_structural_base", Sort::Int, Sort::Int)
        .unwrap();
    let int_target = int_arena
        .array_var_with_sorts("int_structural_target", Sort::Int, Sort::Int)
        .unwrap();
    let zero = int_arena.int_const(0);
    let one = int_arena.int_const(1);
    let int_stored = int_arena.store(int_base, zero, one).unwrap();
    let int_assertion = int_arena.eq(int_stored, int_target).unwrap();
    assert!(matches!(
        check_qf_aufbv_online_cdclt(&mut int_arena, &[int_assertion], &SolverConfig::default(),),
        Err(axeyum_solver::SolverError::Unsupported(_))
    ));
}

#[test]
fn smtlib_selected_ite_equality_decides_unsat() {
    let text = r"
        (set-logic QF_ABV)
        (declare-const c Bool)
        (declare-const a (Array (_ BitVec 3) (_ BitVec 3)))
        (declare-const b (Array (_ BitVec 3) (_ BitVec 3)))
        (declare-const d (Array (_ BitVec 3) (_ BitVec 3)))
        (assert c)
        (assert (= (ite c a b) d))
        (assert (distinct a d))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("structural array-ITE script parses");
    let assertions = script.checked_flat_view().to_vec();
    let result = check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[cfg(feature = "z3")]
#[allow(clippy::too_many_lines)]
fn z3_verdict(seed: u64) -> Verdict {
    let bv_sort = Z3Sort::bitvector(3);
    let array_sort = Z3Sort::array(&bv_sort, &bv_sort);
    let array_function = FuncDecl::new("structural_f", &[&bv_sort], &array_sort);
    let scalar_function = FuncDecl::new("structural_g", &[&array_sort], &bv_sort);
    let x = BV::new_const("structural_x", 3);
    let condition = Bool::new_const("structural_condition");
    let second_condition = Bool::new_const("structural_condition_2");
    let a = Array::new_const("structural_a", &bv_sort, &bv_sort);
    let b = Array::new_const("structural_b", &bv_sort, &bv_sort);
    let d = Array::new_const("structural_d", &bv_sort, &bv_sort);
    let zero = BV::from_u64(0, 3);
    let one_index = BV::from_u64(1, 3);
    let two_index = BV::from_u64(2, 3);
    let one = BV::from_u64(1, 3);
    let two = BV::from_u64(2, 3);
    let store_a = a.store(&zero, &one);
    let store_b_one = b.store(&zero, &one);
    let store_b_two = b.store(&zero, &two);
    let const_one = Array::const_array(&bv_sort, &one);
    let chosen = condition.ite(&a, &b);
    let nested = second_condition.ite(&chosen, &d);
    let fx = array_function.apply(&[&x]).as_array().unwrap();
    let read_is =
        |array: &Array, index: &BV, value: &BV| array.select(index).as_bv().unwrap().eq(value);

    let assertions: Vec<Bool> = match seed % 16 {
        0 => vec![store_a.eq(&d)],
        1 => vec![
            store_a.eq(&d),
            read_is(&a, &one_index, &two),
            read_is(&d, &one_index, &two),
            read_is(&d, &two_index, &one),
        ],
        2 => vec![store_a.eq(&d), read_is(&d, &zero, &two)],
        3 => vec![
            store_a.eq(&store_b_one),
            read_is(&a, &one_index, &two),
            read_is(&b, &one_index, &two),
        ],
        4 => vec![store_a.eq(&store_b_two)],
        5 => vec![d.eq(&const_one)],
        6 => vec![d.eq(&const_one), read_is(&d, &zero, &two)],
        7 => vec![condition.clone(), chosen.eq(&d), read_is(&a, &zero, &one)],
        8 => vec![condition.not(), chosen.eq(&d)],
        9 => vec![condition.clone(), chosen.eq(&d), a.eq(&d).not()],
        10 => vec![condition.not(), chosen.eq(&d), b.eq(&d).not()],
        11 => vec![condition.clone(), chosen.eq(&d), b.eq(&d).not()],
        12 => vec![
            condition,
            second_condition.not(),
            nested.eq(&d),
            a.eq(&d).not(),
        ],
        13 => vec![
            fx.eq(&store_a),
            read_is(&fx, &one_index, &two),
            read_is(&a, &one_index, &two),
        ],
        14 => vec![fx.eq(&const_one)],
        _ => {
            let gx = scalar_function.apply(&[&fx]).as_bv().unwrap();
            let gs = scalar_function.apply(&[&store_a]).as_bv().unwrap();
            vec![fx.eq(&store_a), gx.eq(&one), gs.eq(&two)]
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
    for seed in 0..64 {
        let mut arena = TermArena::new();
        let assertions = build_case(seed, &mut arena);
        let online =
            check_qf_aufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap();
        let z3 = z3_verdict(seed);
        assert_eq!(
            verdict(&online),
            z3,
            "canonical/Z3 structural seed {seed}: online={online:?}, z3={z3:?}"
        );
    }
}
