//! Regression coverage for first-class Int-indexed array sorts.
//!
//! The IR/front-end can represent `(Array Int Int)` directly, and the solver
//! now routes the Bool/linear-Int scalar slice through lazy ROW/extensionality
//! with generic array model projection.

use axeyum_ir::{Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

#[test]
fn int_indexed_array_congruence_conflict_is_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= a b))
        (assert (not (= (select a i) (select b i))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

fn assert_sat_model_replays(text: &str) {
    let mut script = parse_script(text).unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };
    let assignment = model.to_assignment();
    for &assertion in &script.assertions {
        assert_eq!(
            eval(&script.arena, assertion, &assignment),
            Ok(Value::Bool(true))
        );
    }
}

#[test]
fn free_int_indexed_array_sat_model_replays() {
    assert_sat_model_replays(
        r"
        (set-logic QF_ALIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= (select a i) 0))
        (check-sat)
    ",
    );
}

#[test]
fn int_indexed_array_row_conflict_is_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_ALIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= i j))
        (assert (not (= (select (store a i 7) j) 7)))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn int_indexed_array_disequality_sat_model_replays() {
    assert_sat_model_replays(
        r"
        (set-logic QF_ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (not (= a b)))
        (check-sat)
    ",
    );
}

#[test]
fn array_argument_uf_congruence_conflict_is_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-fun g ((Array Int Int)) Int)
        (assert (= a b))
        (assert (not (= (g a) (g b))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn array_argument_uf_sat_model_replays() {
    assert_sat_model_replays(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun g ((Array Int Int)) Int)
        (assert (= (g a) 0))
        (check-sat)
    ",
    );
}

#[test]
fn array_read_indexed_by_array_argument_uf_sat_model_replays() {
    assert_sat_model_replays(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun idx ((Array Int Int)) Int)
        (assert (= (select a (idx a)) 7))
        (check-sat)
    ",
    );
}

#[test]
fn row_conflict_at_array_argument_uf_index_is_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun idx ((Array Int Int)) Int)
        (assert (not (= (select (store a (idx a) 7) (idx a)) 7)))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn store_chain_swap_with_array_argument_skolem_index_is_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert
          (let ((b (store (store a i (select a j)) j (select a i)))
                (c (store (store a j (select a i)) i (select a j))))
            (not (= (select b (sk b c)) (select c (sk b c))))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn symmetric_store_swap_chain_refutes_skolem_read_disequality() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const k Int)
        (declare-const l Int)
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert
          (let ((b1 (store (store a i (select a j)) j (select a i)))
                (c1 (store (store a j (select a i)) i (select a j))))
            (let ((b2 (store (store b1 k (select b1 l)) l (select b1 k)))
                  (c2 (store (store c1 l (select c1 k)) k (select c1 l))))
              (not (= (select b2 (sk b2 c2)) (select c2 (sk b2 c2)))))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn cvc5_swap_chain_refuter_closes_real_regression() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__swap_t1_pp_nf_ai_00010_004.cvc.smt2"
    ))
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn select_over_array_ite_lowers_to_branch_reads() {
    let mut script = parse_script(
        r"
        (set-logic QF_ALIA)
        (declare-const p Bool)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert p)
        (assert (not (= (select (ite p (store a i 7) b) i) 7)))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn two_store_same_target_uf_branches_refute_unsat() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const v Int)
        (declare-const w Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (declare-fun g ((Array Int Int)) Int)
        (assert (= (store a x v) b))
        (assert (= (store a y w) b))
        (assert (not (= (f x) (f y))))
        (assert (not (= (g a) (g b))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn two_store_same_target_declines_when_one_branch_remains_possible() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const v Int)
        (declare-const w Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (= (store a x v) b))
        (assert (= (store a y w) b))
        (assert (not (= (f x) (f y))))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    match result {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            for &assertion in &script.assertions {
                assert_eq!(
                    eval(&script.arena, assertion, &assignment),
                    Ok(Value::Bool(true))
                );
            }
        }
        CheckResult::Unknown(_) => {}
        CheckResult::Unsat => panic!("one remaining array-split branch should not refute"),
    }
}

#[test]
fn const_array_store_chain_default_mismatch_refutes_constarr3() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress1__constarr3.smt2"
    ))
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn const_array_store_chain_same_default_is_not_refuted() {
    let mut script = parse_script(
        r"
        (set-logic QF_ALIA)
        (declare-const all1 (Array Int Int))
        (declare-const all2 (Array Int Int))
        (declare-const aa (Array Int Int))
        (declare-const bb (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= all1 ((as const (Array Int Int)) 1)))
        (assert (= aa (store all1 i 0)))
        (assert (= all2 ((as const (Array Int Int)) 1)))
        (assert (= bb (store all2 j 0)))
        (assert (= aa bb))
        (check-sat)
    ",
    )
    .unwrap();

    let result = check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .unwrap();
    assert_ne!(result, CheckResult::Unsat);
}
