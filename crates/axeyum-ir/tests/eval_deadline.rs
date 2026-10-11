//! Controls for bounded ground evaluation and finite quantifiers.
use axeyum_ir::{Assignment, IrError, Sort, TermArena, Value, eval, eval_within};
use std::time::{Duration, Instant};

#[test]
fn deadline_decline_is_distinct_from_false() {
    let mut arena = TermArena::new();
    let term = arena.bool_const(false);
    let assignment = Assignment::new();
    assert_eq!(
        eval_within(&arena, term, &assignment, Some(Instant::now())).unwrap(),
        None
    );
    assert_eq!(
        eval_within(&arena, term, &assignment, None).unwrap(),
        Some(Value::Bool(false))
    );
}

#[test]
fn bounded_nested_quantifiers_preserve_both_truth_values() {
    let mut arena = TermArena::new();
    let x_symbol = arena.declare("x", Sort::BitVec(2)).unwrap();
    let y_symbol = arena.declare("y", Sort::BitVec(2)).unwrap();
    let x = arena.var(x_symbol);
    let y = arena.var(y_symbol);
    let equality = arena.eq(x, y).unwrap();
    let exists = arena.exists(y_symbol, equality).unwrap();
    let all = arena.forall(y_symbol, equality).unwrap();
    for (body, expected) in [(exists, true), (all, false)] {
        let term = arena.forall(x_symbol, body).unwrap();
        let assignment = Assignment::new();
        assert_eq!(
            eval(&arena, term, &assignment).unwrap(),
            Value::Bool(expected)
        );
        assert_eq!(
            eval_within(
                &arena,
                term,
                &assignment,
                Instant::now().checked_add(Duration::from_secs(10))
            )
            .unwrap(),
            Some(Value::Bool(expected))
        );
        assert_eq!(
            eval_within(&arena, term, &assignment, Some(Instant::now())).unwrap(),
            None
        );
    }
}

#[test]
fn bounded_evaluation_preserves_missing_binding_errors() {
    let mut arena = TermArena::new();
    let symbol = arena.declare("missing", Sort::Bool).unwrap();
    let term = arena.var(symbol);
    assert_eq!(
        eval_within(&arena, term, &Assignment::new(), None),
        Err(IrError::UnboundSymbol(symbol))
    );
}
