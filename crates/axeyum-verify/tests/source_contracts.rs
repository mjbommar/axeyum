//! ADR-0316 source annotation, result-retention, and replay gates.

use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_verify::{
    BinOp, Expr, Ty, Verdict, Witness, default_config, lower::lower_contract_program,
    verify_contract_program,
};

#[axeyum_verify::verify]
#[axeyum_verify::requires(x < 255)]
#[axeyum_verify::ensures(|result| result == x + 1)]
fn checked_inc_contract(x: u8) -> u8 {
    x + 1
}

#[axeyum_verify::verify(expect_bug)]
#[axeyum_verify::requires(x < 255)]
#[axeyum_verify::ensures(|result| result == x)]
fn mutated_inc_contract(x: u8) -> u8 {
    x + 1
}

#[axeyum_verify::verify(expect_bug)]
#[axeyum_verify::requires(x < 255)]
#[axeyum_verify::ensures(|result| result == x)]
fn panicking_division_contract(x: u8) -> u8 {
    x / (x / 255)
}

#[axeyum_verify::verify(expect_bug)]
fn unchecked_inc(x: u8) -> u8 {
    x + 1
}

fn witness_u8(inputs: &[Witness], name: &str) -> u8 {
    inputs
        .iter()
        .find_map(|witness| match witness {
            Witness::Int {
                name: actual, bits, ..
            } if actual == name => u8::try_from(*bits).ok(),
            _ => None,
        })
        .expect("named u8 witness")
}

fn bool_value(value: &Value) -> bool {
    let Value::Bool(value) = value else {
        panic!("expected boolean contract term");
    };
    *value
}

fn bind_u8(symbol: axeyum_ir::SymbolId, value: u8) -> Assignment {
    let mut assignment = Assignment::new();
    assignment.set(
        symbol,
        Value::Bv {
            width: 8,
            value: u128::from(value),
        },
    );
    assignment
}

#[test]
fn source_contract_verdicts_and_replays_are_distinct() {
    assert!(matches!(
        checked_inc_contract__axeyum_verdict(),
        Verdict::Verified { .. }
    ));

    let Verdict::Counterexample { class, inputs } = mutated_inc_contract__axeyum_verdict() else {
        panic!("mutated postcondition must be refuted");
    };
    assert_eq!(class, "postcondition violated");
    let x = witness_u8(&inputs, "x");
    let result = mutated_inc_contract(x);
    assert!(x < 255);
    assert_ne!(
        result, x,
        "normally returned result must replay the violation"
    );

    let Verdict::Counterexample { class, inputs } = panicking_division_contract__axeyum_verdict()
    else {
        panic!("division contract must find its source panic");
    };
    assert_ne!(class, "postcondition violated");
    let x = witness_u8(&inputs, "x");
    assert!(axeyum_verify::reproduce::panics_on(|| {
        let _ = panicking_division_contract(x);
    }));

    let Verdict::Counterexample { class, inputs } = unchecked_inc__axeyum_verdict() else {
        panic!("unrestricted increment must retain its overflow witness");
    };
    assert_eq!(class, "add overflow");
    assert_eq!(witness_u8(&inputs, "x"), 255);

    let mut impossible = checked_inc_contract__axeyum_program();
    impossible.requires = Expr::Binary {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("x".into())),
        rhs: Box::new(Expr::Var("x".into())),
    };
    let Verdict::Unknown { reason } =
        verify_contract_program(&impossible, &default_config()).expect("solver hard error")
    else {
        panic!("a symbolically unsatisfiable precondition must fail closed");
    };
    assert_eq!(reason, "invalid contract: precondition is unsatisfiable");

    let mut partial_postcondition = checked_inc_contract__axeyum_program();
    partial_postcondition.requires = Expr::BoolLit(true);
    partial_postcondition.result = Expr::Var("x".into());
    let Verdict::Unknown { reason } =
        verify_contract_program(&partial_postcondition, &default_config())
            .expect("solver hard error")
    else {
        panic!("a reachable postcondition-evaluation panic must fail closed");
    };
    assert_eq!(
        reason,
        "invalid contract: postcondition may panic on an admitted normal return"
    );
}

#[test]
fn source_contract_complete_u8_population_is_exact() {
    let u8_ty = Ty::Int {
        width: 8,
        signed: false,
    };
    let safe_program = checked_inc_contract__axeyum_program();
    let mut safe_arena = TermArena::new();
    let safe = lower_contract_program(&mut safe_arena, &safe_program)
        .expect("safe source contract must lower");
    assert_eq!(safe.result_ty, u8_ty);
    let [(safe_name, safe_symbol, safe_ty)] = safe.program.param_syms.as_slice() else {
        panic!("safe contract must retain its one u8 parameter");
    };
    assert_eq!(safe_name, "x");
    assert_eq!(*safe_ty, u8_ty);

    let mutated_program = mutated_inc_contract__axeyum_program();
    let mut mutated_arena = TermArena::new();
    let mutated = lower_contract_program(&mut mutated_arena, &mutated_program)
        .expect("mutated source contract must lower");
    assert_eq!(mutated.result_ty, u8_ty);
    let [(mutated_name, mutated_symbol, mutated_ty)] = mutated.program.param_syms.as_slice() else {
        panic!("mutated contract must retain its one u8 parameter");
    };
    assert_eq!(mutated_name, "x");
    assert_eq!(*mutated_ty, u8_ty);

    let mut admitted = 0_u32;
    let mut safe_violations = 0_u32;
    let mut mutated_violations = 0_u32;
    for x in u8::MIN..=u8::MAX {
        let safe_assignment = bind_u8(*safe_symbol, x);
        let safe_requires = bool_value(
            &eval(&safe_arena, safe.requires, &safe_assignment)
                .expect("safe precondition must evaluate"),
        );
        let safe_panics = safe.program.bad_states.iter().any(|bad| {
            bool_value(
                &eval(&safe_arena, bad.term, &safe_assignment)
                    .expect("safe panic predicate must evaluate"),
            )
        });

        let mutated_assignment = bind_u8(*mutated_symbol, x);
        let mutated_requires = bool_value(
            &eval(&mutated_arena, mutated.requires, &mutated_assignment)
                .expect("mutated precondition must evaluate"),
        );
        let mutated_panics = mutated.program.bad_states.iter().any(|bad| {
            bool_value(
                &eval(&mutated_arena, bad.term, &mutated_assignment)
                    .expect("mutated panic predicate must evaluate"),
            )
        });

        assert_eq!(safe_requires, x < 255);
        assert_eq!(mutated_requires, safe_requires);
        assert_eq!(safe_panics, x == 255);
        assert_eq!(mutated_panics, safe_panics);

        if safe_requires {
            admitted += 1;
            assert!(!safe_panics);
            let Value::Bv {
                width: 8,
                value: safe_result,
            } = eval(&safe_arena, safe.result, &safe_assignment)
                .expect("safe retained result must evaluate")
            else {
                panic!("safe retained result must be u8");
            };
            assert_eq!(safe_result, u128::from(checked_inc_contract(x)));
            safe_violations += u32::from(!bool_value(
                &eval(&safe_arena, safe.ensures, &safe_assignment)
                    .expect("safe postcondition must evaluate"),
            ));

            assert!(!mutated_panics);
            let Value::Bv {
                width: 8,
                value: mutated_result,
            } = eval(&mutated_arena, mutated.result, &mutated_assignment)
                .expect("mutated retained result must evaluate")
            else {
                panic!("mutated retained result must be u8");
            };
            assert_eq!(mutated_result, u128::from(mutated_inc_contract(x)));
            mutated_violations += u32::from(!bool_value(
                &eval(&mutated_arena, mutated.ensures, &mutated_assignment)
                    .expect("mutated postcondition must evaluate"),
            ));
        }
    }
    assert_eq!(admitted, 255);
    assert_eq!(safe_violations, 0);
    assert_eq!(mutated_violations, 255);
}
