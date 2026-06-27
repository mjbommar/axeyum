//! Integration tests for the typed property SDK.

use axeyum_ir::Value;
use axeyum_property::Property;
use axeyum_solver::{Model, ProofOutcome};

type TestResult = Result<(), Box<dyn std::error::Error>>;

#[test]
fn proves_trivial_bv_identity_with_evidence() -> TestResult {
    let mut property = Property::new();
    let x = property.bv::<8>("x")?;
    let goal = x.eq(&mut property, x)?;

    let outcome = property.prove(goal)?;
    assert!(matches!(outcome, ProofOutcome::Proved(_)));
    Ok(())
}

#[test]
fn minimized_counterexample_lifts_through_typed_bv_handle() -> TestResult {
    let mut property = Property::new();
    let x = property.bv::<8>("x")?;
    let five = property.bv_const::<8>(5)?;
    let goal = x.ule(&mut property, five)?;

    let outcome = property.prove_minimized(goal)?;
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("expected a minimized counterexample, got {outcome:?}");
    };
    assert_eq!(x.value_u128(&model)?, Some(6));

    let counterexample = property
        .counterexample_from_outcome(&ProofOutcome::Disproved(model.clone()))?
        .expect("disproved outcome should expose a counterexample");
    assert_eq!(
        counterexample.render_rust_let_bindings()?,
        "let x: u8 = 0x06_u8; // BV8\n"
    );
    Ok(())
}

#[test]
fn assumptions_and_int_terms_use_the_same_proof_front_door() -> TestResult {
    let mut property = Property::new();
    let x = property.int("x")?;
    let three = property.int_const(3);
    let four = property.int_const(4);
    let pre = x.le(&mut property, three)?;
    property.assume(pre);
    let goal = x.le(&mut property, four)?;

    let outcome = property.prove(goal)?;
    assert!(matches!(outcome, ProofOutcome::Proved(_)));
    Ok(())
}

#[test]
fn overflow_helper_is_available_on_typed_bv_handles() -> TestResult {
    let mut property = Property::new();
    let x = property.bv::<256>("x")?;
    let y = property.bv::<256>("y")?;
    let overflow = x.umul_overflows(&mut property, y)?;

    assert_eq!(
        property.arena().sort_of(overflow.term()),
        axeyum_ir::Sort::Bool
    );
    assert_eq!(property.counterexample_symbols().len(), 2);
    Ok(())
}

#[test]
fn counterexample_renderer_sanitizes_names_and_builds_test_skeleton() -> TestResult {
    let mut property = Property::new();
    let flag = property.bool("flag-name")?;
    let keyword = property.int("match")?;
    let byte = property.bv::<12>("1 byte")?;

    let mut model = Model::new();
    model.set(flag.symbol().unwrap(), Value::Bool(true));
    model.set(keyword.symbol().unwrap(), Value::Int(-2));
    model.set(
        byte.symbol().unwrap(),
        Value::Bv {
            width: 12,
            value: 0x0abc,
        },
    );

    let counterexample = property.counterexample(&model)?;
    assert_eq!(
        counterexample.render_rust_let_bindings()?,
        concat!(
            "let flag_name: bool = true;\n",
            "let match_: i128 = -2_i128;\n",
            "let _1_byte: u16 = 0xabc_u16; // BV12\n",
        )
    );

    let test = counterexample.render_rust_test(
        "counterexample case",
        "assert!(replay(flag_name, match_, _1_byte));",
    )?;
    assert_eq!(
        test,
        concat!(
            "#[test]\n",
            "fn counterexample_case() {\n",
            "    let flag_name: bool = true;\n",
            "    let match_: i128 = -2_i128;\n",
            "    let _1_byte: u16 = 0xabc_u16; // BV12\n",
            "    assert!(replay(flag_name, match_, _1_byte));\n",
            "}\n",
        )
    );
    Ok(())
}

#[test]
fn symbolic_trait_declares_and_lifts_scalar_inputs() -> TestResult {
    let mut property = Property::new();
    let x = property.symbolic::<u16>("x")?;
    let limit = property.bv_const::<16>(10)?;
    let goal = x.ule(&mut property, limit)?;

    let outcome = property.prove_minimized(goal)?;
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("expected a minimized counterexample, got {outcome:?}");
    };
    assert_eq!(property.concrete::<u16>(&x, &model)?, Some(11));
    Ok(())
}

#[test]
fn symbolic_trait_composes_tuple_inputs_in_deterministic_order() -> TestResult {
    let mut property = Property::new();
    let input = property.symbolic::<(bool, u8, i128)>("input")?;

    let mut model = Model::new();
    model.set(input.0.symbol().unwrap(), Value::Bool(false));
    model.set(
        input.1.symbol().unwrap(),
        Value::Bv {
            width: 8,
            value: 0x2a,
        },
    );
    model.set(input.2.symbol().unwrap(), Value::Int(-7));

    assert_eq!(
        property.concrete::<(bool, u8, i128)>(&input, &model)?,
        Some((false, 42, -7))
    );

    let counterexample = property.counterexample(&model)?;
    assert_eq!(
        counterexample.render_rust_let_bindings()?,
        concat!(
            "let input_0: bool = false;\n",
            "let input_1: u8 = 0x2a_u8; // BV8\n",
            "let input_2: i128 = -7_i128;\n",
        )
    );
    Ok(())
}
