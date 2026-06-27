//! Integration tests for the typed property SDK.

use axeyum_ir::Value;
use axeyum_property::{Bool, Bv, Property};
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
fn symbolic_trait_lifts_signed_fixed_width_inputs() -> TestResult {
    let mut property = Property::new();
    let byte = property.symbolic::<i8>("byte")?;
    let word = property.symbolic::<i16>("word")?;

    let mut model = Model::new();
    model.set(
        byte.symbol().unwrap(),
        Value::Bv {
            width: 8,
            value: 0xff,
        },
    );
    model.set(
        word.symbol().unwrap(),
        Value::Bv {
            width: 16,
            value: 0x8000,
        },
    );

    assert_eq!(property.concrete::<i8>(&byte, &model)?, Some(-1));
    assert_eq!(property.concrete::<i16>(&word, &model)?, Some(i16::MIN));
    assert_eq!(
        property
            .counterexample(&model)?
            .render_rust_let_bindings()?,
        concat!(
            "let byte: i8 = -1_i8; // BV8 two's-complement\n",
            "let word: i16 = i16::MIN; // BV16 two's-complement\n",
        )
    );
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

#[test]
fn symbolic_struct_builder_uses_named_fields_in_counterexample_order() -> TestResult {
    #[derive(Debug, Clone, Copy)]
    struct TransferExpr {
        enabled: Bool,
        amount: Bv<16>,
        balance: Bv<16>,
    }

    let mut property = Property::new();
    let transfer = property.symbolic_struct("transfer", |fields| {
        Ok(TransferExpr {
            enabled: fields.field::<bool>("enabled")?,
            amount: fields.field::<u16>("amount")?,
            balance: fields.field::<u16>("balance")?,
        })
    })?;

    let goal = transfer.amount.ule(&mut property, transfer.balance)?;
    let outcome = property.prove_minimized(goal)?;
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("expected a minimized counterexample, got {outcome:?}");
    };

    assert_eq!(
        property.concrete::<bool>(&transfer.enabled, &model)?,
        Some(false)
    );
    assert_eq!(property.concrete::<u16>(&transfer.amount, &model)?, Some(1));
    assert_eq!(
        property.concrete::<u16>(&transfer.balance, &model)?,
        Some(0)
    );

    let counterexample = property.counterexample(&model)?;
    assert_eq!(
        counterexample.render_rust_let_bindings()?,
        concat!(
            "let transfer_enabled: bool = false;\n",
            "let transfer_amount: u16 = 0x0001_u16; // BV16\n",
            "let transfer_balance: u16 = 0x0000_u16; // BV16\n",
        )
    );
    Ok(())
}

#[test]
fn symbolic_struct_builder_supports_nested_field_names() -> TestResult {
    let mut property = Property::new();
    let fee = property.symbolic_struct("transfer", |fields| {
        fields.struct_field("limits", |limits| limits.field::<u8>("fee"))
    })?;

    let mut model = Model::new();
    model.set(fee.symbol().unwrap(), Value::Bv { width: 8, value: 3 });

    assert_eq!(property.concrete::<u8>(&fee, &model)?, Some(3));
    assert_eq!(
        property
            .counterexample(&model)?
            .render_rust_let_bindings()?,
        "let transfer_limits_fee: u8 = 0x03_u8; // BV8\n"
    );
    Ok(())
}

#[test]
fn derive_symbolic_supports_named_structs() -> TestResult {
    #[derive(Debug, Clone, PartialEq, Eq, axeyum_property::Symbolic)]
    struct TransferInput {
        enabled: bool,
        amount: u16,
        balance: u16,
    }

    let mut property = Property::new();
    let transfer = property.symbolic::<TransferInput>("transfer")?;
    let goal = transfer.amount.ule(&mut property, transfer.balance)?;

    let outcome = property.prove_minimized(goal)?;
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("expected a minimized counterexample, got {outcome:?}");
    };

    assert_eq!(
        property.concrete::<TransferInput>(&transfer, &model)?,
        Some(TransferInput {
            enabled: false,
            amount: 1,
            balance: 0,
        })
    );
    assert_eq!(
        property
            .counterexample(&model)?
            .render_rust_let_bindings()?,
        concat!(
            "let transfer_enabled: bool = false;\n",
            "let transfer_amount: u16 = 0x0001_u16; // BV16\n",
            "let transfer_balance: u16 = 0x0000_u16; // BV16\n",
        )
    );
    Ok(())
}

#[test]
fn derive_symbolic_supports_signed_fixed_width_fields() -> TestResult {
    #[derive(Debug, Clone, PartialEq, Eq, axeyum_property::Symbolic)]
    struct SignedInput {
        delta: i32,
        limit: i64,
        count: u8,
    }

    let mut property = Property::new();
    let input = property.symbolic::<SignedInput>("input")?;

    let mut model = Model::new();
    model.set(
        input.delta.symbol().unwrap(),
        Value::Bv {
            width: 32,
            value: 0xffff_fffe,
        },
    );
    model.set(
        input.limit.symbol().unwrap(),
        Value::Bv {
            width: 64,
            value: 0x7fff_ffff_ffff_fffe,
        },
    );
    model.set(
        input.count.symbol().unwrap(),
        Value::Bv { width: 8, value: 4 },
    );

    assert_eq!(
        property.concrete::<SignedInput>(&input, &model)?,
        Some(SignedInput {
            delta: -2,
            limit: i64::MAX - 1,
            count: 4,
        })
    );
    assert_eq!(
        property
            .counterexample(&model)?
            .render_rust_let_bindings()?,
        concat!(
            "let input_delta: i32 = -2_i32; // BV32 two's-complement\n",
            "let input_limit: i64 = 9223372036854775806_i64; // BV64 two's-complement\n",
            "let input_count: u8 = 0x04_u8; // BV8\n",
        )
    );
    Ok(())
}

#[test]
fn derive_symbolic_supports_tuple_structs() -> TestResult {
    #[derive(Debug, Clone, PartialEq, Eq, axeyum_property::Symbolic)]
    struct Pair(bool, u8);

    let mut property = Property::new();
    let pair = property.symbolic::<Pair>("pair")?;

    let mut model = Model::new();
    model.set(pair.0.symbol().unwrap(), Value::Bool(true));
    model.set(pair.1.symbol().unwrap(), Value::Bv { width: 8, value: 9 });

    assert_eq!(
        property.concrete::<Pair>(&pair, &model)?,
        Some(Pair(true, 9))
    );
    assert_eq!(
        property
            .counterexample(&model)?
            .render_rust_let_bindings()?,
        concat!(
            "let pair_0: bool = true;\n",
            "let pair_1: u8 = 0x09_u8; // BV8\n",
        )
    );
    Ok(())
}

#[test]
fn derive_symbolic_supports_generic_and_unit_structs() -> TestResult {
    #[derive(Debug, Clone, PartialEq, Eq, axeyum_property::Symbolic)]
    struct Wrapper<T> {
        inner: T,
        enabled: bool,
    }

    #[derive(Debug, Clone, PartialEq, Eq, axeyum_property::Symbolic)]
    struct Empty;

    let mut property = Property::new();
    let wrapper = property.symbolic::<Wrapper<u8>>("wrapper")?;
    property.symbolic::<Empty>("empty")?;

    let mut model = Model::new();
    model.set(
        wrapper.inner.symbol().unwrap(),
        Value::Bv {
            width: 8,
            value: 0x2b,
        },
    );
    model.set(wrapper.enabled.symbol().unwrap(), Value::Bool(true));

    assert_eq!(
        property.concrete::<Wrapper<u8>>(&wrapper, &model)?,
        Some(Wrapper {
            inner: 43,
            enabled: true,
        })
    );
    assert_eq!(property.concrete::<Empty>(&(), &model)?, Some(Empty));
    assert_eq!(
        property
            .counterexample(&model)?
            .render_rust_let_bindings()?,
        concat!(
            "let wrapper_inner: u8 = 0x2b_u8; // BV8\n",
            "let wrapper_enabled: bool = true;\n",
        )
    );
    Ok(())
}
