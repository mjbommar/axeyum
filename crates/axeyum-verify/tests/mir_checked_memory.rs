//! Checked authenticated MIR byte-memory gates (T5.1.3, ADR-0288).

use std::fmt::Write as _;
use std::panic::catch_unwind;

use axeyum_ir::{Assignment, TermArena, Value, eval, render};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::{
    BoundedMemoryConfig, reflect_bounded_memory_cfg_checked,
};
use axeyum_verify::reflect::mir::checked::{
    CheckedMirMemory, MirMemoryConfig, ReflectErrorKind, reflect_bounded_memory_checked,
};
use axeyum_verify::reflect::mir::syntax::{MirType, StatementKind, TerminatorKind, parse_function};

const MIR: &str = include_str!("fixtures/mir/rustc197-debug.mir");
const LLVM_ROUNDTRIP: &str = include_str!("fixtures/llvm/clang21_mem2reg_roundtrip.ll");

fn reflect(function: &str) -> CheckedMirMemory {
    reflect_bounded_memory_checked(MIR, &MirMemoryConfig::new(function, 64)).unwrap()
}

fn param(reflected: &CheckedMirMemory, local: u32) -> axeyum_ir::SymbolId {
    reflected
        .params
        .iter()
        .find(|parameter| parameter.local == local)
        .unwrap()
        .symbol
}

fn proved(arena: &mut TermArena, goal: axeyum_ir::TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).unwrap(),
        ProofOutcome::Proved(_)
    )
}

fn implies(
    arena: &mut TermArena,
    premise: axeyum_ir::TermId,
    conclusion: axeyum_ir::TermId,
) -> axeyum_ir::TermId {
    let not_premise = arena.not(premise).unwrap();
    arena.or(not_premise, conclusion).unwrap()
}

fn assignment(reflected: &CheckedMirMemory, scalars: &[(u32, Value)], bytes: &[u8]) -> Assignment {
    let mut assignment = Assignment::new();
    for (local, value) in scalars {
        assignment.set(param(reflected, *local), value.clone());
    }
    assert_eq!(bytes.len(), reflected.region.input.len());
    for (symbol, byte) in reflected.region.input.iter().zip(bytes) {
        assignment.set(
            *symbol,
            Value::Bv {
                width: 8,
                value: u128::from(*byte),
            },
        );
    }
    assignment
}

fn eval_bool(
    reflected: &CheckedMirMemory,
    term: axeyum_ir::TermId,
    assignment: &Assignment,
) -> bool {
    eval(&reflected.arena, term, assignment).unwrap() == Value::Bool(true)
}

fn eval_bv(reflected: &CheckedMirMemory, term: axeyum_ir::TermId, assignment: &Assignment) -> u128 {
    match eval(&reflected.arena, term, assignment).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected bit-vector, got {other:?}"),
    }
}

#[test]
fn authenticated_module_selects_located_typed_write_cfg() {
    let function = parse_function(MIR, "conditional_store").unwrap();
    assert_eq!(function.params.len(), 4);
    assert_eq!(function.params[0].ty, MirType::ByteArray { bytes: 4 });
    assert_eq!(function.blocks.len(), 6);
    assert!(function.span.start < function.span.end);
    assert!(matches!(
        function.blocks[0].terminator.kind,
        TerminatorKind::Switch { .. }
    ));
    assert!(matches!(
        function.blocks[2].statements[0].kind,
        StatementKind::ArrayStore {
            array: 1,
            index: 2,
            ..
        }
    ));

    let missing = parse_function(MIR, "absent").unwrap_err();
    assert_eq!(
        missing.kind(),
        axeyum_verify::reflect::mir::syntax::ParseErrorKind::MissingFunction
    );
    let duplicate = format!("{MIR}\n{MIR}");
    assert_eq!(
        parse_function(&duplicate, "conditional_store")
            .unwrap_err()
            .kind(),
        axeyum_verify::reflect::mir::syntax::ParseErrorKind::DuplicateFunction
    );

    let with_unrelated_unsupported = format!(
        "{MIR}\nfn unrelated(_1: &[u8]) -> u8 {{\n    let mut _0: u8;\n    bb0: {{\n        _0 = copy (*_1)[const 0_usize];\n        return;\n    }}\n}}\n"
    );
    assert_eq!(
        parse_function(&with_unrelated_unsupported, "store_then_load")
            .unwrap()
            .name,
        "store_then_load"
    );
    assert_eq!(
        parse_function(&with_unrelated_unsupported, "unrelated")
            .unwrap_err()
            .kind(),
        axeyum_verify::reflect::mir::syntax::ParseErrorKind::UnsupportedType
    );
}

#[test]
fn store_then_load_has_exact_panic_result_and_final_memory() {
    let mut reflected = reflect("store_then_load");
    let index = reflected.arena.var(param(&reflected, 2));
    let value = reflected.arena.var(param(&reflected, 3));
    let four = reflected.arena.bv_const(64, 4).unwrap();
    let in_bounds = reflected.arena.bv_ult(index, four).unwrap();
    let out_of_bounds = reflected.arena.not(in_bounds).unwrap();
    let panic_exact = reflected.arena.eq(reflected.panic, out_of_bounds).unwrap();
    assert!(proved(&mut reflected.arena, panic_exact));
    let result_same = reflected.arena.eq(reflected.result.value, value).unwrap();
    let guarded = implies(&mut reflected.arena, in_bounds, result_same);
    assert!(proved(&mut reflected.arena, guarded));

    for offset in 0..4 {
        let at = reflected.arena.bv_const(64, offset).unwrap();
        let selected = reflected.arena.eq(index, at).unwrap();
        let input = reflected.arena.var(reflected.region.input[offset as usize]);
        let expected = reflected.arena.ite(selected, value, input).unwrap();
        let memory_equal = reflected
            .arena
            .eq(reflected.region.output[offset as usize], expected)
            .unwrap();
        assert!(proved(&mut reflected.arena, memory_equal));
    }

    let concrete = assignment(
        &reflected,
        &[
            (
                2,
                Value::Bv {
                    width: 64,
                    value: 2,
                },
            ),
            (
                3,
                Value::Bv {
                    width: 8,
                    value: 0xaa,
                },
            ),
        ],
        &[1, 2, 3, 4],
    );
    assert!(!eval_bool(&reflected, reflected.panic, &concrete));
    assert_eq!(eval_bv(&reflected, reflected.result.value, &concrete), 0xaa);
    let output = reflected
        .region
        .output
        .iter()
        .map(|term| eval_bv(&reflected, *term, &concrete))
        .collect::<Vec<_>>();
    assert_eq!(output, [1, 2, 0xaa, 4]);
}

#[test]
fn conditional_path_joins_panic_and_memory_exactly() {
    let mut reflected = reflect("conditional_store");
    let index = reflected.arena.var(param(&reflected, 2));
    let value = reflected.arena.var(param(&reflected, 3));
    let take = reflected.arena.var(param(&reflected, 4));
    let four = reflected.arena.bv_const(64, 4).unwrap();
    let in_bounds = reflected.arena.bv_ult(index, four).unwrap();
    let out_of_bounds = reflected.arena.not(in_bounds).unwrap();
    let expected_panic = reflected.arena.and(take, out_of_bounds).unwrap();
    let panic_exact = reflected.arena.eq(reflected.panic, expected_panic).unwrap();
    assert!(proved(&mut reflected.arena, panic_exact));
    let result_same = reflected.arena.eq(reflected.result.value, value).unwrap();
    let safe = reflected.arena.not(reflected.panic).unwrap();
    let guarded = implies(&mut reflected.arena, safe, result_same);
    assert!(proved(&mut reflected.arena, guarded));

    for offset in 0..4 {
        let at = reflected.arena.bv_const(64, offset).unwrap();
        let selected_index = reflected.arena.eq(index, at).unwrap();
        let selected = reflected.arena.and(take, selected_index).unwrap();
        let input = reflected.arena.var(reflected.region.input[offset as usize]);
        let expected = reflected.arena.ite(selected, value, input).unwrap();
        let memory_equal = reflected
            .arena
            .eq(reflected.region.output[offset as usize], expected)
            .unwrap();
        assert!(proved(&mut reflected.arena, memory_equal));
    }

    for (take_value, index_value, should_panic) in
        [(false, 99, false), (true, 3, false), (true, 4, true)]
    {
        let concrete = assignment(
            &reflected,
            &[
                (
                    2,
                    Value::Bv {
                        width: 64,
                        value: index_value,
                    },
                ),
                (
                    3,
                    Value::Bv {
                        width: 8,
                        value: 0xcc,
                    },
                ),
                (4, Value::Bool(take_value)),
            ],
            &[1, 2, 3, 4],
        );
        assert_eq!(
            eval_bool(&reflected, reflected.panic, &concrete),
            should_panic
        );
    }
}

#[test]
fn memory_accesses_do_not_trust_compiler_asserts() {
    let without_assert = r"
fn unchecked(_1: [u8; 4], _2: usize, _3: u8) -> u8 {
    let mut _0: u8;
    bb0: {
        _1[_2] = copy _3;
        _0 = copy _1[_2];
        return;
    }
}
";
    let mut reflected =
        reflect_bounded_memory_checked(without_assert, &MirMemoryConfig::new("unchecked", 64))
            .unwrap();
    let index = reflected.arena.var(param(&reflected, 2));
    let four = reflected.arena.bv_const(64, 4).unwrap();
    let in_bounds = reflected.arena.bv_ult(index, four).unwrap();
    let expected = reflected.arena.not(in_bounds).unwrap();
    let exact = reflected.arena.eq(reflected.panic, expected).unwrap();
    assert!(proved(&mut reflected.arena, exact));

    let wrong_assert = without_assert.replace(
        "_1[_2] = copy _3;",
        "assert(const true, \"wrong\") -> [success: bb1, unwind continue];\n    }\n    bb1: {\n        _1[_2] = copy _3;",
    );
    let mut wrong =
        reflect_bounded_memory_checked(&wrong_assert, &MirMemoryConfig::new("unchecked", 64))
            .unwrap();
    let index = wrong.arena.var(param(&wrong, 2));
    let four = wrong.arena.bv_const(64, 4).unwrap();
    let in_bounds = wrong.arena.bv_ult(index, four).unwrap();
    let expected = wrong.arena.not(in_bounds).unwrap();
    let exact = wrong.arena.eq(wrong.panic, expected).unwrap();
    assert!(proved(&mut wrong.arena, exact));
}

#[test]
fn checked_path_is_non_panicking_and_errors_are_stable() {
    let malformed = [
        "",
        "fn f(_1: [u8; 4]) -> u8 {",
        "fn f(_1: [u8; 0]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n",
        "fn f(_1: [u8; 4]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        goto -> bb0;\n    }\n}\n",
        "fn f(_1: [u8; 4]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        goto -> bb9;\n    }\n}\n",
    ];
    for input in malformed {
        assert!(
            catch_unwind(|| {
                reflect_bounded_memory_checked(input, &MirMemoryConfig::new("f", 64))
            })
            .is_ok()
        );
    }
    assert_eq!(
        reflect_bounded_memory_checked(malformed[2], &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::RegionSize
    );
    assert_eq!(
        reflect_bounded_memory_checked(malformed[3], &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::CyclicControlFlow
    );
    assert_eq!(
        reflect_bounded_memory_checked(malformed[4], &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::UndefinedBlock
    );
    assert_eq!(
        reflect_bounded_memory_checked(MIR, &MirMemoryConfig::new("checked_read", 32))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::TargetWidth
    );

    let first = reflect("conditional_store");
    let second = reflect("conditional_store");
    assert_eq!(
        first
            .arena
            .symbols()
            .map(|(_, name, sort)| (name.to_owned(), sort))
            .collect::<Vec<_>>(),
        second
            .arena
            .symbols()
            .map(|(_, name, sort)| (name.to_owned(), sort))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        render(&first.arena, first.panic),
        render(&second.arena, second.panic)
    );
    assert_eq!(
        first
            .region
            .output
            .iter()
            .map(|term| render(&first.arena, *term))
            .collect::<Vec<_>>(),
        second
            .region
            .output
            .iter()
            .map(|term| render(&second.arena, *term))
            .collect::<Vec<_>>()
    );
}

#[test]
fn rejected_memory_type_and_control_profiles_keep_stable_classes() {
    let region_257 = "fn f(_1: [u8; 257]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n";
    assert_eq!(
        reflect_bounded_memory_checked(region_257, &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::RegionSize
    );

    let two_arrays = "fn f(_1: [u8; 1], _2: [u8; 1]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n";
    assert_eq!(
        reflect_bounded_memory_checked(two_arrays, &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::RegionCount
    );

    for syntax_error in [
        "fn f(_1: [u16; 1]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n",
        "fn f(_1: [u8; 1], _2: u7) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n",
        "fn f(_1: [u8; 1]) -> u8 {\n    let mut _0: u8;\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n",
        "fn f(_1: [u8; 1]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        call foo() -> [return: bb1, unwind continue];\n    }\n}\n",
    ] {
        assert_eq!(
            reflect_bounded_memory_checked(syntax_error, &MirMemoryConfig::new("f", 64))
                .unwrap_err()
                .kind(),
            ReflectErrorKind::Syntax
        );
    }

    let undefined_local = "fn f(_1: [u8; 1]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = copy _9;\n        return;\n    }\n}\n";
    assert_eq!(
        reflect_bounded_memory_checked(undefined_local, &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::UndefinedLocal
    );

    let duplicate_assignment = "fn f(_1: [u8; 1]) -> u8 {\n    let mut _0: u8;\n    bb0: {\n        _0 = const 0_u8;\n        _0 = const 1_u8;\n        return;\n    }\n}\n";
    assert_eq!(
        reflect_bounded_memory_checked(duplicate_assignment, &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::DuplicateDefinition
    );

    let invalid_signed_constant = "fn f(_1: [u8; 1]) -> i8 {\n    let mut _0: i8;\n    bb0: {\n        _0 = const 255_i8;\n        return;\n    }\n}\n";
    assert_eq!(
        reflect_bounded_memory_checked(invalid_signed_constant, &MirMemoryConfig::new("f", 64),)
            .unwrap_err()
            .kind(),
        ReflectErrorKind::TypeMismatch
    );

    let mut expansive = String::from("fn f(_1: [u8; 1], _2: bool) -> u8 {\n    let mut _0: u8;\n");
    for block in 0..13 {
        write!(
            expansive,
            "    bb{block}: {{\n        switchInt(copy _2) -> [0: bb{}, otherwise: bb{}];\n    }}\n",
            block + 1,
            block + 1
        )
        .unwrap();
    }
    expansive.push_str("    bb13: {\n        _0 = const 0_u8;\n        return;\n    }\n}\n");
    assert_eq!(
        reflect_bounded_memory_checked(&expansive, &MirMemoryConfig::new("f", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::ExecutionLimit
    );
}

#[test]
fn source_replay_and_mir_llvm_roundtrip_specs_agree() {
    fn store_then_load(mut buf: [u8; 4], index: usize, value: u8) -> u8 {
        buf[index] = value;
        buf[index]
    }

    fn conditional_store(mut buf: [u8; 4], index: usize, value: u8, take: bool) -> u8 {
        if take {
            buf[index] = value;
            buf[index]
        } else {
            value
        }
    }

    assert_eq!(store_then_load([1, 2, 3, 4], 2, 0xaa), 0xaa);
    assert!(catch_unwind(|| store_then_load([1, 2, 3, 4], 4, 0xaa)).is_err());
    assert_eq!(conditional_store([1, 2, 3, 4], 2, 0xbb, true), 0xbb);
    assert_eq!(conditional_store([1, 2, 3, 4], 99, 0xbb, false), 0xbb);
    assert!(catch_unwind(|| conditional_store([1, 2, 3, 4], 4, 0xbb, true)).is_err());

    let mut mir = reflect("store_then_load");
    let mir_index = mir.arena.var(param(&mir, 2));
    let mir_value = mir.arena.var(param(&mir, 3));
    let four = mir.arena.bv_const(64, 4).unwrap();
    let mir_in_bounds = mir.arena.bv_ult(mir_index, four).unwrap();
    let mir_result_equal = mir.arena.eq(mir.result.value, mir_value).unwrap();
    let mir_spec = implies(&mut mir.arena, mir_in_bounds, mir_result_equal);
    assert!(proved(&mut mir.arena, mir_spec));

    let mut llvm =
        reflect_bounded_memory_cfg_checked(LLVM_ROUNDTRIP, &BoundedMemoryConfig::new("0", 4))
            .unwrap();
    let llvm_index_symbol = llvm
        .params
        .iter()
        .find(|(name, _, _)| name == "1")
        .unwrap()
        .1;
    let llvm_value_symbol = llvm
        .params
        .iter()
        .find(|(name, _, _)| name == "2")
        .unwrap()
        .1;
    let llvm_index = llvm.arena.var(llvm_index_symbol);
    let llvm_value = llvm.arena.var(llvm_value_symbol);
    let four = llvm.arena.bv_const(64, 4).unwrap();
    let llvm_in_bounds = llvm.arena.bv_ult(llvm_index, four).unwrap();
    let defined_exact = llvm.arena.eq(llvm.result.defined, llvm_in_bounds).unwrap();
    assert!(proved(&mut llvm.arena, defined_exact));
    let llvm_result_equal = llvm.arena.eq(llvm.result.value, llvm_value).unwrap();
    let llvm_spec = implies(&mut llvm.arena, llvm_in_bounds, llvm_result_equal);
    assert!(proved(&mut llvm.arena, llvm_spec));
}
