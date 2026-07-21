//! Typed scalar LLVM syntax and definedness gates (T5.1.2, ADR-0281).

use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::{
    checked::{ReflectErrorKind, reflect_scalar_checked, reflect_scalar_into_checked},
    reflect_into,
    syntax::{
        BinaryOpcode, CallResultRange, CastOpcode, IntPredicate, Intrinsic, ParseErrorKind,
        ScalarInstructionKind, SemanticFlag, parse_function, parse_scalar_cfg,
        parse_scalar_instruction, render_scalar_cfg,
    },
};

const CLANG_PICK: &str = include_str!("fixtures/llvm/clang21_pick.ll");
const RUSTC_PICK: &str = include_str!("fixtures/llvm/rustc197_pick.ll");
const CLANG_EXTEND: &str = include_str!("fixtures/llvm/clang21_extend.ll");
const NOISE_ALPHABET: &[u8] = b"define@%(){}[]<>,:=; abcdefghijklmnopqrstuvwxyz0123456789\"\\";

fn typed_kinds(ll: &str) -> Vec<ScalarInstructionKind> {
    parse_function(ll)
        .unwrap()
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .map(|instruction| parse_scalar_instruction(instruction).unwrap().kind)
        .collect()
}

#[test]
fn typed_ctlz_and_call_result_range_round_trip_exactly() {
    let ll = "define i32 @f(i32 %x) {\n%r = tail call range(i32 0, 33) i32 @llvm.ctlz.i32(i32 %x, i1 true)\nret i32 %r\n}\n";
    let kinds = typed_kinds(ll);
    assert!(matches!(
        &kinds[0],
        ScalarInstructionKind::CountLeadingZeros {
            dest,
            tail: true,
            result_range: Some(CallResultRange {
                width: 32,
                lower: 0,
                upper: 33,
            }),
            width: 32,
            operand: axeyum_verify::reflect::llvm::syntax::Operand::Local(operand),
            zero_is_poison: true,
        } if dest == "r" && operand == "x"
    ));

    let cfg = parse_scalar_cfg(&parse_function(ll).unwrap()).unwrap();
    let canonical = render_scalar_cfg(&cfg);
    assert!(canonical.contains(
        "%\"r\" = tail call range(i32 0, 33) i32 @\"llvm.ctlz.i32\"(i32 %\"x\", i1 true)"
    ));
    let reparsed = parse_scalar_cfg(&parse_function(&canonical).unwrap()).unwrap();
    assert_eq!(canonical, render_scalar_cfg(&reparsed));
}

#[test]
fn ctlz_and_call_result_ranges_fail_closed_at_frozen_boundaries() {
    let cases = [
        (
            "%r = call range(i8 -1, 9) i8 @llvm.ctlz.i8(i8 %x, i1 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call range(i8 0, 256) i8 @llvm.ctlz.i8(i8 %x, i1 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call range(i8 8, 8) i8 @llvm.ctlz.i8(i8 %x, i1 false)",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "%r = call range(i8 9, 8) i8 @llvm.ctlz.i8(i8 %x, i1 false)",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "%r = call range(i16 0, 9) i8 @llvm.ctlz.i8(i8 %x, i1 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call range(i8 0, 9) range(i8 0, 9) i8 @llvm.ctlz.i8(i8 %x, i1 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call range(i8 0, 9) i8 @ordinary(i8 %x)",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "%r = call i8 @llvm.ctlz.i16(i8 %x, i1 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call i8 @llvm.ctlz.i8(i16 %x, i1 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call i8 @llvm.ctlz.i8(i8 %x, i8 false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call i8 @llvm.ctlz.i8(i8 %x, i1 %flag)",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "%r = call i8 @llvm.ctlz.i8(i8 %x, i1 noundef false)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call i8 @llvm.ctlz.i8(i8 %x, i1 false, i1 true)",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "%r = call i8 @llvm.cttz.i8(i8 %x, i1 false)",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "%r = call i8 @llvm.ctpop.i8(i8 %x)",
            ParseErrorKind::UnsupportedSemantics,
        ),
    ];
    for (instruction, expected) in cases {
        let ll = format!("define i8 @f(i8 %x, i1 %flag) {{\n{instruction}\nret i8 %x\n}}\n");
        let function = parse_function(&ll).unwrap();
        let error = parse_scalar_instruction(&function.blocks[0].instructions[0]).unwrap_err();
        assert_eq!(error.kind(), expected, "{instruction}");
        assert_eq!(error.span().line, 2, "{instruction}");
        assert!(error.span().start < error.span().end, "{instruction}");
    }
}

#[test]
fn unmodified_clang_and_rustc_pick_fixtures_converge_to_select_then_return() {
    let clang = typed_kinds(CLANG_PICK);
    let rustc = typed_kinds(RUSTC_PICK);
    assert_eq!(clang.len(), 2);
    assert_eq!(rustc.len(), 2);

    for kinds in [&clang, &rustc] {
        assert!(matches!(
            &kinds[0],
            ScalarInstructionKind::Select { width: 32, .. }
        ));
        assert!(matches!(
            &kinds[1],
            ScalarInstructionKind::Return { width: 32, .. }
        ));
    }
}

#[test]
fn every_scalar_opcode_predicate_cast_intrinsic_and_flag_is_typed() {
    let ll = r"
define i32 @all(i32 %a, i32 %b, i8 %small, i1 %cond) {
entry:
  %add = add nuw nsw i32 %a, %b
  %sub = sub nuw nsw i32 %a, %b
  %mul = mul nuw nsw i32 %a, %b
  %and = and i32 %a, %b
  %or = or disjoint i32 %a, %b
  %xor = xor i32 %a, -1
  %shl = shl nuw nsw i32 %a, %b
  %lshr = lshr exact i32 %a, %b
  %ashr = ashr exact i32 %a, %b
  %udiv = udiv exact i32 %a, %b
  %sdiv = sdiv exact i32 %a, %b
  %urem = urem i32 %a, %b
  %srem = srem i32 %a, %b
  %cmp = icmp sge i32 %a, %b
  %sel = select i1 %cond, i32 %a, i32 %b
  %z = zext nneg i8 %small to i32
  %s = sext i8 %small to i32
  %tnu = trunc nuw i32 %a to i8
  %tns = trunc nsw i32 %a to i8
  %min = tail call i32 @llvm.umin.i32(i32 %a, i32 %b)
  %max = call i32 @llvm.umax.i32(i32 %a, i32 %b)
  ret i32 %sel
}
";
    let kinds = typed_kinds(ll);
    let binaries: Vec<_> = kinds
        .iter()
        .filter_map(|kind| match kind {
            ScalarInstructionKind::Binary { opcode, flags, .. } => Some((*opcode, flags.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(
        binaries
            .iter()
            .map(|(opcode, _)| *opcode)
            .collect::<Vec<_>>(),
        vec![
            BinaryOpcode::Add,
            BinaryOpcode::Sub,
            BinaryOpcode::Mul,
            BinaryOpcode::And,
            BinaryOpcode::Or,
            BinaryOpcode::Xor,
            BinaryOpcode::Shl,
            BinaryOpcode::Lshr,
            BinaryOpcode::Ashr,
            BinaryOpcode::Udiv,
            BinaryOpcode::Sdiv,
            BinaryOpcode::Urem,
            BinaryOpcode::Srem,
        ]
    );
    assert_eq!(binaries[0].1, vec![SemanticFlag::Nuw, SemanticFlag::Nsw]);
    assert_eq!(binaries[4].1, vec![SemanticFlag::Disjoint]);
    assert_eq!(binaries[7].1, vec![SemanticFlag::Exact]);
    assert!(matches!(
        kinds[13],
        ScalarInstructionKind::Icmp {
            predicate: IntPredicate::Sge,
            ..
        }
    ));
    assert!(matches!(
        kinds[15],
        ScalarInstructionKind::Cast {
            opcode: CastOpcode::Zext,
            ref flags,
            ..
        } if flags == &[SemanticFlag::Nneg]
    ));
    assert!(matches!(
        kinds[19],
        ScalarInstructionKind::Intrinsic {
            intrinsic: Intrinsic::UnsignedMin,
            ..
        }
    ));
    assert!(matches!(
        kinds[20],
        ScalarInstructionKind::Intrinsic {
            intrinsic: Intrinsic::UnsignedMax,
            ..
        }
    ));
}

#[test]
fn every_predicate_and_quoted_name_is_typed() {
    let predicates = [
        ("eq", IntPredicate::Eq),
        ("ne", IntPredicate::Ne),
        ("ult", IntPredicate::Ult),
        ("ule", IntPredicate::Ule),
        ("ugt", IntPredicate::Ugt),
        ("uge", IntPredicate::Uge),
        ("slt", IntPredicate::Slt),
        ("sle", IntPredicate::Sle),
        ("sgt", IntPredicate::Sgt),
        ("sge", IntPredicate::Sge),
    ];
    for (spelling, expected) in predicates {
        let ll = format!(
            "define i1 @cmp(i32 %a, i32 %b) {{\n%r = icmp {spelling} i32 %a, %b\nret i1 %r\n}}\n"
        );
        assert!(matches!(
            typed_kinds(&ll)[0],
            ScalarInstructionKind::Icmp { predicate, .. } if predicate == expected
        ));
    }

    let quoted = parse_function(
        "define i8 @\"quoted fn\"(i8 %\"input value\") {\n%\"output value\" = xor i8 %\"input value\", -1\nret i8 %\"output value\"\n}\n",
    )
    .unwrap();
    let typed = parse_scalar_instruction(&quoted.blocks[0].instructions[0]).unwrap();
    assert!(matches!(
        typed.kind,
        ScalarInstructionKind::Binary {
            dest,
            lhs: axeyum_verify::reflect::llvm::syntax::Operand::Local(lhs),
            ..
        } if dest == "output value" && lhs == "input value"
    ));
}

#[test]
fn typed_parser_fails_closed_with_located_errors() {
    let cases = [
        (
            "define i8 @f(i8 %a) {\n%x = add bogus i8 %a, 1\nret i8 %x\n}\n",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "define i8 @f(i8 %a) {\n%x = and nuw i8 %a, 1\nret i8 %x\n}\n",
            ParseErrorKind::MalformedInstruction,
        ),
        (
            "define i8 @f(i8 %a) {\n%x = fadd float 0.0, 1.0\nret i8 %a\n}\n",
            ParseErrorKind::UnsupportedInstruction,
        ),
        (
            "define i8 @f(i8 %a) {\n%x = add i8 poison, 1\nret i8 %x\n}\n",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "define i8 @f(i8 %a) {\nret i8\n}\n",
            ParseErrorKind::MalformedInstruction,
        ),
    ];
    for (ll, expected) in cases {
        let function = parse_function(ll).unwrap();
        let bad = function
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .find_map(|instruction| parse_scalar_instruction(instruction).err())
            .expect("one instruction must fail");
        assert_eq!(bad.kind(), expected, "{ll}");
        assert!(bad.span().start < bad.span().end);
        assert!(bad.span().line >= 2);
    }
}

fn eval_defined(ll: &str, values: &[(&str, u32, u128)]) -> bool {
    let reflected = reflect_scalar_checked(ll).unwrap();
    let mut assignment = Assignment::new();
    for (name, width, value) in values {
        let symbol = reflected
            .params
            .iter()
            .find(|(param, _, _)| param == name)
            .unwrap()
            .1;
        assignment.set(
            symbol,
            if *width == 1 {
                Value::Bool(*value != 0)
            } else {
                Value::Bv {
                    width: *width,
                    value: *value,
                }
            },
        );
    }
    eval(&reflected.arena, reflected.result.defined, &assignment).unwrap() == Value::Bool(true)
}

#[test]
fn compiler_emitted_flags_are_proved_defined_and_violations_are_visible() {
    let mut reflected = reflect_scalar_checked(CLANG_EXTEND).unwrap();
    assert!(matches!(
        prove(
            &mut reflected.arena,
            &[],
            reflected.result.defined,
            &SolverConfig::default()
        )
        .unwrap(),
        ProofOutcome::Proved(_)
    ));

    let unsigned_add = "define i8 @f(i8 %a, i8 %b) {\n%x = add nuw i8 %a, %b\nret i8 %x\n}\n";
    assert!(eval_defined(unsigned_add, &[("a", 8, 1), ("b", 8, 2)]));
    assert!(!eval_defined(unsigned_add, &[("a", 8, 255), ("b", 8, 1)]));

    let signed_add = "define i8 @f(i8 %a, i8 %b) {\n%x = add nsw i8 %a, %b\nret i8 %x\n}\n";
    assert!(!eval_defined(signed_add, &[("a", 8, 127), ("b", 8, 1)]));

    let disjoint = "define i8 @f(i8 %a, i8 %b) {\n%x = or disjoint i8 %a, %b\nret i8 %x\n}\n";
    assert!(!eval_defined(disjoint, &[("a", 8, 3), ("b", 8, 1)]));

    let bool_disjoint = "define i1 @f(i1 %a, i1 %b) {\n%x = or disjoint i1 %a, %b\nret i1 %x\n}\n";
    assert!(eval_defined(bool_disjoint, &[("a", 1, 1), ("b", 1, 0)]));
    assert!(!eval_defined(bool_disjoint, &[("a", 1, 1), ("b", 1, 1)]));

    let unsigned_shift = "define i8 @f(i8 %a) {\n%x = shl nuw i8 %a, 1\nret i8 %x\n}\n";
    assert!(!eval_defined(unsigned_shift, &[("a", 8, 128)]));

    let signed_shift = "define i8 @f(i8 %a) {\n%x = shl nsw i8 %a, 1\nret i8 %x\n}\n";
    assert!(!eval_defined(signed_shift, &[("a", 8, 64)]));

    let lshr_exact = "define i8 @f(i8 %a) {\n%x = lshr exact i8 %a, 1\nret i8 %x\n}\n";
    assert!(!eval_defined(lshr_exact, &[("a", 8, 1)]));

    let zext_nneg = "define i16 @f(i8 %a) {\n%x = zext nneg i8 %a to i16\nret i16 %x\n}\n";
    assert!(!eval_defined(zext_nneg, &[("a", 8, 128)]));

    let bool_zext_nneg = "define i8 @f(i1 %a) {\n%x = zext nneg i1 %a to i8\nret i8 %x\n}\n";
    assert!(eval_defined(bool_zext_nneg, &[("a", 1, 0)]));
    assert!(!eval_defined(bool_zext_nneg, &[("a", 1, 1)]));

    let unsigned_truncation = "define i8 @f(i16 %a) {\n%x = trunc nuw i16 %a to i8\nret i8 %x\n}\n";
    assert!(!eval_defined(unsigned_truncation, &[("a", 16, 256)]));

    let signed_truncation = "define i8 @f(i16 %a) {\n%x = trunc nsw i16 %a to i8\nret i8 %x\n}\n";
    assert!(!eval_defined(signed_truncation, &[("a", 16, 128)]));
}

#[test]
fn select_only_propagates_definedness_from_the_chosen_arm() {
    let ll = r"
define i32 @day(i32 %x) {
entry:
  %in = icmp ult i32 %x, 3
  %offset = add nsw i32 %x, 7
  %result = select i1 %in, i32 %offset, i32 0
  ret i32 %result
}
";
    let mut reflected = reflect_scalar_checked(ll).unwrap();
    assert!(matches!(
        prove(
            &mut reflected.arena,
            &[],
            reflected.result.defined,
            &SolverConfig::default()
        )
        .unwrap(),
        ProofOutcome::Proved(_)
    ));
}

#[test]
fn shift_and_division_undefined_cases_do_not_inherit_total_bv_semantics() {
    let shift = "define i8 @f(i8 %a, i8 %b) {\n%x = shl i8 %a, %b\nret i8 %x\n}\n";
    assert!(!eval_defined(shift, &[("a", 8, 1), ("b", 8, 8)]));

    let exact = "define i8 @f(i8 %a, i8 %b) {\n%x = udiv exact i8 %a, %b\nret i8 %x\n}\n";
    assert!(!eval_defined(exact, &[("a", 8, 6), ("b", 8, 0)]));
    assert!(!eval_defined(exact, &[("a", 8, 5), ("b", 8, 2)]));
    assert!(eval_defined(exact, &[("a", 8, 6), ("b", 8, 2)]));

    let signed = "define i8 @f(i8 %a, i8 %b) {\n%x = sdiv i8 %a, %b\nret i8 %x\n}\n";
    assert!(!eval_defined(signed, &[("a", 8, 128), ("b", 8, 255)]));
}

#[test]
fn checked_and_legacy_values_agree_on_the_flag_free_fragment() {
    let ll = "define i8 @f(i8 %a, i8 %b) {\n%x = xor i8 %a, %b\nret i8 %x\n}\n";
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let legacy = reflect_into(&mut arena, &[a, b], ll);
    let checked = reflect_scalar_into_checked(&mut arena, &[a, b], ll).unwrap();
    let same = arena.eq(legacy, checked.value).unwrap();
    let both = arena.and(same, checked.defined).unwrap();
    assert!(matches!(
        prove(&mut arena, &[], both, &SolverConfig::default()).unwrap(),
        ProofOutcome::Proved(_)
    ));
}

#[test]
fn checked_reflection_rejects_width_mismatch_and_never_panics_on_noise() {
    let mismatch = "define i8 @f(i8 %a) {\n%x = add i16 %a, 1\nret i16 %x\n}\n";
    let error = reflect_scalar_checked(mismatch).unwrap_err();
    assert_eq!(error.kind(), ReflectErrorKind::WidthMismatch);

    let mut state = 0xbb67_ae85_84ca_a73b_u64;
    for case in 0..1_024 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let len = usize::from(state.to_le_bytes()[0] & 63);
        let mut input = String::with_capacity(len);
        for _ in 0..len {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            input.push(
                NOISE_ALPHABET[usize::from(state.to_le_bytes()[0]) % NOISE_ALPHABET.len()] as char,
            );
        }
        let result = std::panic::catch_unwind(|| {
            if let Ok(function) = parse_function(&input) {
                for instruction in function.blocks.iter().flat_map(|block| &block.instructions) {
                    let _ = parse_scalar_instruction(instruction);
                }
            }
            let _ = reflect_scalar_checked(&input);
        });
        assert!(result.is_ok(), "case {case} panicked: {input:?}");
    }
}
