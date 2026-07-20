//! Checked bounded LLVM byte-memory gates (T5.1.5, ADR-0286).

use std::io::Write as _;
use std::panic::catch_unwind;
use std::process::{Command, Stdio};

use axeyum_ir::{Assignment, TermArena, Value, eval, render};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::{
    BoundedMemoryConfig, CheckedMemoryCfgReflected, ReflectErrorKind,
    reflect_bounded_memory_cfg_checked,
};
use axeyum_verify::reflect::llvm::syntax::{
    GepFlag, ScalarInstructionKind, SourceSpan, parse_function, parse_scalar_cfg, render_scalar_cfg,
};

const READ_BE16: &str = include_str!("fixtures/llvm/clang21_read_be16.ll");
const GET_MASKED: &str = include_str!("fixtures/llvm/clang21_get_masked.ll");
const ROUNDTRIP: &str = include_str!("fixtures/llvm/clang21_mem2reg_roundtrip.ll");

fn config(bytes: usize) -> BoundedMemoryConfig {
    BoundedMemoryConfig::new("0", bytes)
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

fn scalar_symbol(reflected: &CheckedMemoryCfgReflected, name: &str) -> axeyum_ir::SymbolId {
    reflected
        .params
        .iter()
        .find(|(found, _, _)| found == name)
        .unwrap()
        .1
}

fn assignment(
    reflected: &CheckedMemoryCfgReflected,
    scalars: &[(&str, u32, u128)],
    bytes: &[u8],
) -> Assignment {
    let mut result = Assignment::new();
    for (name, width, value) in scalars {
        result.set(
            scalar_symbol(reflected, name),
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
    assert_eq!(bytes.len(), reflected.region.input.len());
    for (symbol, byte) in reflected.region.input.iter().zip(bytes) {
        result.set(
            *symbol,
            Value::Bv {
                width: 8,
                value: u128::from(*byte),
            },
        );
    }
    result
}

fn eval_bool(
    reflected: &CheckedMemoryCfgReflected,
    term: axeyum_ir::TermId,
    assignment: &Assignment,
) -> bool {
    eval(&reflected.arena, term, assignment).unwrap() == Value::Bool(true)
}

fn eval_bv(
    reflected: &CheckedMemoryCfgReflected,
    term: axeyum_ir::TermId,
    assignment: &Assignment,
) -> u128 {
    match eval(&reflected.arena, term, assignment).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected bit-vector, got {other:?}"),
    }
}

fn without_spans(
    mut cfg: axeyum_verify::reflect::llvm::syntax::ScalarCfg,
) -> axeyum_verify::reflect::llvm::syntax::ScalarCfg {
    let absent = SourceSpan {
        start: 0,
        end: 0,
        line: 0,
        column: 0,
    };
    for parameter in &mut cfg.params {
        parameter.span = absent;
    }
    for block in &mut cfg.blocks {
        block.span = absent;
        for phi in &mut block.phis {
            phi.span = absent;
        }
        for instruction in &mut block.instructions {
            instruction.span = absent;
        }
        block.terminator.span = absent;
    }
    cfg
}

#[test]
fn compiler_memory_forms_are_typed_and_canonical() {
    for ll in [READ_BE16, GET_MASKED, ROUNDTRIP] {
        let parsed = parse_scalar_cfg(&parse_function(ll).unwrap()).unwrap();
        let rendered = render_scalar_cfg(&parsed);
        let reparsed = parse_scalar_cfg(&parse_function(&rendered).unwrap()).unwrap();
        assert_eq!(without_spans(parsed), without_spans(reparsed.clone()));
        assert_eq!(rendered, render_scalar_cfg(&reparsed));

        for (label, text) in [("source", ll), ("canonical", rendered.as_str())] {
            let Ok(mut child) = Command::new("llvm-as")
                .args(["-o", "/dev/null", "-"])
                .stdin(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
            else {
                eprintln!("skipping external llvm-as gate: tool is not installed");
                break;
            };
            child
                .stdin
                .take()
                .unwrap()
                .write_all(text.as_bytes())
                .unwrap();
            let output = child.wait_with_output().unwrap();
            assert!(
                output.status.success(),
                "llvm-as rejected {label} memory CFG: {}\n{text}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }

    let roundtrip = parse_scalar_cfg(&parse_function(ROUNDTRIP).unwrap()).unwrap();
    assert!(matches!(
        &roundtrip.blocks[0].instructions[0].kind,
        ScalarInstructionKind::GetElementPtr {
            flags,
            element_width: 8,
            index_width: 64,
            ..
        } if flags == &[GepFlag::InBounds, GepFlag::Nuw]
    ));
    assert!(matches!(
        &roundtrip.blocks[0].instructions[1].kind,
        ScalarInstructionKind::Store {
            width: 8,
            align: 1,
            ..
        }
    ));
    assert!(matches!(
        &roundtrip.blocks[0].instructions[3].kind,
        ScalarInstructionKind::Load {
            width: 8,
            align: 1,
            ..
        }
    ));
}

#[test]
fn fixed_byte_reads_are_value_correct_and_defined() {
    let mut reflected = reflect_bounded_memory_cfg_checked(READ_BE16, &config(2)).unwrap();
    let b0 = reflected.arena.var(reflected.region.input[0]);
    let b1 = reflected.arena.var(reflected.region.input[1]);
    let hi = reflected.arena.zero_ext(8, b0).unwrap();
    let eight = reflected.arena.bv_const(16, 8).unwrap();
    let shifted = reflected.arena.bv_shl(hi, eight).unwrap();
    let lo = reflected.arena.zero_ext(8, b1).unwrap();
    let expected = reflected.arena.bv_or(shifted, lo).unwrap();
    let same = reflected
        .arena
        .eq(reflected.result.value, expected)
        .unwrap();
    assert!(proved(&mut reflected.arena, same));
    assert!(proved(&mut reflected.arena, reflected.result.defined));

    let asg = assignment(&reflected, &[], &[0x12, 0x34]);
    assert_eq!(eval_bv(&reflected, reflected.result.value, &asg), 0x1234);
    assert!(eval_bool(&reflected, reflected.result.defined, &asg));
}

#[test]
fn symbolic_reads_have_exact_bounds_definedness() {
    let unmasked = r"
define i8 @get(ptr noundef readonly %0, i64 noundef %1) {
  %p = getelementptr inbounds i8, ptr %0, i64 %1
  %v = load i8, ptr %p, align 1
  ret i8 %v
}
";
    let mut reflected = reflect_bounded_memory_cfg_checked(unmasked, &config(4)).unwrap();
    let index = reflected.arena.var(scalar_symbol(&reflected, "1"));
    let four = reflected.arena.bv_const(64, 4).unwrap();
    let in_bounds = reflected.arena.bv_ult(index, four).unwrap();
    let exact = reflected
        .arena
        .eq(reflected.result.defined, in_bounds)
        .unwrap();
    assert!(proved(&mut reflected.arena, exact));

    let mut expected = reflected.arena.var(reflected.region.input[0]);
    for byte in 1..4 {
        let offset = reflected.arena.bv_const(64, byte).unwrap();
        let selected = reflected.arena.eq(index, offset).unwrap();
        let value = reflected.arena.var(reflected.region.input[byte as usize]);
        expected = reflected.arena.ite(selected, value, expected).unwrap();
    }
    let value_same = reflected
        .arena
        .eq(reflected.result.value, expected)
        .unwrap();
    let guarded = implies(&mut reflected.arena, reflected.result.defined, value_same);
    assert!(proved(&mut reflected.arena, guarded));

    let oob = assignment(&reflected, &[("1", 64, 4)], &[10, 11, 12, 13]);
    assert!(!eval_bool(&reflected, reflected.result.defined, &oob));

    let mut masked = reflect_bounded_memory_cfg_checked(GET_MASKED, &config(4)).unwrap();
    assert!(proved(&mut masked.arena, masked.result.defined));
    for index in [0, 1, 2, 3, 4, u32::MAX] {
        let asg = assignment(&masked, &[("1", 32, u128::from(index))], &[10, 11, 12, 13]);
        assert!(eval_bool(&masked, masked.result.defined, &asg));
        assert_eq!(
            eval_bv(&masked, masked.result.value, &asg),
            u128::from([10_u8, 11, 12, 13][(index & 3) as usize])
        );
    }
}

#[test]
fn store_load_roundtrip_and_final_memory_are_exact() {
    let mut reflected = reflect_bounded_memory_cfg_checked(ROUNDTRIP, &config(4)).unwrap();
    let index = reflected.arena.var(scalar_symbol(&reflected, "1"));
    let value = reflected.arena.var(scalar_symbol(&reflected, "2"));
    let four = reflected.arena.bv_const(64, 4).unwrap();
    let in_bounds = reflected.arena.bv_ult(index, four).unwrap();
    let defined_same = reflected
        .arena
        .eq(reflected.result.defined, in_bounds)
        .unwrap();
    assert!(proved(&mut reflected.arena, defined_same));
    let result_same = reflected.arena.eq(reflected.result.value, value).unwrap();
    let guarded = implies(&mut reflected.arena, in_bounds, result_same);
    assert!(proved(&mut reflected.arena, guarded));

    for byte in 0..4 {
        let at = reflected.arena.bv_const(64, byte).unwrap();
        let selected = reflected.arena.eq(index, at).unwrap();
        let input = reflected.arena.var(reflected.region.input[byte as usize]);
        let expected = reflected.arena.ite(selected, value, input).unwrap();
        let same = reflected
            .arena
            .eq(reflected.region.output[byte as usize].value, expected)
            .unwrap();
        assert!(proved(&mut reflected.arena, same));
        assert!(proved(
            &mut reflected.arena,
            reflected.region.output[byte as usize].defined
        ));
    }

    let asg = assignment(&reflected, &[("1", 64, 2), ("2", 8, 0xaa)], &[1, 2, 3, 4]);
    assert!(eval_bool(&reflected, reflected.result.defined, &asg));
    assert_eq!(eval_bv(&reflected, reflected.result.value, &asg), 0xaa);
    let output = reflected
        .region
        .output
        .iter()
        .map(|byte| eval_bv(&reflected, byte.value, &asg))
        .collect::<Vec<_>>();
    assert_eq!(output, [1, 2, 0xaa, 4]);
}

#[test]
fn poison_storage_and_pointer_ub_remain_distinct() {
    let store_only = r"
define i8 @store_poison(ptr noundef %0, i8 noundef %1) {
  %v = add nsw i8 %1, 1
  store i8 %v, ptr %0, align 1
  ret i8 7
}
";
    let mut stored = reflect_bounded_memory_cfg_checked(store_only, &config(1)).unwrap();
    assert!(proved(&mut stored.arena, stored.result.defined));
    let asg = assignment(&stored, &[("1", 8, 127)], &[0]);
    assert!(eval_bool(&stored, stored.result.defined, &asg));
    assert!(!eval_bool(&stored, stored.region.output[0].defined, &asg));

    let store_load = r"
define i8 @load_poison(ptr noundef %0, i8 noundef %1) {
  %v = add nsw i8 %1, 1
  store i8 %v, ptr %0, align 1
  %r = load i8, ptr %0, align 1
  ret i8 %r
}
";
    let loaded = reflect_bounded_memory_cfg_checked(store_load, &config(1)).unwrap();
    let asg = assignment(&loaded, &[("1", 8, 127)], &[0]);
    assert!(!eval_bool(&loaded, loaded.result.defined, &asg));

    let unused_poison = r"
define i8 @unused(ptr noundef %0) {
  %p = getelementptr inbounds i8, ptr %0, i64 2
  ret i8 7
}
";
    let mut unused = reflect_bounded_memory_cfg_checked(unused_poison, &config(1)).unwrap();
    assert!(proved(&mut unused.arena, unused.result.defined));

    let one_past = r"
define i8 @one_past(ptr noundef %0) {
  %p = getelementptr inbounds i8, ptr %0, i64 1
  %v = load i8, ptr %p, align 1
  ret i8 %v
}
";
    let one_past = reflect_bounded_memory_cfg_checked(one_past, &config(1)).unwrap();
    assert!(!eval_bool(
        &one_past,
        one_past.result.defined,
        &assignment(&one_past, &[], &[9])
    ));
}

#[test]
fn gep_bounds_wrap_flags_and_pointer_names_are_exact() {
    let back_in_bounds = r#"
define i8 @back(ptr %"p x") {
  %"one x" = getelementptr inbounds i8, ptr %"p x", i64 1
  %"back x" = getelementptr inbounds i8, ptr %"one x", i64 -1
  %"value x" = load i8, ptr %"back x", align 1
  ret i8 %"value x"
}
"#;
    let mut back =
        reflect_bounded_memory_cfg_checked(back_in_bounds, &BoundedMemoryConfig::new("p x", 2))
            .unwrap();
    assert!(proved(&mut back.arena, back.result.defined));
    let asg = assignment(&back, &[], &[41, 42]);
    assert_eq!(eval_bv(&back, back.result.value, &asg), 41);

    let back_nuw = back_in_bounds.replace(
        "getelementptr inbounds i8, ptr %\"one x\", i64 -1",
        "getelementptr inbounds nuw i8, ptr %\"one x\", i64 -1",
    );
    let wrapped =
        reflect_bounded_memory_cfg_checked(&back_nuw, &BoundedMemoryConfig::new("p x", 2)).unwrap();
    assert!(!eval_bool(
        &wrapped,
        wrapped.result.defined,
        &assignment(&wrapped, &[], &[41, 42])
    ));

    let negative = r"
define i8 @negative(ptr %p) {
  %q = getelementptr inbounds i8, ptr %p, i64 -1
  %v = load i8, ptr %q, align 1
  ret i8 %v
}
";
    let negative =
        reflect_bounded_memory_cfg_checked(negative, &BoundedMemoryConfig::new("p", 2)).unwrap();
    assert!(!eval_bool(
        &negative,
        negative.result.defined,
        &assignment(&negative, &[], &[1, 2])
    ));

    let duplicate = r"
define i8 @duplicate(ptr %p) {
  %q = getelementptr inbounds i8, ptr %p, i64 0
  %q = getelementptr inbounds i8, ptr %p, i64 1
  ret i8 0
}
";
    assert_eq!(
        reflect_bounded_memory_cfg_checked(duplicate, &BoundedMemoryConfig::new("p", 2))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::DuplicateValue
    );

    let undefined = "define i8 @f(ptr %p) {\n%v = load i8, ptr %q, align 1\nret i8 %v\n}\n";
    assert_eq!(
        reflect_bounded_memory_cfg_checked(undefined, &BoundedMemoryConfig::new("p", 1))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::UndefinedValue
    );
}

#[test]
fn out_of_bounds_accesses_are_path_conditioned() {
    let ll = r"
define i8 @selected(ptr %p, i1 %c) {
entry:
  br i1 %c, label %bad, label %good
bad:
  %past = getelementptr inbounds i8, ptr %p, i64 1
  %bad_value = load i8, ptr %past, align 1
  ret i8 %bad_value
good:
  %good_value = load i8, ptr %p, align 1
  ret i8 %good_value
}
";
    let mut reflected =
        reflect_bounded_memory_cfg_checked(ll, &BoundedMemoryConfig::new("p", 1)).unwrap();
    let condition = reflected.arena.var(scalar_symbol(&reflected, "c"));
    let expected = reflected.arena.not(condition).unwrap();
    let exact = reflected
        .arena
        .eq(reflected.result.defined, expected)
        .unwrap();
    assert!(proved(&mut reflected.arena, exact));
    assert!(eval_bool(
        &reflected,
        reflected.result.defined,
        &assignment(&reflected, &[("c", 1, 0)], &[77])
    ));
    assert!(!eval_bool(
        &reflected,
        reflected.result.defined,
        &assignment(&reflected, &[("c", 1, 1)], &[77])
    ));
}

#[test]
fn branch_memory_joins_only_selected_writes() {
    let ll = r"
define i8 @branch_store(ptr noundef %0, i1 noundef %1) {
entry:
  br i1 %1, label %yes, label %no
yes:
  store i8 11, ptr %0, align 1
  ret i8 0
no:
  store i8 22, ptr %0, align 1
  ret i8 0
}
";
    let mut reflected = reflect_bounded_memory_cfg_checked(ll, &config(1)).unwrap();
    let condition = reflected.arena.var(scalar_symbol(&reflected, "1"));
    let eleven = reflected.arena.bv_const(8, 11).unwrap();
    let twenty_two = reflected.arena.bv_const(8, 22).unwrap();
    let expected = reflected.arena.ite(condition, eleven, twenty_two).unwrap();
    let same = reflected
        .arena
        .eq(reflected.region.output[0].value, expected)
        .unwrap();
    assert!(proved(&mut reflected.arena, same));
    assert!(proved(&mut reflected.arena, reflected.result.defined));
    assert!(proved(
        &mut reflected.arena,
        reflected.region.output[0].defined
    ));
}

#[test]
fn unsupported_memory_and_region_shapes_fail_closed() {
    let direct = "define i8 @f(ptr %p) {\n%v = load i8, ptr %p, align 1\nret i8 %v\n}\n";
    assert_eq!(
        reflect_bounded_memory_cfg_checked(direct, &BoundedMemoryConfig::new("p", 0))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::RegionSize
    );
    assert_eq!(
        reflect_bounded_memory_cfg_checked(direct, &BoundedMemoryConfig::new("p", 257))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::RegionSize
    );
    assert_eq!(
        reflect_bounded_memory_cfg_checked(direct, &BoundedMemoryConfig::new("missing", 1))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::PointerParameter
    );

    let two_ptrs = "define i8 @f(ptr %p, ptr %q) {\n%v = load i8, ptr %p, align 1\nret i8 %v\n}\n";
    assert_eq!(
        reflect_bounded_memory_cfg_checked(two_ptrs, &BoundedMemoryConfig::new("p", 1))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::PointerParameterCount
    );

    for ll in [
        "define i16 @f(ptr %p) {\n%v = load i16, ptr %p, align 1\nret i16 %v\n}\n",
        "define i8 @f(ptr %p) {\n%q = getelementptr i8, ptr %p, i64 0\n%v = load i8, ptr %q, align 1\nret i8 %v\n}\n",
        "define i8 @f(ptr %p, i32 %i) {\n%q = getelementptr inbounds i8, ptr %p, i32 %i\n%v = load i8, ptr %q, align 1\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%q = getelementptr inbounds i8, ptr %p, i64 0, i64 1\n%v = load i8, ptr %q, align 1\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%v = load i8, ptr %p, align 2\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%v = load volatile i8, ptr %p, align 1\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%v = load atomic i8, ptr %p seq_cst, align 1\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%v = load i8, ptr %p, align 1, !noundef !0\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%slot = alloca i8\nret i8 0\n}\n",
        "define i8 @f(ptr %p) {\n%v = load i8, ptr @global, align 1\nret i8 %v\n}\n",
        "define i8 @f(ptr %p) {\n%v = load i8, ptr null, align 1\nret i8 %v\n}\n",
        "define i64 @f(ptr %p) {\n%v = ptrtoint ptr %p to i64\nret i64 %v\n}\n",
        "define i8 @f(ptr %p) {\ncall void @llvm.lifetime.start.p0(i64 1, ptr %p)\nret i8 0\n}\n",
        "define i8 @f(ptr %p) {\n%v = call i8 @callee(ptr %p)\nret i8 %v\n}\n",
        "define i8 @f(ptr %p, i1 %c) {\n%q = select i1 %c, ptr %p, ptr %p\n%v = load i8, ptr %q, align 1\nret i8 %v\n}\n",
    ] {
        let error =
            reflect_bounded_memory_cfg_checked(ll, &BoundedMemoryConfig::new("p", 1)).unwrap_err();
        assert_eq!(error.kind(), ReflectErrorKind::Syntax, "{ll}");
        assert!(error.span().is_some());
    }

    let address_space =
        "define i8 @f(ptr addrspace(1) %p) {\n%v = load i8, ptr %p, align 1\nret i8 %v\n}\n";
    assert_eq!(
        reflect_bounded_memory_cfg_checked(address_space, &BoundedMemoryConfig::new("p", 1))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::PointerParameter
    );
}

#[test]
fn internal_memory_symbols_never_alias_source_parameters() {
    let ll = r"
define i8 @names(ptr %p, i8 %__axeyum_llvm_mem_0) {
  store i8 %__axeyum_llvm_mem_0, ptr %p, align 1
  %v = load i8, ptr %p, align 1
  ret i8 %v
}
";
    let mut reflected =
        reflect_bounded_memory_cfg_checked(ll, &BoundedMemoryConfig::new("p", 1)).unwrap();
    let source = scalar_symbol(&reflected, "__axeyum_llvm_mem_0");
    assert_ne!(source, reflected.region.input[0]);
    let source_term = reflected.arena.var(source);
    let same = reflected
        .arena
        .eq(reflected.result.value, source_term)
        .unwrap();
    assert!(proved(&mut reflected.arena, same));
}

#[test]
fn deterministic_memory_noise_never_panics() {
    const ALPHABET: &[u8] =
        b"definegetelementptrinboundsnuwloadstorealignptri8i64ret%@,={} !0123456789\n";
    let mut state = 0xa409_3822_299f_31d0_u64;
    for case in 0..512 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let len = usize::from(state.to_le_bytes()[0] & 127);
        let mut input = String::with_capacity(len);
        for _ in 0..len {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            input.push(ALPHABET[usize::from(state.to_le_bytes()[0]) % ALPHABET.len()] as char);
        }
        assert!(
            catch_unwind(|| reflect_bounded_memory_cfg_checked(&input, &config(4))).is_ok(),
            "case {case} panicked: {input:?}"
        );
    }

    let first = reflect_bounded_memory_cfg_checked(ROUNDTRIP, &config(4)).unwrap();
    let second = reflect_bounded_memory_cfg_checked(ROUNDTRIP, &config(4)).unwrap();
    assert_eq!(first.params, second.params);
    assert_eq!(first.region.input, second.region.input);
    assert_eq!(first.region.output, second.region.output);
    assert_eq!(first.result, second.result);
    assert_eq!(first.arena.len(), second.arena.len());
    assert_eq!(
        render(&first.arena, first.result.defined),
        render(&second.arena, second.result.defined)
    );
}
