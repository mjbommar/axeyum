//! Checked acyclic LLVM CFG execution gates (T5.1.2, ADR-0283).

use std::fmt::Write as _;
use std::panic::catch_unwind;

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval, render};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::{
    CheckedCfgReflected, ReflectErrorKind, reflect_cfg_checked, reflect_cfg_into_checked,
    reflect_scalar_into_checked,
};

const CLANG_DIAMOND: &str = include_str!("fixtures/llvm/clang21_div_diamond.ll");
const RUSTC_DIAMOND: &str = include_str!("fixtures/llvm/rustc197_div_diamond.ll");

fn proved(arena: &mut TermArena, goal: axeyum_ir::TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).unwrap(),
        ProofOutcome::Proved(_)
    )
}

fn bool_equivalent(
    arena: &mut TermArena,
    lhs: axeyum_ir::TermId,
    rhs: axeyum_ir::TermId,
) -> axeyum_ir::TermId {
    arena.eq(lhs, rhs).unwrap()
}

fn implies(
    arena: &mut TermArena,
    premise: axeyum_ir::TermId,
    conclusion: axeyum_ir::TermId,
) -> axeyum_ir::TermId {
    let not_premise = arena.not(premise).unwrap();
    arena.or(not_premise, conclusion).unwrap()
}

fn assignment(reflected: &CheckedCfgReflected, values: &[(&str, u32, u128)]) -> Assignment {
    let mut result = Assignment::new();
    for (name, width, value) in values {
        let symbol = reflected
            .params
            .iter()
            .find(|(param, _, _)| param == name)
            .unwrap()
            .1;
        result.set(
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
    result
}

fn eval_defined(reflected: &CheckedCfgReflected, values: &[(&str, u32, u128)]) -> bool {
    eval(
        &reflected.arena,
        reflected.result.defined,
        &assignment(reflected, values),
    )
    .unwrap()
        == Value::Bool(true)
}

fn eval_value(reflected: &CheckedCfgReflected, values: &[(&str, u32, u128)]) -> u128 {
    match eval(
        &reflected.arena,
        reflected.result.value,
        &assignment(reflected, values),
    )
    .unwrap()
    {
        Value::Bv { value, .. } => value,
        other => panic!("expected BV value, got {other:?}"),
    }
}

#[test]
fn compiler_division_diamonds_have_exact_selected_divisor_definedness() {
    for ll in [CLANG_DIAMOND, RUSTC_DIAMOND] {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 32).unwrap();
        let y = arena.bv_var("y", 32).unwrap();
        let c = arena.bool_var("c").unwrap();
        let reflected = reflect_cfg_into_checked(&mut arena, &[x, y, c], ll).unwrap();

        let zero = arena.bv_const(32, 0).unwrap();
        let y_zero = arena.eq(y, zero).unwrap();
        let y_nonzero = arena.not(y_zero).unwrap();
        let x_zero = arena.eq(x, zero).unwrap();
        let x_nonzero = arena.not(x_zero).unwrap();
        let expected_defined = arena.ite(c, y_nonzero, x_nonzero).unwrap();
        let defined_same = bool_equivalent(&mut arena, reflected.defined, expected_defined);
        assert!(proved(&mut arena, defined_same));

        let xy = arena.bv_udiv(x, y).unwrap();
        let yx = arena.bv_udiv(y, x).unwrap();
        let expected_value = arena.ite(c, xy, yx).unwrap();
        let value_same = arena.eq(reflected.value, expected_value).unwrap();
        let value_where_defined = implies(&mut arena, reflected.defined, value_same);
        assert!(proved(&mut arena, value_where_defined));
    }

    let reflected = reflect_cfg_checked(CLANG_DIAMOND).unwrap();
    assert!(eval_defined(
        &reflected,
        &[("0", 32, 12), ("1", 32, 3), ("2", 1, 1)]
    ));
    assert_eq!(
        eval_value(&reflected, &[("0", 32, 12), ("1", 32, 3), ("2", 1, 1)]),
        4
    );
    assert!(!eval_defined(
        &reflected,
        &[("0", 32, 12), ("1", 32, 0), ("2", 1, 1)]
    ));
    assert!(!eval_defined(
        &reflected,
        &[("0", 32, 0), ("1", 32, 12), ("2", 1, 0)]
    ));
}

#[test]
fn negative_integer_constants_are_normalized_to_their_declared_width() {
    let ll = "define i32 @not(i32 %x) {\n%r = xor i32 %x, -1\nret i32 %r\n}\n";
    let reflected = reflect_cfg_checked(ll).unwrap();
    assert!(eval_defined(&reflected, &[("x", 32, 0x1234_5678)]));
    assert_eq!(
        eval_value(&reflected, &[("x", 32, 0x1234_5678)]),
        0xedcb_a987
    );
}

#[test]
fn branch_phi_and_select_agree_with_selected_arm_poison() {
    let cfg = r"
define i8 @cfg(i8 %a, i8 %b, i1 %c) {
entry:
  br i1 %c, label %taken, label %other
taken:
  %p = add nsw i8 %a, %b
  br label %join
other:
  br label %join
join:
  %r = phi i8 [ %p, %taken ], [ 0, %other ]
  ret i8 %r
}
";
    let select = r"
define i8 @select(i8 %a, i8 %b, i1 %c) {
entry:
  %p = add nsw i8 %a, %b
  %r = select i1 %c, i8 %p, i8 0
  ret i8 %r
}
";
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let c = arena.bool_var("c").unwrap();
    let branched = reflect_cfg_into_checked(&mut arena, &[a, b, c], cfg).unwrap();
    let selected = reflect_scalar_into_checked(&mut arena, &[a, b, c], select).unwrap();
    let values = arena.eq(branched.value, selected.value).unwrap();
    let defined = arena.eq(branched.defined, selected.defined).unwrap();
    let both = arena.and(values, defined).unwrap();
    assert!(proved(&mut arena, both));

    let reflected = reflect_cfg_checked(cfg).unwrap();
    assert!(eval_defined(
        &reflected,
        &[("a", 8, 127), ("b", 8, 1), ("c", 1, 0)]
    ));
    assert!(!eval_defined(
        &reflected,
        &[("a", 8, 127), ("b", 8, 1), ("c", 1, 1)]
    ));
}

#[test]
fn immediate_ub_is_path_conditioned() {
    let ll = r"
define i8 @f(i8 %a, i8 %b, i1 %c) {
entry:
  br i1 %c, label %risky, label %safe
risky:
  %q = udiv i8 %a, %b
  ret i8 %q
safe:
  ret i8 7
}
";
    let reflected = reflect_cfg_checked(ll).unwrap();
    assert!(eval_defined(
        &reflected,
        &[("a", 8, 9), ("b", 8, 0), ("c", 1, 0)]
    ));
    assert!(!eval_defined(
        &reflected,
        &[("a", 8, 9), ("b", 8, 0), ("c", 1, 1)]
    ));
}

#[test]
fn unused_poison_is_not_promoted_to_immediate_ub() {
    let cases = [
        (
            "define i8 @f(i8 %a) {\n%p = add nsw i8 %a, 1\nret i8 7\n}\n",
            true,
        ),
        (
            "define i8 @f(i8 %a) {\n%q = udiv exact i8 5, 2\nret i8 7\n}\n",
            true,
        ),
        (
            "define i8 @f(i8 %a) {\n%p = add nsw i8 %a, 1\n%q = udiv i8 %p, 2\nret i8 7\n}\n",
            true,
        ),
        (
            "define i8 @f(i8 %a) {\n%q = udiv i8 %a, 0\nret i8 7\n}\n",
            false,
        ),
        (
            "define i8 @f(i8 %a) {\n%p = add nsw i8 %a, 1\n%q = udiv i8 4, %p\nret i8 7\n}\n",
            false,
        ),
    ];
    for (ll, expected) in cases {
        let reflected = reflect_cfg_checked(ll).unwrap();
        assert_eq!(eval_defined(&reflected, &[("a", 8, 127)]), expected, "{ll}");
    }
}

#[test]
fn unreachable_default_is_false_definedness_not_a_fabricated_value() {
    let ll = r"
define i8 @lut3(i8 %x) {
entry:
  switch i8 %x, label %dead [ i8 0, label %r5 i8 1, label %r7 i8 2, label %r9 ]
dead:
  unreachable
r5:
  ret i8 5
r7:
  ret i8 7
r9:
  ret i8 9
}
";
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let reflected = reflect_cfg_into_checked(&mut arena, &[x], ll).unwrap();
    let three = arena.bv_const(8, 3).unwrap();
    let in_range = arena.bv_ult(x, three).unwrap();
    let defined_same = arena.eq(reflected.defined, in_range).unwrap();
    assert!(proved(&mut arena, defined_same));

    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let x0 = arena.eq(x, zero).unwrap();
    let x1 = arena.eq(x, one).unwrap();
    let tail = arena.ite(x1, seven, nine).unwrap();
    let expected = arena.ite(x0, five, tail).unwrap();
    let value_same = arena.eq(reflected.value, expected).unwrap();
    let under_range = implies(&mut arena, in_range, value_same);
    assert!(proved(&mut arena, under_range));
    assert!(matches!(
        prove(&mut arena, &[], reflected.defined, &SolverConfig::default()).unwrap(),
        ProofOutcome::Disproved(_)
    ));
}

#[test]
fn poison_control_is_ub_even_when_destinations_repeat() {
    let branch = r"
define i8 @f(i8 %a) {
entry:
  %p = add nsw i8 %a, 1
  %c = icmp eq i8 %p, 0
  br i1 %c, label %join, label %join
join:
  %r = phi i8 [ 7, %entry ]
  ret i8 %r
}
";
    let switch = r"
define i8 @f(i8 %a) {
entry:
  %p = add nsw i8 %a, 1
  switch i8 %p, label %join [ i8 0, label %join ]
join:
  %r = phi i8 [ 7, %entry ]
  ret i8 %r
}
";
    for ll in [branch, switch] {
        let reflected = reflect_cfg_checked(ll).unwrap();
        assert!(!eval_defined(&reflected, &[("a", 8, 127)]));
        assert!(eval_defined(&reflected, &[("a", 8, 1)]));
    }
}

#[test]
fn malformed_ssa_cycles_and_execution_growth_fail_closed() {
    let return_mismatch = "define i8 @f(i8 %x) {\nentry:\n  ret i16 0\n}\n";
    assert_eq!(
        reflect_cfg_checked(return_mismatch).unwrap_err().kind(),
        ReflectErrorKind::Syntax
    );

    let duplicate = r"
define i8 @f(i8 %x, i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  %v = add i8 %x, 1
  ret i8 %v
b:
  %v = sub i8 %x, 1
  ret i8 %v
}
";
    assert_eq!(
        reflect_cfg_checked(duplicate).unwrap_err().kind(),
        ReflectErrorKind::DuplicateValue
    );

    let non_dominating = r"
define i8 @f(i8 %x, i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  %v = add i8 %x, 1
  br label %join
b:
  br label %join
join:
  ret i8 %v
}
";
    assert_eq!(
        reflect_cfg_checked(non_dominating).unwrap_err().kind(),
        ReflectErrorKind::UndefinedValue
    );

    let cycle = r"
define i8 @f(i8 %x) {
entry:
  br label %loop
loop:
  br label %loop
}
";
    assert_eq!(
        reflect_cfg_checked(cycle).unwrap_err().kind(),
        ReflectErrorKind::CyclicControlFlow
    );

    let mut expansive = String::from("define i8 @f(i1 %c) {\ns0:\n");
    for stage in 0..12 {
        write!(
            &mut expansive,
            "  br i1 %c, label %t{stage}, label %f{stage}\nt{stage}:\n  br label %s{}\nf{stage}:\n  br label %s{}\ns{}:\n",
            stage + 1,
            stage + 1,
            stage + 1
        )
        .unwrap();
    }
    expansive.push_str("  ret i8 0\n}\n");
    assert_eq!(
        reflect_cfg_checked(&expansive).unwrap_err().kind(),
        ReflectErrorKind::ExecutionLimit
    );
}

#[test]
fn straight_line_checked_apis_are_equivalent() {
    let ll = "define i8 @f(i8 %a, i8 %b) {\n%x = xor i8 %a, %b\nret i8 %x\n}\n";
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let scalar = reflect_scalar_into_checked(&mut arena, &[a, b], ll).unwrap();
    let cfg = reflect_cfg_into_checked(&mut arena, &[a, b], ll).unwrap();
    let values = arena.eq(scalar.value, cfg.value).unwrap();
    let defined = arena.eq(scalar.defined, cfg.defined).unwrap();
    let both = arena.and(values, defined).unwrap();
    assert!(proved(&mut arena, both));
}

#[test]
fn deterministic_graph_noise_never_panics_checked_execution() {
    const ALPHABET: &[u8] = b"definebrswitchphiretunreachablelabeli1i8%@[],:={} !0123456789\n";
    let mut state = 0x3c6e_f372_fe94_f82b_u64;
    for case in 0..1_024 {
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
            catch_unwind(|| reflect_cfg_checked(&input)).is_ok(),
            "case {case} panicked: {input:?}"
        );
    }

    let first = reflect_cfg_checked(CLANG_DIAMOND).unwrap();
    let second = reflect_cfg_checked(CLANG_DIAMOND).unwrap();
    assert_eq!(first.params, second.params);
    assert_eq!(first.arena.len(), second.arena.len());
    assert_eq!(first.result, second.result);
    assert_eq!(
        render(&first.arena, first.result.value),
        render(&second.arena, second.result.value)
    );
    assert_eq!(
        render(&first.arena, first.result.defined),
        render(&second.arena, second.result.defined)
    );
}

#[test]
fn bool_return_cfg_is_supported() {
    let ll = "define i1 @f(i1 %x) {\nret i1 %x\n}\n";
    let reflected = reflect_cfg_checked(ll).unwrap();
    assert_eq!(reflected.arena.sort_of(reflected.result.value), Sort::Bool);
}
