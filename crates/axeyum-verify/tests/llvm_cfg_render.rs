//! Canonical typed LLVM CFG rendering gates (T5.1.2, ADR-0284).

use std::io::Write as _;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::{Command, Stdio};

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::reflect_cfg_into_checked;
use axeyum_verify::reflect::llvm::syntax::{
    ParseErrorKind, ScalarCfg, SourceSpan, parse_function, parse_scalar_cfg, render_scalar_cfg,
};

const CLANG_DIAMOND: &str = include_str!("fixtures/llvm/clang21_div_diamond.ll");
const RUSTC_DIAMOND: &str = include_str!("fixtures/llvm/rustc197_div_diamond.ll");

const OMNIBUS: &str = r#"
define i8 @"fn\22\5C \C3\A9"(i8 %"x\22\5C", i1 %c) {
"entry \22":
  %add = add nuw nsw i8 %"x\22\5C", -1
  %sub = sub nuw nsw i8 %add, 1
  %mul = mul nuw nsw i8 %sub, 3
  %and = and i8 %mul, 127
  %or = or disjoint i8 %and, 128
  %xor = xor i8 %or, -1
  %shl = shl nuw nsw i8 %xor, 1
  %lshr = lshr exact i8 %shl, 1
  %ashr = ashr exact i8 %lshr, 1
  %udiv = udiv exact i8 %ashr, 3
  %sdiv = sdiv exact i8 %udiv, 3
  %urem = urem i8 %sdiv, 3
  %srem = srem i8 %urem, 3
  %eq = icmp eq i8 %srem, 0
  %ne = icmp ne i8 %srem, 0
  %ult = icmp ult i8 %srem, 1
  %ule = icmp ule i8 %srem, 1
  %ugt = icmp ugt i8 %srem, 1
  %uge = icmp uge i8 %srem, 1
  %slt = icmp slt i8 %srem, 1
  %sle = icmp sle i8 %srem, 1
  %sgt = icmp sgt i8 %srem, 1
  %sge = icmp sge i8 %srem, 1
  %sel = select i1 %eq, i8 %srem, i8 7
  %z = zext nneg i8 %sel to i16
  %s = sext i8 %sel to i16
  %t = trunc nuw nsw i16 %z to i8
  %min = call i8 @llvm.umin.i8(i8 %t, i8 %sel)
  %max = tail call i8 @llvm.umax.i8(i8 %min, i8 %sel)
  br i1 %c, label %"switch \5C", label %join, !prof !0
"switch \5C":
  switch i8 %max, label %join [
    i8 -1, label %case
    i8 1, label %join
    i8 2, label %dead
  ], !prof !1
case:
  br label %join
dead:
  unreachable
join:
  %r = phi i8 [ %sel, %"entry \22" ], [ %max, %"switch \5C" ], [ 9, %case ]
  ret i8 %r
}
"#;

fn cfg(ll: &str) -> ScalarCfg {
    parse_scalar_cfg(&parse_function(ll).unwrap()).unwrap()
}

fn without_spans(mut cfg: ScalarCfg) -> ScalarCfg {
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

fn proved(arena: &mut TermArena, goal: axeyum_ir::TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).unwrap(),
        ProofOutcome::Proved(_)
    )
}

#[test]
fn every_typed_scalar_form_round_trips_canonically() {
    let original = cfg(OMNIBUS);
    let rendered = render_scalar_cfg(&original);
    let reparsed = cfg(&rendered);

    assert_eq!(without_spans(original), without_spans(reparsed.clone()));
    assert_eq!(rendered, render_scalar_cfg(&reparsed));
    assert!(rendered.ends_with('\n'));
    assert!(!rendered.ends_with("\n\n"));
    assert!(rendered.contains("@\"fn\\22\\5C \\C3\\A9\""));
    assert!(rendered.contains("i8 255, label %\"case\""));
    assert!(rendered.contains(", !prof !0"));
}

#[test]
fn llvm_identifier_byte_escapes_are_exact_and_fail_closed() {
    let parsed = parse_function(
        "define i8 @\"q\\22b\\5C c\\00\\C3\\A9\"(i8 %\"x\\0A\") {\nret i8 %\"x\\0A\"\n}\n",
    )
    .unwrap();
    assert_eq!(parsed.name, "q\"b\\ c\0é");
    assert_eq!(parsed.params[0].name, "x\n");
    let rendered = render_scalar_cfg(&parse_scalar_cfg(&parsed).unwrap());
    assert!(rendered.contains("@\"q\\22b\\5C c\\00\\C3\\A9\""));
    assert!(rendered.contains("%\"x\\0A\""));
    assert_eq!(rendered, render_scalar_cfg(&cfg(&rendered)));

    for (ll, offending) in [
        ("define i8 @\"bad\\2\"() { ret i8 0 }", "\\2"),
        ("define i8 @\"bad\\GG\"() { ret i8 0 }", "\\GG"),
        ("define i8 @\"bad\\FF\"() { ret i8 0 }", "\\FF"),
        ("define i8 @\"bad\\\"() { ret i8 0 }", "\\\""),
    ] {
        let error = parse_function(ll).unwrap_err();
        assert_eq!(error.kind(), ParseErrorKind::MalformedIdentifierEscape);
        assert_eq!(error.span().line, 1);
        assert_eq!(error.span().start, ll.find(offending).unwrap());
    }
}

#[test]
fn compiler_diamonds_are_idempotent_and_accepted_by_llvm_as() {
    for ll in [CLANG_DIAMOND, RUSTC_DIAMOND] {
        let original = cfg(ll);
        let rendered = render_scalar_cfg(&original);
        let reparsed = cfg(&rendered);
        assert_eq!(without_spans(original), without_spans(reparsed.clone()));
        assert_eq!(rendered, render_scalar_cfg(&reparsed));

        let Ok(mut child) = Command::new("llvm-as")
            .args(["-o", "/dev/null", "-"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            eprintln!("skipping external llvm-as gate: tool is not installed");
            continue;
        };
        child
            .stdin
            .take()
            .unwrap()
            .write_all(rendered.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "llvm-as rejected canonical CFG: {}\n{rendered}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn canonical_cfg_preserves_checked_value_and_definedness() {
    for ll in [CLANG_DIAMOND, RUSTC_DIAMOND] {
        let canonical = render_scalar_cfg(&cfg(ll));
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 32).unwrap();
        let y = arena.bv_var("y", 32).unwrap();
        let c = arena.bool_var("c").unwrap();
        let original = reflect_cfg_into_checked(&mut arena, &[x, y, c], ll).unwrap();
        let rendered = reflect_cfg_into_checked(&mut arena, &[x, y, c], &canonical).unwrap();
        let values = arena.eq(original.value, rendered.value).unwrap();
        let defined = arena.eq(original.defined, rendered.defined).unwrap();
        let both = arena.and(values, defined).unwrap();
        assert!(proved(&mut arena, both));
    }

    let unreachable = r"
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
    let canonical = render_scalar_cfg(&cfg(unreachable));
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let original = reflect_cfg_into_checked(&mut arena, &[x], unreachable).unwrap();
    let rendered = reflect_cfg_into_checked(&mut arena, &[x], &canonical).unwrap();
    let defined = arena.eq(original.defined, rendered.defined).unwrap();
    assert!(proved(&mut arena, defined));
    let three = arena.bv_const(8, 3).unwrap();
    let in_range = arena.bv_ult(x, three).unwrap();
    let values = arena.eq(original.value, rendered.value).unwrap();
    let not_range = arena.not(in_range).unwrap();
    let under_range = arena.or(not_range, values).unwrap();
    assert!(proved(&mut arena, under_range));
}

#[test]
fn structured_name_and_graph_noise_never_panics_or_renders_nondeterministically() {
    const ALPHABET: &[u8] = b"abcXYZ012_%@\\\"0123456789ABCDEF";
    let mut state = 0xd1b5_4a32_d192_ed03_u64;
    for case in 0..1_024 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let len = usize::from(state.to_le_bytes()[0] & 31);
        let mut name = String::with_capacity(len);
        for _ in 0..len {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            name.push(ALPHABET[usize::from(state.to_le_bytes()[0]) % ALPHABET.len()] as char);
        }
        let ll = format!("define i8 @\"{name}\"(i8 %x) {{\nret i8 %x\n}}\n");
        let parsed = catch_unwind(AssertUnwindSafe(|| {
            parse_function(&ll).and_then(|function| parse_scalar_cfg(&function))
        }));
        assert!(parsed.is_ok(), "case {case} panicked: {ll:?}");
        if let Ok(graph) = parsed.unwrap() {
            let first = render_scalar_cfg(&graph);
            let second = render_scalar_cfg(&graph);
            assert_eq!(first, second);
            assert_eq!(first, render_scalar_cfg(&cfg(&first)));
        }
    }
}

#[test]
fn canonical_bool_return_keeps_bool_sort() {
    let canonical = render_scalar_cfg(&cfg("define i1 @f(i1 %x) {\nret i1 %x\n}\n"));
    let reflected = axeyum_verify::reflect::llvm::checked::reflect_cfg_checked(&canonical).unwrap();
    assert_eq!(reflected.arena.sort_of(reflected.result.value), Sort::Bool);
}
