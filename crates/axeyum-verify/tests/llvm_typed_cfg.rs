//! Typed LLVM control-flow syntax and structural validation (T5.1.2, ADR-0282).

use std::panic::{AssertUnwindSafe, catch_unwind};

use axeyum_verify::reflect::llvm::syntax::{
    BlockId, ParseErrorKind, TerminatorKind, parse_function, parse_scalar_cfg,
};

const CLANG_DIAMOND: &str = include_str!("fixtures/llvm/clang21_div_diamond.ll");
const RUSTC_DIAMOND: &str = include_str!("fixtures/llvm/rustc197_div_diamond.ll");
const NOISE_ALPHABET: &[u8] = b"brswitchphiretunreachablelabeli1i8%@[],:= !0123456789\n";

fn cfg(ll: &str) -> axeyum_verify::reflect::llvm::syntax::ScalarCfg {
    let function = parse_function(ll).unwrap();
    parse_scalar_cfg(&function).unwrap()
}

fn shape(ll: &str) -> Vec<&'static str> {
    cfg(ll)
        .blocks
        .iter()
        .map(|block| match block.terminator.kind {
            TerminatorKind::Branch { .. } => "br",
            TerminatorKind::CondBranch { .. } => "cond-br",
            TerminatorKind::Switch { .. } => "switch",
            TerminatorKind::Return { .. } => "ret",
            TerminatorKind::Unreachable => "unreachable",
        })
        .collect()
}

#[test]
fn unmodified_clang_and_rustc_diamonds_converge_to_one_cfg_shape() {
    for ll in [CLANG_DIAMOND, RUSTC_DIAMOND] {
        let graph = cfg(ll);
        assert_eq!(graph.return_width, 32);
        assert_eq!(shape(ll), ["cond-br", "br", "br", "ret"]);
        assert_eq!(
            graph
                .blocks
                .iter()
                .map(|block| block.phis.len())
                .sum::<usize>(),
            1
        );
        assert_eq!(graph.blocks[0].successors.len(), 2);
        assert_eq!(graph.blocks[3].predecessors.len(), 2);
    }
}

#[test]
fn every_control_form_role_label_spelling_and_metadata_is_typed() {
    let ll = r#"
define i8 @roles(i8 %x, i1 %c) {
entry:
  br i1 %c, label %"switch block", label %join, !prof !0
"switch block":
  switch i8 %x, label %join [ i8 -1, label %7
    i8 1, label %join
    i8 2, label %dead ], !prof !1
7:
  br label %join
dead:
  unreachable
join:
  %r = phi i8 [ 0, %entry ], [ 1, %"switch block" ], [ 2, %7 ]
  ret i8 %r
}
"#;
    let graph = cfg(ll);
    assert_eq!(graph.entry, BlockId::Label("entry".to_owned()));
    assert_eq!(shape(ll), ["cond-br", "switch", "br", "unreachable", "ret"]);

    let TerminatorKind::CondBranch {
        true_target,
        false_target,
        ..
    } = &graph.blocks[0].terminator.kind
    else {
        panic!("expected conditional branch")
    };
    assert_eq!(true_target, &BlockId::Label("switch block".to_owned()));
    assert_eq!(false_target, &BlockId::Label("join".to_owned()));
    assert_eq!(graph.blocks[0].terminator.metadata, ["!prof !0"]);

    let TerminatorKind::Switch {
        default_target,
        cases,
        ..
    } = &graph.blocks[1].terminator.kind
    else {
        panic!("expected switch")
    };
    assert_eq!(default_target, &BlockId::Label("join".to_owned()));
    assert_eq!(cases[0].value, 255);
    assert_eq!(cases[0].target, BlockId::Label("7".to_owned()));
    assert_eq!(cases[1].target, BlockId::Label("join".to_owned()));
    assert_eq!(graph.blocks[1].terminator.metadata, ["!prof !1"]);
    assert_eq!(
        graph.blocks[4].predecessors,
        [
            BlockId::Label("entry".to_owned()),
            BlockId::Label("switch block".to_owned()),
            BlockId::Label("7".to_owned()),
        ]
    );
}

#[test]
fn single_line_switch_and_repeated_destinations_are_valid() {
    let ll = r"
define i8 @same(i8 %x) {
entry:
  switch i8 %x, label %join [ i8 0, label %join i8 1, label %join ]
join:
  %r = phi i8 [ %x, %entry ]
  ret i8 %r
}
";
    let graph = cfg(ll);
    assert_eq!(
        graph.blocks[0].successors,
        [BlockId::Label("join".to_owned())]
    );
    assert_eq!(
        graph.blocks[1].predecessors,
        [BlockId::Label("entry".to_owned())]
    );
}

fn cfg_error(ll: &str) -> ParseErrorKind {
    let function = parse_function(ll).unwrap();
    parse_scalar_cfg(&function).unwrap_err().kind()
}

#[test]
fn malformed_graphs_fail_closed_with_stable_located_errors() {
    let cases = [
        (
            "define i8 @f(i8 %x) {\nentry:\nbr label %missing\n}\n",
            ParseErrorKind::UndefinedBlockLabel,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr label %entry\n}\n",
            ParseErrorKind::MalformedControlFlow,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nswitch i8 %x, label %done [ i8 -1, label %done i8 255, label %done ]\ndone:\nret i8 %x\n}\n",
            ParseErrorKind::MalformedControlFlow,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nswitch i8 %x, label %done [ i16 1, label %done ]\ndone:\nret i8 %x\n}\n",
            ParseErrorKind::MalformedControlFlow,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr label %join\njoin:\n%x2 = add i8 %x, 1\n%r = phi i8 [ %x, %entry ]\nret i8 %r\n}\n",
            ParseErrorKind::InvalidPhi,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr label %join\njoin:\n%r = phi i8 [ %x, %entry ], [ 0, %entry ]\nret i8 %r\n}\n",
            ParseErrorKind::InvalidPhi,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr label %join\nother:\nbr label %join\njoin:\n%r = phi i8 [ %x, %entry ]\nret i8 %r\n}\n",
            ParseErrorKind::InvalidPhi,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr i8 %x, label %yes, label %no\nyes:\nret i8 1\nno:\nret i8 0\n}\n",
            ParseErrorKind::MalformedControlFlow,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr label %done\n%x2 = add i8 %x, 1\ndone:\nret i8 %x\n}\n",
            ParseErrorKind::MalformedControlFlow,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\n%x2 = add i8 %x, 1\n}\n",
            ParseErrorKind::MalformedControlFlow,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nbr i1 poison, label %yes, label %no\nyes:\nret i8 1\nno:\nret i8 0\n}\n",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nswitch i8 undef, label %done [ ]\ndone:\nret i8 %x\n}\n",
            ParseErrorKind::UnsupportedSemantics,
        ),
        (
            "define i8 @f(i8 %x) {\nentry:\nindirectbr ptr %x, [ label %entry ]\n}\n",
            ParseErrorKind::UnsupportedInstruction,
        ),
    ];
    for (ll, expected) in cases {
        let function = parse_function(ll).unwrap();
        let error = parse_scalar_cfg(&function).unwrap_err();
        assert_eq!(error.kind(), expected, "{ll}");
        assert!(error.span().line >= 2);
        assert!(error.span().start < error.span().end);
    }
}

#[test]
fn multiline_switch_errors_retain_the_offending_source_line() {
    let ll = "define i8 @f(i8 %x) {\nentry:\n  switch i8 %x, label %done [\n    i16 1, label %done\n  ]\ndone:\n  ret i8 %x\n}\n";
    let error = parse_scalar_cfg(&parse_function(ll).unwrap()).unwrap_err();
    assert_eq!(error.kind(), ParseErrorKind::MalformedControlFlow);
    assert_eq!(error.span().line, 4);
    assert_eq!(error.span().column, 5);
}

#[test]
fn deterministic_graph_noise_never_panics() {
    let mut state = 0x9e37_79b9_u32;
    for case in 0..4_096 {
        let mut body = String::new();
        let len = 8 + case % 96;
        for _ in 0..len {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            body.push(NOISE_ALPHABET[(state as usize) % NOISE_ALPHABET.len()] as char);
        }
        let ll = format!("define i8 @f(i8 %x) {{\nentry:\n{body}\n}}\n");
        let parsed = catch_unwind(AssertUnwindSafe(|| {
            parse_function(&ll).and_then(|function| parse_scalar_cfg(&function))
        }));
        assert!(parsed.is_ok(), "case {case} panicked");
        if let Ok(first) = &parsed.unwrap() {
            let second = parse_scalar_cfg(&parse_function(&ll).unwrap()).unwrap();
            assert_eq!(first, &second);
            assert_eq!(format!("{first:?}"), format!("{second:?}"));
        }
    }
}

#[test]
fn error_helper_covers_the_expected_kind() {
    assert_eq!(
        cfg_error("define i8 @f(i8 %x) {\nentry:\nresume i8 %x\n}\n"),
        ParseErrorKind::UnsupportedInstruction
    );
}
