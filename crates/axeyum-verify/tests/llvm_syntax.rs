//! Structured textual LLVM parser gates (P5.1/T5.1.2, ADR-0280).

use axeyum_verify::reflect::llvm::{
    param_decls,
    syntax::{ParseErrorKind, parse_function},
};

const COMPILER_SHAPED: &str = r#"; ModuleID = 'parser-gate'
target triple = "x86_64-unknown-linux-gnu"

declare void @side_effect(i32)

define noundef i32 @"quoted fn"(i32 noundef %x, i8 range(i8 0, 4) %"mode value") #0 {
entry:
  %cmp = icmp eq i8 %"mode value", 0 ; an instruction comment
  br i1 %cmp, label %"then block", label %else

"then block":
  ret i32 %x

else:
  %next = add i32 %x, 1
  ret i32 %next
}

attributes #0 = { nounwind }
"#;

#[test]
fn parses_compiler_shaped_function_with_spans_and_nested_parameter_attributes() {
    let parsed = parse_function(COMPILER_SHAPED).expect("compiler-shaped function must parse");

    assert_eq!(parsed.name, "quoted fn");
    assert_eq!(
        parsed
            .params
            .iter()
            .map(|p| (p.ty.as_str(), p.name.as_str()))
            .collect::<Vec<_>>(),
        vec![("i32", "x"), ("i8", "mode value")]
    );
    assert_eq!(
        parsed
            .blocks
            .iter()
            .map(|b| b.label.as_deref())
            .collect::<Vec<_>>(),
        vec![Some("entry"), Some("then block"), Some("else")]
    );
    assert_eq!(
        parsed.blocks[0]
            .instructions
            .iter()
            .map(|i| i.text.as_str())
            .collect::<Vec<_>>(),
        vec![
            "%cmp = icmp eq i8 %\"mode value\", 0",
            "br i1 %cmp, label %\"then block\", label %else",
        ]
    );

    for span in std::iter::once(&parsed.span)
        .chain(parsed.params.iter().map(|p| &p.span))
        .chain(parsed.blocks.iter().map(|b| &b.span))
        .chain(
            parsed
                .blocks
                .iter()
                .flat_map(|b| b.instructions.iter().map(|i| &i.span)),
        )
    {
        assert!(span.start < span.end, "nonempty span: {span:?}");
        assert!(span.end <= COMPILER_SHAPED.len(), "in-range span: {span:?}");
        assert!(span.line >= 1 && span.column >= 1, "located span: {span:?}");
    }

    assert_eq!(parsed, parse_function(COMPILER_SHAPED).unwrap());
    assert_eq!(
        param_decls(COMPILER_SHAPED),
        vec![("x".to_owned(), 32), ("mode value".to_owned(), 8)]
    );
}

#[test]
fn preserves_an_unlabeled_entry_block_without_inventing_a_source_label() {
    let parsed = parse_function("define i8 @id(i8 %x) {\n  ret i8 %x\n}\n").unwrap();
    assert_eq!(parsed.name, "id");
    assert_eq!(parsed.blocks.len(), 1);
    assert_eq!(parsed.blocks[0].label, None);
    assert_eq!(parsed.blocks[0].instructions[0].text, "ret i8 %x");

    let aggregate =
        parse_function("define { i8, i8 } @pair(i8 %x) {\n  ret { i8, i8 } zeroinitializer\n}\n")
            .unwrap();
    assert_eq!(aggregate.name, "pair");
}

#[test]
fn malformed_inputs_return_typed_located_errors() {
    let cases = [
        (
            "target triple = \"x86_64\"\n",
            ParseErrorKind::MissingDefinition,
        ),
        (
            "define i8 no_global(i8 %x) {\nret i8 %x\n}\n",
            ParseErrorKind::MalformedHeader,
        ),
        (
            "define i8 no_global(i8 %x) {\ncall void @side()\nret i8 %x\n}\n",
            ParseErrorKind::MalformedHeader,
        ),
        (
            "define i8 @f(i8) {\nret i8 0\n}\n",
            ParseErrorKind::MalformedParameter,
        ),
        (
            "define i8 @\"f(i8 %x) {\nret i8 %x\n}\n",
            ParseErrorKind::UnterminatedQuotedToken,
        ),
        (
            "define i8 @f(i8 %x {\nret i8 %x\n}\n",
            ParseErrorKind::UnbalancedDelimiter,
        ),
        (
            "define i8 @f(i8 %x) {\nret i8 %x\n",
            ParseErrorKind::UnclosedBody,
        ),
    ];

    for (input, expected) in cases {
        let error = parse_function(input).expect_err(input);
        assert_eq!(error.kind(), expected, "{input}");
        assert!(error.span().start < error.span().end, "{error:?}");
        assert!(error.span().end <= input.len(), "{error:?}");
        assert!(error.span().line >= 1 && error.span().column >= 1);
        assert!(!error.to_string().is_empty());
    }
}

#[test]
fn duplicate_labels_and_multiple_definitions_fail_closed() {
    let duplicate = "define i1 @f(i1 %x) {\nentry:\n  br label %entry\nentry:\n  ret i1 %x\n}\n";
    assert_eq!(
        parse_function(duplicate).unwrap_err().kind(),
        ParseErrorKind::DuplicateBlockLabel
    );

    let multiple = "define i1 @f(i1 %x) {\nret i1 %x\n}\ndefine i1 @g(i1 %x) {\nret i1 %x\n}\n";
    assert_eq!(
        parse_function(multiple).unwrap_err().kind(),
        ParseErrorKind::MultipleDefinitions
    );
}

#[test]
fn parser_never_panics_on_deterministic_ascii_noise() {
    const ALPHABET: &[u8] = b"define@%(){}[]<>,:=;\n\t abcdefghijklmnopqrstuvwxyz0123456789\"\\";
    let mut state = 0x6a09_e667_f3bc_c909_u64;
    for case in 0..4_096 {
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
        let result = std::panic::catch_unwind(|| parse_function(&input));
        assert!(result.is_ok(), "case {case} panicked: {input:?}");
    }
}
