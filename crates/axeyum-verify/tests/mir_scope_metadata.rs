//! Exact rustc MIR lexical-scope metadata gates (ADR-0319).

use std::fmt::Write as _;
use std::panic::catch_unwind;

use axeyum_ir::{Sort, TermArena, render};
use axeyum_verify::reflect::mir::checked::{MirScalarConfig, reflect_scalar_into_checked};
use axeyum_verify::reflect::mir::syntax::{MirType, ParseErrorKind, parse_function};

const SCOPED: &str = r"
fn scoped(_1: u8) -> u8 {
    let mut _0: u8;
    scope 1 {
        debug input => _1;
        let _2: u8;
        scope 2 {
            debug temporary => _2;
        }
    }

    bb0: {
        _2 = copy _1;
        _0 = copy _2;
        return;
    }
}
";

const FLAT: &str = r"
fn scoped(_1: u8) -> u8 {
    let mut _0: u8;
    let _2: u8;

    bb0: {
        _2 = copy _1;
        _0 = copy _2;
        return;
    }
}
";

fn rendered(input: &str) -> (String, String) {
    let mut arena = TermArena::new();
    let symbol = arena.declare("input", Sort::BitVec(8)).unwrap();
    let parameter = arena.var(symbol);
    let checked = reflect_scalar_into_checked(
        &mut arena,
        &[parameter],
        input,
        &MirScalarConfig::new("scoped", 64),
    )
    .unwrap();
    (
        render(&arena, checked.result.value),
        render(&arena, checked.panic),
    )
}

fn nested(depth: usize) -> String {
    let mut source = String::from("fn nested(_1: u8) -> u8 {\n    let mut _0: u8;\n");
    for id in 1..=depth {
        writeln!(source, "    scope {id} {{").expect("writing to a String cannot fail");
    }
    for _ in 0..depth {
        source.push_str("    }\n");
    }
    source.push_str("    bb0: {\n        _0 = copy _1;\n        return;\n    }\n}\n");
    source
}

#[test]
fn nested_scopes_flatten_typed_locals_without_semantic_effect() {
    let parsed = parse_function(SCOPED, "scoped").unwrap();
    assert_eq!(parsed.locals.len(), 2);
    assert_eq!(parsed.locals[0].local, 0);
    assert_eq!(parsed.locals[1].local, 2);
    assert_eq!(
        parsed.locals[1].ty,
        MirType::Integer {
            width: 8,
            signed: false,
        }
    );
    assert!(parsed.locals[0].span.start < parsed.locals[1].span.start);
    assert_eq!(rendered(SCOPED), rendered(FLAT));

    let empty = SCOPED.replace("        let _2: u8;", "");
    assert_eq!(parse_function(&empty, "scoped").unwrap().locals.len(), 1);
}

#[test]
fn scope_depth_and_structure_fail_closed() {
    assert!(parse_function(&nested(64), "nested").is_ok());
    assert_eq!(
        parse_function(&nested(65), "nested").unwrap_err().kind(),
        ParseErrorKind::MalformedStatement
    );

    for mutation in [
        SCOPED.replace("scope 1 {", "scope x {"),
        SCOPED.replace("scope 1 {", "scope 1 { trailing"),
        SCOPED.replace("scope 1 {", "scope 1"),
        SCOPED.replace("        debug input => _1;", "        _2 = copy _1;"),
        SCOPED.replace("        debug input => _1;", "        bb9: {"),
    ] {
        assert!(matches!(
            parse_function(&mutation, "scoped").unwrap_err().kind(),
            ParseErrorKind::MalformedStatement | ParseErrorKind::UnsupportedStatement
        ));
    }

    let unclosed = SCOPED.replacen("    }\n\n    bb0", "\n    bb0", 1);
    assert!(matches!(
        parse_function(&unclosed, "scoped").unwrap_err().kind(),
        ParseErrorKind::MalformedStatement | ParseErrorKind::UnsupportedStatement
    ));
}

#[test]
fn scoped_local_duplicates_and_types_keep_existing_classes() {
    let duplicate = SCOPED.replace("        let _2: u8;", "        let _0: u8;");
    assert_eq!(
        parse_function(&duplicate, "scoped").unwrap_err().kind(),
        ParseErrorKind::DuplicateLocal
    );
    let unsupported = SCOPED.replace("let _2: u8;", "let _2: String;");
    assert_eq!(
        parse_function(&unsupported, "scoped").unwrap_err().kind(),
        ParseErrorKind::UnsupportedType
    );
}

#[test]
fn scope_prefixed_noise_never_panics_or_changes_diagnostics() {
    let mut state = 0x52_31_19_07_u32;
    for _ in 0..1_000 {
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let input = format!(
            "fn noisy(_1: u8) -> u8 {{\n    scope {}{}\n}}\n",
            state,
            if state & 1 == 0 { " {" } else { " trailing" }
        );
        let first = catch_unwind(|| parse_function(&input, "noisy"));
        assert!(first.is_ok());
        let second = parse_function(&input, "noisy");
        assert_eq!(first.unwrap(), second);
    }
}
