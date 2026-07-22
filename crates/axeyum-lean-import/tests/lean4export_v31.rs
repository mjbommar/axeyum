//! End-to-end and mutation tests for the official format-3.1 fixture.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use axeyum_lean_kernel::Kernel;

const FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson");
const RECURSIVE_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson");
const PROJECTION_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-projection.ndjson");
const NAT_LITERAL_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nat-literal.ndjson");
const QUOTIENT_FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson");

fn import(text: &str) -> Result<(Kernel, axeyum_lean_import::ImportReport), ImportError> {
    let mut kernel = Kernel::new();
    let report = import_ndjson(
        Cursor::new(text.as_bytes()),
        &mut kernel,
        ImportLimits::default(),
    )?;
    Ok((kernel, report))
}

fn metadata() -> &'static str {
    r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"test","version":"4.30.0"}}}"#
}

#[test]
fn official_flat_fixture_is_independently_admitted() {
    let (kernel, report) = import(FIXTURE).expect("the official flat fixture admits");
    assert_eq!(report.format_version, "3.1.0");
    assert_eq!(report.lean_version, "4.30.0");
    assert_eq!(
        report.lean_githash,
        "d024af099ca4bf2c86f649261ebf59565dc8c622"
    );
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (14, 2, 43, 5, 8)
    );
    assert_eq!(report.axioms, ["P"]);
    let admitted: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
        .collect();
    assert_eq!(
        admitted,
        [
            "Two",
            "Two.left",
            "Two.right",
            "Two.rec",
            "Two.recOn",
            "chooseLeft",
            "P",
            "identity",
        ]
    );
}

#[test]
fn official_direct_recursive_families_are_independently_admitted() {
    let (kernel, report) = import(RECURSIVE_FIXTURE).expect("direct-recursive fixture admits");
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        (30, 4, 130, 5, 11)
    );
    assert!(report.axioms.is_empty());
    let admitted: Vec<_> = kernel
        .environment()
        .iter()
        .map(|(_, declaration)| kernel.display_name(declaration.name()).to_string())
        .collect();
    assert_eq!(
        admitted,
        [
            "MiniList",
            "MiniList.nil",
            "MiniList.cons",
            "MiniList.rec",
            "MiniList.recOn",
            "MiniNat",
            "MiniNat.zero",
            "MiniNat.succ",
            "MiniNat.rec",
            "miniOne",
            "MiniNat.recOn",
        ]
    );
}

#[test]
fn official_blocker_fixtures_have_stable_first_declines() {
    let cases = [
        (PROJECTION_FIXTURE, 81, "expr-projection"),
        // `Nat`'s dependency closure reaches a structure projection before the
        // literal record, making projection the measured first implementation
        // slice rather than an ordering guess.
        (NAT_LITERAL_FIXTURE, 106, "expr-projection"),
        (QUOTIENT_FIXTURE, 65, "quotient-package"),
    ];
    for (fixture, expected_line, expected_code) in cases {
        let error = import(fixture).unwrap_err();
        assert!(
            matches!(
                error,
                ImportError::Unsupported { line, code }
                    if line == expected_line && code == expected_code
            ),
            "{error:?}",
        );
    }
}

#[test]
fn repeated_import_is_deterministic() {
    let (first_kernel, first_report) = import(FIXTURE).unwrap();
    let (second_kernel, second_report) = import(FIXTURE).unwrap();
    assert_eq!(first_report, second_report);
    let first: Vec<_> = first_kernel
        .environment()
        .iter()
        .map(|(_, declaration)| format!("{declaration:?}"))
        .collect();
    let second: Vec<_> = second_kernel
        .environment()
        .iter()
        .map(|(_, declaration)| format!("{declaration:?}"))
        .collect();
    assert_eq!(first, second);
}

#[test]
fn unknown_record_fails_closed() {
    let text = format!("{}\n{{\"mystery\":{{}}}}\n", metadata());
    let error = import(&text).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 2, .. }),
        "{error:?}"
    );
}

#[test]
fn forward_expression_reference_fails_closed() {
    let text = format!(
        "{}\n{{\"ie\":0,\"app\":{{\"fn\":1,\"arg\":1}}}}\n",
        metadata()
    );
    let error = import(&text).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 2, .. }),
        "{error:?}"
    );
}

#[test]
fn projection_and_unknown_format_have_stable_declines() {
    let projection = format!(
        concat!(
            "{}\n",
            "{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"T\"}}}}\n",
            "{{\"ie\":0,\"bvar\":0}}\n",
            "{{\"ie\":1,\"proj\":{{\"typeName\":1,\"idx\":0,\"struct\":0}}}}\n"
        ),
        metadata()
    );
    let error = import(&projection).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Unsupported {
            line: 4,
            code: "expr-projection"
        }
    ));

    let wrong_format = metadata().replace("3.1.0", "4.0.0");
    let error = import(&wrong_format).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Unsupported {
            line: 1,
            code: "format-version"
        }
    ));
}

#[test]
fn tampered_theorem_value_is_rejected_by_kernel() {
    let tampered = FIXTURE.replace(
        r#"{"ie":42,"lam":{"binderInfo":"default","body":4,"name":14,"type":40}}"#,
        r#"{"ie":42,"lam":{"binderInfo":"default","body":39,"name":14,"type":40}}"#,
    );
    assert_ne!(tampered, FIXTURE);
    let error = import(&tampered).unwrap_err();
    assert!(
        matches!(
            error,
            ImportError::Kernel {
                ref declaration,
                ..
            } if declaration == "identity"
        ),
        "{error:?}"
    );
}

#[test]
fn tampered_recursor_rule_is_rejected_before_later_declarations() {
    let tampered = FIXTURE.replacen(r#""rhs":18"#, r#""rhs":17"#, 1);
    assert_ne!(tampered, FIXTURE);
    let error = import(&tampered).unwrap_err();
    assert!(
        matches!(error, ImportError::Malformed { line: 35, .. }),
        "{error:?}"
    );
}

#[test]
fn partial_definition_is_rejected() {
    let text = format!(
        concat!(
            "{}\n",
            "{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"loop\"}}}}\n",
            "{{\"ie\":0,\"sort\":0}}\n",
            "{{\"def\":{{\"name\":1,\"levelParams\":[],\"type\":0,",
            "\"value\":0,\"hints\":\"opaque\",\"safety\":\"partial\",\"all\":[1]}}}}\n"
        ),
        metadata()
    );
    let error = import(&text).unwrap_err();
    assert!(matches!(
        error,
        ImportError::Unsupported {
            line: 4,
            code: "declaration-unsafe-or-partial"
        }
    ));
}

#[test]
fn resource_limits_reject_before_unbounded_import() {
    let mut kernel = Kernel::new();
    let error = import_ndjson(
        Cursor::new(FIXTURE.as_bytes()),
        &mut kernel,
        ImportLimits {
            max_line_bytes: 32,
            max_records: 10,
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        ImportError::LineLimit { line: 1, limit: 32 }
    ));

    let mut kernel = Kernel::new();
    let error = import_ndjson(
        Cursor::new(FIXTURE.as_bytes()),
        &mut kernel,
        ImportLimits {
            max_line_bytes: 16 * 1024 * 1024,
            max_records: 1,
        },
    )
    .unwrap_err();
    assert!(matches!(error, ImportError::RecordLimit { limit: 1 }));
}
