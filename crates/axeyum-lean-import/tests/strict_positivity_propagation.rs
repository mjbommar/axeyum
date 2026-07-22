//! Synthetic format-3.1 propagation test for TL2.11's kernel error boundary.
//! The base is an official stream; the inserted expression/group edit is
//! explicitly synthetic and receives no official-wire credit.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use axeyum_lean_kernel::KernelError;

const CONTROL: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson");
const NEW_NEGATIVE_EXPRESSION: &str =
    r#"{"forallE":{"binderInfo":"default","body":84,"name":10,"type":85},"ie":114}"#;
const MINI_NAT_GROUP_MARKER: &str =
    r#""name":23,"numIndices":0,"numNested":0,"numParams":0,"type":83"#;
const ORIGINAL_SUCCESSOR: &str = r#""name":25,"numFields":1,"numParams":0,"type":85"#;
const MUTATED_SUCCESSOR: &str = r#""name":25,"numFields":1,"numParams":0,"type":114"#;

fn synthetic_negative_stream() -> String {
    let mut output = String::new();
    let mut found = false;
    for line in CONTROL.lines() {
        if line.contains(MINI_NAT_GROUP_MARKER) {
            assert!(line.contains(ORIGINAL_SUCCESSOR));
            output.push_str(NEW_NEGATIVE_EXPRESSION);
            output.push('\n');
            output.push_str(&line.replacen(ORIGINAL_SUCCESSOR, MUTATED_SUCCESSOR, 1));
            output.push('\n');
            found = true;
            break;
        }
        output.push_str(line);
        output.push('\n');
    }
    assert!(found, "official MiniNat group marker drifted");
    output
}

#[test]
fn synthetic_negative_constructor_propagates_typed_error_without_publication() {
    let control = import_ndjson(Cursor::new(CONTROL.as_bytes()), ImportLimits::default())
        .expect("official direct-recursive control should complete");
    assert_eq!(control.report().admitted_declarations, 11);

    let mutation = synthetic_negative_stream();
    let error = import_ndjson(Cursor::new(mutation.as_bytes()), ImportLimits::default())
        .expect_err("synthetic non-positive group must not publish CompletedImport");
    assert!(
        matches!(
            error,
            ImportError::Kernel {
                line: 151,
                ref declaration,
                source: KernelError::NonPositiveInductiveOccurrence {
                    field_index: 0,
                    ..
                },
            } if declaration == "MiniNat"
        ),
        "unexpected synthetic propagation result: {error:?}"
    );
}
