//! Frozen current-product outcomes for the official Lean construct matrix.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use axeyum_lean_kernel::KernelError;

const CONTROL: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson");
const RECURSIVE_INDEXED: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-recursive-indexed.ndjson"
);
const REFLEXIVE: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson"
);
const MUTUAL: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson");
const NESTED: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-nested.ndjson");
const WELL_FOUNDED: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-well-founded.ndjson"
);

#[derive(Clone, Copy)]
enum ExpectedOutcome {
    RecursiveIndexedKernel,
    Unsupported { line: usize, code: &'static str },
    Malformed { line: usize, message: &'static str },
}

fn assert_control() {
    let completed = import_ndjson(Cursor::new(CONTROL.as_bytes()), ImportLimits::default())
        .expect("the direct-recursive control must admit before every decline");
    let report = completed.report();
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
            report.axioms.len(),
        ),
        (30, 4, 130, 5, 11, 0)
    );
    assert_eq!(
        (
            report.axiom_identities.len(),
            report.declaration_identities.len()
        ),
        (0, 11)
    );
}

fn assert_decline(case_id: &str, fixture: &str, expected: ExpectedOutcome) {
    let Err(error) = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default()) else {
        panic!("{case_id}: unsupported frozen row unexpectedly admitted");
    };
    match (error, expected) {
        (
            ImportError::Kernel {
                line: 148,
                declaration,
                source: KernelError::RecursiveIndexedNotSupported { .. },
            },
            ExpectedOutcome::RecursiveIndexedKernel,
        ) => assert_eq!(declaration, "AxeyumConstructMatrix.MiniVector"),
        (
            ImportError::Unsupported {
                line: actual_line,
                code: actual_code,
            },
            ExpectedOutcome::Unsupported { line, code },
        ) => assert_eq!((actual_line, actual_code), (line, code), "{case_id}"),
        (
            ImportError::Malformed {
                line: actual_line,
                message: actual_message,
            },
            ExpectedOutcome::Malformed { line, message },
        ) => assert_eq!(
            (actual_line, actual_message.as_str()),
            (line, message),
            "{case_id}"
        ),
        (actual, _) => panic!("{case_id}: unexpected typed outcome: {actual:?}"),
    }
}

#[test]
fn frozen_matrix_outcomes_repeat_with_a_control_before_every_decline() {
    let cases = [
        (
            "recursive-indexed",
            RECURSIVE_INDEXED,
            ExpectedOutcome::RecursiveIndexedKernel,
        ),
        (
            "reflexive-higher-order",
            REFLEXIVE,
            ExpectedOutcome::Unsupported {
                line: 117,
                code: "inductive-reflexive",
            },
        ),
        (
            "mutual",
            MUTUAL,
            ExpectedOutcome::Unsupported {
                line: 233,
                code: "inductive-mutual",
            },
        ),
        (
            "nested",
            NESTED,
            ExpectedOutcome::Malformed {
                line: 248,
                message: "single-family inductive must export one recursor",
            },
        ),
        (
            "well-founded",
            WELL_FOUNDED,
            ExpectedOutcome::Unsupported {
                line: 208,
                code: "inductive-reflexive",
            },
        ),
    ];

    for _ in 0..2 {
        for (case_id, fixture, expected) in cases {
            assert_control();
            assert_decline(case_id, fixture, expected);
        }
    }
}
