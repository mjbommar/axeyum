//! Golden test for the capability ledger: the committed capability-matrix
//! document must equal what the ledger renders, so trust metadata cannot drift
//! out of sync with the code (architecture review recommendations #3/#4/#9).
#![cfg(feature = "full")]

use axeyum_solver::capabilities::{CAPABILITIES, capability_matrix_markdown};

const DOC: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/research/08-planning/capability-matrix.md"
);

#[test]
fn capability_matrix_doc_is_in_sync() {
    let generated = capability_matrix_markdown();
    if std::env::var_os("UPDATE_CAPABILITY_MATRIX").is_some() {
        std::fs::write(DOC, &generated).expect("write capability-matrix.md");
        return;
    }
    let committed = std::fs::read_to_string(DOC).expect(
        "docs/research/08-planning/capability-matrix.md missing — regenerate with \
         `UPDATE_CAPABILITY_MATRIX=1 cargo test -p axeyum-solver --test capabilities`",
    );
    assert_eq!(
        committed, generated,
        "capability-matrix.md is stale vs the ledger — regenerate with \
         `UPDATE_CAPABILITY_MATRIX=1 cargo test -p axeyum-solver --test capabilities`",
    );
}

#[test]
fn ledger_entries_are_well_formed() {
    assert!(!CAPABILITIES.is_empty(), "ledger must not be empty");
    for c in CAPABILITIES {
        assert!(!c.area.is_empty(), "area must be set");
        assert!(!c.feature.is_empty(), "feature must be set for {}", c.area);
        assert!(
            !c.evidence.is_empty(),
            "evidence must be set for {} / {}",
            c.area,
            c.feature
        );
        assert!(
            c.reference.starts_with("ADR-"),
            "{} / {} must cite an ADR, got {:?}",
            c.area,
            c.feature,
            c.reference
        );
    }
}
