//! Golden test for the reduction trust ledger (P3.0): the committed
//! trust-ledger document must equal what the ledger renders, so the trusted-base
//! inventory cannot drift out of sync with the `TrustId` enum.
#![cfg(feature = "full")]

use axeyum_solver::trust::{ALL_TRUST_IDS, trust_ledger_markdown};

const DOC: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/research/08-planning/trust-ledger.md"
);

#[test]
fn trust_ledger_doc_is_in_sync() {
    let generated = trust_ledger_markdown();
    if std::env::var_os("UPDATE_TRUST_LEDGER").is_some() {
        std::fs::write(DOC, &generated).expect("write trust-ledger.md");
        return;
    }
    let committed = std::fs::read_to_string(DOC).expect(
        "docs/research/08-planning/trust-ledger.md missing — regenerate with \
         `UPDATE_TRUST_LEDGER=1 cargo test -p axeyum-solver --test trust_ledger`",
    );
    assert_eq!(
        committed, generated,
        "trust-ledger.md is stale vs the enum — regenerate with \
         `UPDATE_TRUST_LEDGER=1 cargo test -p axeyum-solver --test trust_ledger`",
    );
}

#[test]
fn trust_ids_are_well_formed() {
    assert!(!ALL_TRUST_IDS.is_empty(), "ledger must not be empty");
    for &id in ALL_TRUST_IDS {
        assert!(!id.label().is_empty(), "label must be set");
        assert!(!id.meaning().is_empty(), "meaning must be set for {id}");
        assert!(
            id.pedantic_level() <= 10,
            "pedantic level out of range for {id}"
        );
        assert!(
            id.reference().starts_with("ADR-"),
            "{id} must cite an ADR, got {:?}",
            id.reference()
        );
    }
}
