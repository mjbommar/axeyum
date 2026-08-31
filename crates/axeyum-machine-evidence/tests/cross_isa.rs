//! Replay and mutation controls for the typed cross-ISA relation.

use std::collections::BTreeSet;
use std::fs;

use axeyum_machine_evidence::{
    EvidenceError, check_cross_isa_absolute_value, check_cross_isa_predicate_control,
    cross_isa_absolute_value_report, write_json,
};

#[test]
fn report_replays_both_paths_and_the_signed_minimum_boundary() {
    let report = cross_isa_absolute_value_report().unwrap();
    assert_eq!(report.cases.len(), 10);
    assert_eq!(
        report
            .cases
            .iter()
            .map(|case| case.input)
            .collect::<BTreeSet<_>>()
            .len(),
        report.cases.len()
    );
    assert!(report.cases.iter().any(|case| case.path == "keep"));
    assert!(report.cases.iter().any(|case| case.path == "negate"));
    assert_eq!(
        report
            .cases
            .iter()
            .filter(|case| !case.mathematical_absolute_value_admitted)
            .count(),
        1
    );

    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("cross-isa.json");
    write_json(&path, &report).unwrap();
    assert_eq!(check_cross_isa_absolute_value(&path).unwrap(), report);
    assert!(matches!(
        check_cross_isa_predicate_control(&path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::write(&path, b"{}\n").unwrap();
    assert!(check_cross_isa_absolute_value(&path).is_err());
}
