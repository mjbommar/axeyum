//! End-to-end checks for the standalone canonical-artifact verifier.

use std::fs;
use std::process::Command;

use axeyum_cas::gf2::{Gf2Limits, Gf2Poly, certify_irreducible};
use axeyum_cas::gf2_artifact::{ArtifactLimits, HalfDegreeArtifact, to_canonical_json};

fn control_json() -> String {
    let limits = Gf2Limits::default();
    let polynomial = Gf2Poly::from_exponents(&[0, 1, 4], limits).unwrap();
    let artifact = HalfDegreeArtifact {
        id: "cli-degree-4".to_owned(),
        producer: "integration-test".to_owned(),
        certificate: certify_irreducible(&polynomial, limits)
            .unwrap()
            .expect("control must be irreducible"),
    };
    to_canonical_json(&artifact, ArtifactLimits::default()).unwrap()
}

#[test]
fn standalone_checker_accepts_canonical_bytes_and_rejects_mutation() {
    let path = std::env::temp_dir().join(format!(
        "axeyum-gf2-artifact-cli-{}.json",
        std::process::id()
    ));
    let canonical = control_json();
    fs::write(&path, &canonical).unwrap();

    let accepted = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-check"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(accepted.status.success());
    assert_eq!(
        String::from_utf8(accepted.stdout).unwrap(),
        "GF2_CHECK|status=PASS|id=cli-degree-4|degree=4|primary=PASS|independent=PASS\n"
    );

    let mutated = canonical.replacen("0000000000000004", "0000000000000005", 1);
    fs::write(&path, mutated).unwrap();
    let rejected = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-check"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    assert!(
        String::from_utf8(rejected.stderr)
            .unwrap()
            .contains("status=FAIL")
    );

    fs::remove_file(path).unwrap();
}
