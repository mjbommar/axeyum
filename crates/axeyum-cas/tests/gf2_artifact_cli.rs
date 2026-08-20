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

#[test]
fn standalone_producer_writes_once_and_composes_with_checker() {
    let path = std::env::temp_dir().join(format!(
        "axeyum-gf2-artifact-producer-{}.json",
        std::process::id()
    ));
    let produced = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-certify"))
        .args([
            path.as_os_str(),
            "producer-degree-4".as_ref(),
            "integration-test".as_ref(),
            "0,1,4".as_ref(),
        ])
        .output()
        .unwrap();
    assert!(produced.status.success());

    let checked = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-check"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(checked.status.success());

    let overwrite = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-certify"))
        .args([
            path.as_os_str(),
            "producer-degree-4".as_ref(),
            "integration-test".as_ref(),
            "0,1,4".as_ref(),
        ])
        .output()
        .unwrap();
    assert!(!overwrite.status.success());
    fs::remove_file(path).unwrap();
}

#[test]
fn sparse_shard_producer_composes_with_population_and_artifact_checker() {
    let directory =
        std::env::temp_dir().join(format!("axeyum-gf2-search-shard-{}", std::process::id()));
    let produced = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-search"))
        .args([
            directory.as_os_str(),
            "integration-search".as_ref(),
            "1".as_ref(),
            "12".as_ref(),
            "4".as_ref(),
            "10000".as_ref(),
        ])
        .output()
        .unwrap();
    assert!(
        produced.status.success(),
        "{}",
        String::from_utf8_lossy(&produced.stderr)
    );

    let checked = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-check-shard"))
        .arg(&directory)
        .arg("--require-all-found")
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    assert!(
        String::from_utf8(checked.stdout)
            .unwrap()
            .contains("rows=12|found=12|exhausted=0|candidate_limit=0")
    );

    let manifest = directory.join("manifest.json");
    let bytes = fs::read_to_string(&manifest).unwrap();
    fs::write(
        &manifest,
        bytes.replacen("\"degree\": 1", "\"degree\": 2", 1),
    )
    .unwrap();
    let rejected = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-check-shard"))
        .arg(&directory)
        .output()
        .unwrap();
    assert!(!rejected.status.success());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn capell_audit_replays_sources_and_both_composition_checkers() {
    let directory =
        std::env::temp_dir().join(format!("axeyum-gf2-capell-audit-{}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let limits = Gf2Limits::default();
    let cases = [
        ("degree-3.json", "capell-degree-3", vec![0, 1, 3]),
        ("degree-4.json", "capell-degree-4", vec![0, 1, 4]),
    ];
    let mut paths = Vec::new();
    for (name, id, exponents) in cases {
        let polynomial = Gf2Poly::from_exponents(&exponents, limits).unwrap();
        let artifact = HalfDegreeArtifact {
            id: id.to_owned(),
            producer: "integration-test".to_owned(),
            certificate: certify_irreducible(&polynomial, limits)
                .unwrap()
                .expect("control must be irreducible"),
        };
        let path = directory.join(name);
        fs::write(
            &path,
            to_canonical_json(&artifact, ArtifactLimits::default()).unwrap(),
        )
        .unwrap();
        paths.push(path);
    }

    let audited = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-capell-audit"))
        .args(&paths)
        .output()
        .unwrap();
    assert!(
        audited.status.success(),
        "{}",
        String::from_utf8_lossy(&audited.stderr)
    );
    assert_eq!(
        String::from_utf8(audited.stdout).unwrap(),
        "GF2_CAPELL_AUDIT|status=PASS|sources=2|min_degree=3|max_degree=4|eligible=1|odd_degree=1|cube=0|eligible_degrees=4\n"
    );

    let generalized = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-capell-audit"))
        .args(["--prime-limit", "7"])
        .args(&paths)
        .output()
        .unwrap();
    assert!(
        generalized.status.success(),
        "{}",
        String::from_utf8_lossy(&generalized.stderr)
    );
    assert_eq!(
        String::from_utf8(generalized.stdout).unwrap(),
        "GF2_GENERAL_CAPELL_AUDIT|status=PASS|sources=2|min_degree=3|max_degree=4|prime_limit=7|eligible=2|odd_eligible=1|direct_certificates=2|falsification_controls=2|eligible_rays=3:7,4:3\n"
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn composition_tower_cli_retains_a_certified_chain() {
    let output = Command::new(env!("CARGO_BIN_EXE_axeyum-gf2-composition-tower"))
        .args(["hex:13", "3", "1", "10000000"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("GF2_COMPOSITION_TOWER|status=PASS|"));
    assert!(stdout.contains("|base_degree=4|substitution_degree=3|depth=1|degrees=4,12|"));
    assert!(stdout.contains("|substitutions=0,3|"));
}
