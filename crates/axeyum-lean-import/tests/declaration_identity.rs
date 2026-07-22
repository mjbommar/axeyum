//! TL1.7 canonical declaration/dependency identity gates (ADR-0350).

use std::io::Cursor;

use axeyum_lean_import::{
    DeclarationIdentity, DeclarationKind, IDENTITY_VERSION, ImportLimits, ImportReport,
    import_ndjson,
};

const FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson");

const EXACT_FLAT_IDENTITIES: [(&str, &str, &str); 8] = [
    (
        "P",
        "0bdd9ce84a603187f198c16bd42f43af439c2c352d8dcfeabdf13e6f5ef574b6",
        "041ae2cf343563b09c9d79d6ac74935ffb4233bcffc92a9bf3d697cc48eb8759",
    ),
    (
        "Two",
        "a431bac73691b918d0cdce8822d39ecdf959c754ae8c43454268c38d1fdb6aa1",
        "d3d86536c7ba31b56a6f66fd45152b80e439ad1423ba24a91be974b27ca80149",
    ),
    (
        "identity",
        "29ad0b801ead6f7df353cc79e68939398c71b60af92a2631ca5b2a47f3f70dae",
        "fa7dc67300e3ed4639b1c119a46331cfa495f20ccaacea42baa58f641f8f7854",
    ),
    (
        "chooseLeft",
        "eaa81df1dfb8832880e1147055999f806f9ccd871d47454803122bf626a52106",
        "7dc1acc46d7a17f865483389845471a2713b9d0724f1bc250a19d920e248538f",
    ),
    (
        "Two.rec",
        "28f4d4fb59759afe6f189a24288f3197757aa14a367df2c895e86bfda474322f",
        "0b99196e05a3811fcbc39c65bb42823e600e6dfde6b2b2045e4006a8fe44efd1",
    ),
    (
        "Two.left",
        "3f4145dc299f5d3adfc1646166ffd5d2adeb457c3a95c1eff2185cf928034f06",
        "8a72f302e06972ed0a3a87932b1183abc22266d515b43e12e31f5d375580a3e5",
    ),
    (
        "Two.recOn",
        "54dcf3918c57ac7a6084a8eb6dab07a65a2fd1699a81f5493ff60605aee87cbc",
        "52cdcecc8e8f2c07239cf1c5b3ab194e9d22487a45f0b6e500de498a8a67a5d9",
    ),
    (
        "Two.right",
        "3fd1de82b904ae84e20d882629b5ae6de0a79fb2ed8891b717ace05be59d1e34",
        "8a72f302e06972ed0a3a87932b1183abc22266d515b43e12e31f5d375580a3e5",
    ),
];

fn import(text: &str) -> ImportReport {
    import_ndjson(Cursor::new(text.as_bytes()), ImportLimits::default())
        .expect("identity fixture must import")
        .into_parts()
        .1
}

fn declaration<'report>(report: &'report ImportReport, name: &str) -> &'report DeclarationIdentity {
    report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == name)
        .unwrap_or_else(|| panic!("missing declaration identity {name}"))
}

fn is_lower_hex_digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[test]
fn flat_fixture_identity_manifest_is_complete_stable_and_canonically_ordered() {
    let first = import(FIXTURE);
    let second = import(FIXTURE);
    assert_eq!(first.identity_version, IDENTITY_VERSION);
    assert_eq!(first.axiom_identities, second.axiom_identities);
    assert_eq!(first.declaration_identities, second.declaration_identities);
    assert_eq!(first.axiom_identities.len(), 1);
    assert_eq!(first.declaration_identities.len(), 8);

    let names: Vec<_> = first
        .declaration_identities
        .iter()
        .map(|identity| identity.name.as_str())
        .collect();
    assert_eq!(
        names,
        [
            "P",
            "Two",
            "identity",
            "chooseLeft",
            "Two.rec",
            "Two.left",
            "Two.recOn",
            "Two.right",
        ]
    );
    for identity in &first.declaration_identities {
        assert!(is_lower_hex_digest(&identity.content_sha256));
        assert!(is_lower_hex_digest(&identity.dependency_sha256));
        for dependency in &identity.dependencies {
            assert!(is_lower_hex_digest(&dependency.content_sha256));
        }
    }
    let axiom = &first.axiom_identities[0];
    assert_eq!(axiom.name, "P");
    assert_eq!(
        axiom.name_sha256,
        "5c62e091b8c0565f1bafad0dad5934276143ae2ccef7a5381e8ada5b1a8d26d2"
    );
    assert_eq!(
        axiom.type_sha256,
        "57d968860fabe1008d2c72342adec04b70f4bae48b7bcf6ebca915624100c353"
    );

    assert_eq!(declaration(&first, "P").kind, DeclarationKind::Axiom);
    assert_eq!(
        declaration(&first, "chooseLeft").kind,
        DeclarationKind::Definition
    );
    assert_eq!(
        declaration(&first, "identity").kind,
        DeclarationKind::Theorem
    );
    assert_eq!(declaration(&first, "Two").kind, DeclarationKind::Inductive);
    assert_eq!(
        declaration(&first, "Two.left").kind,
        DeclarationKind::Constructor
    );
    assert_eq!(
        declaration(&first, "Two.rec").kind,
        DeclarationKind::Recursor
    );

    let exact: Vec<_> = first
        .declaration_identities
        .iter()
        .map(|identity| {
            (
                identity.name.as_str(),
                identity.content_sha256.as_str(),
                identity.dependency_sha256.as_str(),
            )
        })
        .collect();
    assert_eq!(exact, EXACT_FLAT_IDENTITIES);
}

#[test]
fn independent_declaration_record_reordering_preserves_all_identities() {
    let mut lines: Vec<_> = FIXTURE.lines().map(str::to_owned).collect();
    let moved_index = lines
        .iter()
        .position(|line| line.contains(r#""def":{"all":[10]"#))
        .expect("recOn definition record");
    let moved = lines.remove(moved_index);
    let choose_left_index = lines
        .iter()
        .position(|line| line.contains(r#""def":{"all":[11]"#))
        .expect("chooseLeft definition record");
    lines.insert(choose_left_index + 1, moved);
    let reordered = format!("{}\n", lines.join("\n"));
    assert_ne!(reordered, FIXTURE);

    let original = import(FIXTURE);
    let reordered = import(&reordered);
    assert_eq!(original.axiom_identities, reordered.axiom_identities);
    assert_eq!(
        original.declaration_identities,
        reordered.declaration_identities
    );
}

#[test]
fn axiom_type_mutation_changes_ledger_and_dependency_identity_not_dependent_content() {
    let mutated = FIXTURE.replace(
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":12,"type":39}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":12,"type":0}}"#,
    );
    assert_ne!(mutated, FIXTURE);
    let original = import(FIXTURE);
    let mutated = import(&mutated);

    assert_ne!(
        original.axiom_identities[0].type_sha256,
        mutated.axiom_identities[0].type_sha256
    );
    let original_axiom = declaration(&original, "P");
    let mutated_axiom = declaration(&mutated, "P");
    assert_ne!(original_axiom.content_sha256, mutated_axiom.content_sha256);

    let original_dependent = declaration(&original, "identity");
    let mutated_dependent = declaration(&mutated, "identity");
    assert_eq!(
        original_dependent.content_sha256,
        mutated_dependent.content_sha256
    );
    assert_ne!(
        original_dependent.dependency_sha256,
        mutated_dependent.dependency_sha256
    );
    assert_eq!(
        original_dependent.dependencies[0].content_sha256,
        original_axiom.content_sha256
    );
    assert_eq!(
        mutated_dependent.dependencies[0].content_sha256,
        mutated_axiom.content_sha256
    );
}

#[test]
fn valid_definition_body_mutation_changes_only_the_affected_content_cone() {
    let mutated = FIXTURE.replace(
        r#""name":11,"safety":"safe","type":1,"value":5"#,
        r#""name":11,"safety":"safe","type":1,"value":8"#,
    );
    assert_ne!(mutated, FIXTURE);
    let original = import(FIXTURE);
    let mutated = import(&mutated);

    let original_choice = declaration(&original, "chooseLeft");
    let mutated_choice = declaration(&mutated, "chooseLeft");
    assert_ne!(
        original_choice.content_sha256,
        mutated_choice.content_sha256
    );
    assert_ne!(
        original_choice.dependency_sha256,
        mutated_choice.dependency_sha256
    );
    for name in ["P", "Two", "identity", "Two.recOn"] {
        assert_eq!(
            declaration(&original, name),
            declaration(&mutated, name),
            "unrelated identity drift for {name}"
        );
    }
}

#[test]
fn structural_content_includes_binder_info_omitted_by_the_readable_projection() {
    let mutated = FIXTURE.replace(
        r#"{"forallE":{"binderInfo":"default","body":40,"name":14,"type":40},"ie":41}"#,
        r#"{"forallE":{"binderInfo":"implicit","body":40,"name":14,"type":40},"ie":41}"#,
    );
    assert_ne!(mutated, FIXTURE);
    let original = import(FIXTURE);
    let mutated = import(&mutated);
    let original_identity = declaration(&original, "identity");
    let mutated_identity = declaration(&mutated, "identity");
    assert_ne!(
        original_identity.content_sha256,
        mutated_identity.content_sha256
    );
    assert_eq!(
        original_identity.dependency_sha256,
        mutated_identity.dependency_sha256
    );
}
