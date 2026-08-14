//! Differential round-trip of the `lean4export` NDJSON 3.1.0 **emitter**
//! (`axeyum-lean-kernel`) against the **importer** (this crate).
//!
//! The two are written against the same external specification and share no
//! code, so this is a differential test rather than a tautology. The invariant
//! compared is the ADR-0350 canonical identity manifest — per-declaration
//! structural content plus direct-dependency digests — which by construction
//! ignores wire and arena allocation order.
//!
//! The strongest case here is import-export-import over **Lean's own output**:
//! every committed official v4.30 fixture is imported, re-emitted by our writer,
//! and imported again; the manifests must match. Those artifacts were produced
//! by `lean4export` from a real Lean 4.30.0, not by this project.

use std::io::Cursor;

use axeyum_lean_import::{ImportLimits, ImportReport, import_ndjson};
use axeyum_lean_kernel::{Kernel, Lean4ExportMetadata, build_logic_prelude, build_nat_prelude};

/// Every committed official `lean4export` v4.30 fixture.
const FIXTURES: &[(&str, &str)] = &[
    (
        "axeyum-probe",
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson"),
    ),
    (
        "construct-matrix-mutual",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson"
        ),
    ),
    (
        "construct-matrix-nested",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-nested.ndjson"
        ),
    ),
    (
        "construct-matrix-recursive-indexed",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-recursive-indexed.ndjson"
        ),
    ),
    (
        "construct-matrix-reflexive-higher-order",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson"
        ),
    ),
    (
        "construct-matrix-well-founded",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-well-founded.ndjson"
        ),
    ),
    (
        "mutual-cross-computation",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-mutual-cross-computation.ndjson"
        ),
    ),
    (
        "mutual-indexed-computation",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-mutual-indexed-computation.ndjson"
        ),
    ),
    (
        "nat-literal",
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nat-literal.ndjson"),
    ),
    (
        "nested-aux-computation",
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nested-aux-computation.ndjson"),
    ),
    (
        "nested-indexed-computation",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-nested-indexed-computation.ndjson"
        ),
    ),
    (
        "nested-repeated-container-computation",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-nested-repeated-container-computation.ndjson"
        ),
    ),
    (
        "projection",
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-projection.ndjson"),
    ),
    (
        "quotient",
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson"),
    ),
    (
        "recursive-ih-acc-computation",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-recursive-ih-acc-computation.ndjson"
        ),
    ),
    (
        "recursive-ih-vector-computation",
        include_str!(
            "../../../docs/plan/fixtures/lean4export-v4.30-recursive-ih-vector-computation.ndjson"
        ),
    ),
    (
        "recursive-shapes",
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson"),
    ),
];

fn import(stream: &str, label: &str) -> (Kernel, ImportReport) {
    import_ndjson(Cursor::new(stream.as_bytes()), ImportLimits::default())
        .unwrap_or_else(|error| panic!("{label} must import: {error}"))
        .into_parts()
}

fn emit(kernel: &Kernel, metadata: &Lean4ExportMetadata, label: &str) -> String {
    kernel
        .render_lean4export_ndjson(metadata)
        .unwrap_or_else(|error| panic!("{label} must emit: {error}"))
}

fn fixture_metadata(report: &ImportReport) -> Lean4ExportMetadata {
    Lean4ExportMetadata {
        lean_version: report.lean_version.clone(),
        lean_githash: report.lean_githash.clone(),
        exporter_version: report.exporter_version.clone(),
    }
}

fn assert_same_manifest(first: &ImportReport, second: &ImportReport, label: &str) {
    assert_eq!(
        first.identity_version, second.identity_version,
        "{label}: identity schema"
    );
    assert_eq!(
        first.declaration_identities.len(),
        second.declaration_identities.len(),
        "{label}: declaration count"
    );
    assert!(
        !first.declaration_identities.is_empty(),
        "{label}: a vacuous manifest proves nothing"
    );
    assert_eq!(
        first.declaration_identities, second.declaration_identities,
        "{label}: canonical declaration identities"
    );
    assert_eq!(
        first.axiom_identities, second.axiom_identities,
        "{label}: axiom identities"
    );
    assert_eq!(
        first.admitted_declarations, second.admitted_declarations,
        "{label}: admitted declaration count"
    );
}

/// Import-export-import over Lean's own output: each official v4.30 fixture is
/// imported, re-emitted by our writer, and imported again. The canonical
/// identity manifests must be equal.
#[test]
fn official_fixtures_survive_import_export_import() {
    assert!(FIXTURES.len() >= 17, "every committed fixture must be run");
    for (label, stream) in FIXTURES {
        let (kernel, report) = import(stream, label);
        let metadata = fixture_metadata(&report);
        let emitted = emit(&kernel, &metadata, label);
        let (_, reimported) = import(&emitted, &format!("{label} (re-emitted)"));
        assert_same_manifest(&report, &reimported, label);
        assert_eq!(
            (
                report.names,
                report.levels,
                report.expressions,
                report.declaration_records
            )
                .3,
            reimported.declaration_records,
            "{label}: declaration record count"
        );
    }
}

/// A second emit/import cycle must be a fixed point: the emitter's own output,
/// re-imported and re-emitted, is byte-identical. This is the determinism
/// promise (no hash-map iteration order in output) stated as a measurement.
#[test]
fn re_emission_is_a_byte_stable_fixed_point() {
    for (label, stream) in FIXTURES {
        let (kernel, report) = import(stream, label);
        let metadata = fixture_metadata(&report);
        let first = emit(&kernel, &metadata, label);
        let (second_kernel, _) = import(&first, label);
        let second = emit(&second_kernel, &metadata, label);
        assert_eq!(first, second, "{label}: emission is not a fixed point");
        // Emitting the same kernel twice must also be byte-identical.
        assert_eq!(first, emit(&kernel, &metadata, label), "{label}: unstable");
    }
}

/// How closely the emitter reproduces Lean's own bytes. Byte identity is *not*
/// the contract (Lean's exporter chooses its own name/level/expression
/// numbering and emits metadata this kernel does not model), so this test
/// records the measurement instead of asserting a coincidence.
#[test]
fn byte_identity_against_official_fixtures_is_measured() {
    let mut identical = Vec::new();
    let mut differing = Vec::new();
    for (label, stream) in FIXTURES {
        let (kernel, report) = import(stream, label);
        let emitted = emit(&kernel, &fixture_metadata(&report), label);
        if emitted == *stream {
            identical.push(*label);
        } else {
            differing.push((
                *label,
                stream.lines().count(),
                emitted.lines().count(),
                first_difference(stream, &emitted),
            ));
        }
    }
    println!("byte-identical fixtures: {identical:?}");
    for (label, official, ours, difference) in &differing {
        println!(
            "{label}: official {official} records, ours {ours}; first difference {difference}"
        );
    }
    assert_eq!(
        identical.len() + differing.len(),
        FIXTURES.len(),
        "every fixture must be classified"
    );
}

fn first_difference(official: &str, ours: &str) -> String {
    for (index, (left, right)) in official.lines().zip(ours.lines()).enumerate() {
        if left != right {
            return format!("record {}: official {left} / ours {right}", index + 1);
        }
    }
    "records are a prefix of one another".to_owned()
}

/// An axeyum-built development (not one of Lean's) also survives the round
/// trip: emit, import, re-emit, import, and compare manifests.
#[test]
fn axeyum_built_prelude_round_trips() {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude must build");
    build_nat_prelude(&mut kernel).expect("nat prelude must build");
    let declarations = kernel.environment().len();
    assert!(declarations > 20, "the prelude must be non-trivial");

    let metadata = Lean4ExportMetadata::axeyum("4.30.0");
    let emitted = emit(&kernel, &metadata, "axeyum prelude");
    let (round_tripped, report) = import(&emitted, "axeyum prelude");
    assert_eq!(
        round_tripped.environment().len(),
        declarations,
        "an independent re-admission must reproduce every declaration"
    );
    let again = emit(&round_tripped, &metadata, "axeyum prelude (re-emitted)");
    assert_eq!(emitted, again, "re-emission must be byte-stable");
    let (_, second_report) = import(&again, "axeyum prelude (re-emitted)");
    assert_same_manifest(&report, &second_report, "axeyum prelude");
}

/// Every declaration name the source kernel checked appears in the re-admitted
/// environment. A silently dropped declaration would produce a stream a
/// consumer checks *less* of than the kernel did.
#[test]
fn no_declaration_is_dropped_by_the_emitter() {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude must build");
    build_nat_prelude(&mut kernel).expect("nat prelude must build");
    let expected: Vec<String> = kernel
        .environment()
        .iter()
        .map(|(&name, _)| kernel.display_name(name).to_string())
        .collect();

    let emitted = emit(&kernel, &Lean4ExportMetadata::axeyum("4.30.0"), "prelude");
    let (round_tripped, _) = import(&emitted, "prelude");
    let mut admitted: Vec<String> = round_tripped
        .environment()
        .iter()
        .map(|(&name, _)| round_tripped.display_name(name).to_string())
        .collect();
    admitted.sort();
    let mut expected = expected;
    expected.sort();
    assert_eq!(expected, admitted);
}

// ---------------------------------------------------------------------------
// Wire-metadata comparison against Lean's own bytes.
//
// The importer validates most inductive metadata against what the independent
// kernel generates, so the round-trip above already covers `numParams`,
// `numIndices`, `numFields`, `cidx`, `isRec` and `numNested`. Three fields it
// treats as descriptive — `k`, `isReflexive` and the recursor premise counts —
// would not be caught by a round trip, and `k` in particular is *derived* by
// the emitter because the kernel does not store it. These are compared field by
// field against the official fixtures, which Lean produced.
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;

use serde_json::Value;

#[derive(Debug, PartialEq, Eq)]
struct FamilyWire {
    num_params: u64,
    num_indices: u64,
    num_nested: u64,
    is_rec: bool,
    is_reflexive: bool,
}

#[derive(Debug, PartialEq, Eq)]
struct RecursorWire {
    k: bool,
    num_params: u64,
    num_indices: u64,
    num_motives: u64,
    num_minors: u64,
    rules: usize,
}

#[derive(Debug, Default)]
struct WireMetadata {
    families: BTreeMap<String, FamilyWire>,
    recursors: BTreeMap<String, RecursorWire>,
}

fn resolve(record: &Value, field: &str) -> usize {
    usize::try_from(record[field].as_u64().expect("index field")).expect("index fits usize")
}

fn wire_metadata(stream: &str) -> WireMetadata {
    let mut names: Vec<String> = vec![String::new()];
    let mut metadata = WireMetadata::default();
    for line in stream.lines() {
        let record: Value = serde_json::from_str(line).expect("emitted records must be JSON");
        if let Some(name) = record.get("in") {
            let index = usize::try_from(name.as_u64().expect("name index")).expect("index");
            assert_eq!(index, names.len(), "name indices must be dense");
            let rendered = if let Some(entry) = record.get("str") {
                let parent = &names[resolve(entry, "pre")];
                let component = entry["str"].as_str().expect("str");
                if parent.is_empty() {
                    component.to_owned()
                } else {
                    format!("{parent}.{component}")
                }
            } else {
                let entry = &record["num"];
                let parent = &names[resolve(entry, "pre")];
                format!("{parent}.{}", entry["i"].as_u64().expect("i"))
            };
            names.push(rendered);
            continue;
        }
        let Some(group) = record.get("inductive") else {
            continue;
        };
        for family in group["types"].as_array().expect("types") {
            metadata.families.insert(
                names[resolve(family, "name")].clone(),
                FamilyWire {
                    num_params: family["numParams"].as_u64().expect("numParams"),
                    num_indices: family["numIndices"].as_u64().expect("numIndices"),
                    num_nested: family["numNested"].as_u64().expect("numNested"),
                    is_rec: family["isRec"].as_bool().expect("isRec"),
                    is_reflexive: family["isReflexive"].as_bool().expect("isReflexive"),
                },
            );
        }
        for recursor in group["recs"].as_array().expect("recs") {
            metadata.recursors.insert(
                names[resolve(recursor, "name")].clone(),
                RecursorWire {
                    k: recursor["k"].as_bool().expect("k"),
                    num_params: recursor["numParams"].as_u64().expect("numParams"),
                    num_indices: recursor["numIndices"].as_u64().expect("numIndices"),
                    num_motives: recursor["numMotives"].as_u64().expect("numMotives"),
                    num_minors: recursor["numMinors"].as_u64().expect("numMinors"),
                    rules: recursor["rules"].as_array().expect("rules").len(),
                },
            );
        }
    }
    metadata
}

/// The inductive metadata this writer emits must equal, field for field, what
/// Lean's own exporter wrote — including the `k` flag, which the kernel does
/// not store and the emitter therefore derives.
#[test]
fn emitted_inductive_wire_metadata_equals_lean_s_own() {
    let mut families = 0usize;
    let mut recursors = 0usize;
    let mut k_true = 0usize;
    for (label, stream) in FIXTURES {
        let (kernel, report) = import(stream, label);
        let emitted = emit(&kernel, &fixture_metadata(&report), label);
        let official = wire_metadata(stream);
        let ours = wire_metadata(&emitted);
        assert_eq!(
            official.families.keys().collect::<Vec<_>>(),
            ours.families.keys().collect::<Vec<_>>(),
            "{label}: exported family set"
        );
        assert_eq!(
            official.recursors.keys().collect::<Vec<_>>(),
            ours.recursors.keys().collect::<Vec<_>>(),
            "{label}: exported recursor set"
        );
        for (name, expected) in &official.families {
            assert_eq!(Some(expected), ours.families.get(name), "{label}: {name}");
        }
        for (name, expected) in &official.recursors {
            assert_eq!(Some(expected), ours.recursors.get(name), "{label}: {name}");
            k_true += usize::from(expected.k);
        }
        families += official.families.len();
        recursors += official.recursors.len();
    }
    println!("compared {families} families and {recursors} recursors ({k_true} K-like)");
    assert!(families >= 20, "the comparison must not be vacuous");
    assert!(
        k_true >= 5,
        "the K-like derivation must be exercised in both directions"
    );
}

/// The defect this whole route exists to make impossible, stated on the wire:
/// the logic prelude's `Eq` is 2 parameters and 1 index, and the NDJSON writer
/// carries that separation natively — a flattened telescope cannot be expressed.
#[test]
fn logic_prelude_eq_exports_two_parameters_and_one_index() {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let emitted = emit(&kernel, &Lean4ExportMetadata::axeyum("4.30.0"), "logic");
    let metadata = wire_metadata(&emitted);
    let eq = metadata.families.get("Eq").expect("Eq must be exported");
    assert_eq!(eq.num_params, 2, "Eq has parameters α and a");
    assert_eq!(eq.num_indices, 1, "Eq has one index");
    assert!(!eq.is_rec);
    let recursor = metadata.recursors.get("Eq.rec").expect("Eq.rec");
    assert!(recursor.k, "Eq is Lean's canonical K-like inductive");
    assert_eq!(recursor.num_params, 2);
    assert_eq!(recursor.num_indices, 1);
}
