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
use axeyum_lean_kernel::{
    Declaration, Kernel, Lean4ExportMetadata, Lit, ReducibilityHint, build_logic_prelude,
    build_nat_prelude,
};

// The Lean-shaped `String` environment lives with the kernel's own tests, and is
// shared here by path rather than duplicated: both crates are `publish = false`,
// so the cross-crate include costs nothing (`lean_probe.rs` is shared the same
// way).
#[path = "../../axeyum-lean-kernel/tests/support/lean_shaped_string.rs"]
mod lean_shaped_string;

use lean_shaped_string::Mutation;

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

/// A root-selected stream is a complete environment in its own right: its
/// atomic dependency closure re-admits in a fresh kernel, unrelated declarations
/// stay unavailable, and selecting the same root after re-admission is
/// byte-stable.
#[test]
fn root_selected_environment_round_trips_without_unrelated_declarations() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let metadata = Lean4ExportMetadata::axeyum("4.30.0");
    let emitted = kernel
        .render_lean4export_ndjson_roots(&metadata, &[logic.true_intro])
        .expect("the True constructor closure must emit");
    let (round_tripped, report) = import(&emitted, "root-selected True");
    let admitted: Vec<_> = report
        .declaration_identities
        .iter()
        .map(|identity| identity.name.as_str())
        .collect();
    assert_eq!(admitted, ["True", "True.rec", "True.intro"]);
    assert!(
        round_tripped
            .environment()
            .iter()
            .all(|(&name, _)| !round_tripped
                .display_name(name)
                .to_string()
                .starts_with("False")),
        "an unrelated inductive must not enter the fresh kernel"
    );
    let true_intro = round_tripped
        .environment()
        .iter()
        .find_map(|(&name, _)| {
            (round_tripped.display_name(name).to_string() == "True.intro").then_some(name)
        })
        .expect("the selected constructor must re-admit");
    let again = round_tripped
        .render_lean4export_ndjson_roots(&metadata, &[true_intro])
        .expect("the re-admitted root must re-emit");
    assert_eq!(emitted, again);
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

/// A **string literal** survives emit / import / re-emit, payload and all.
///
/// The writer refused `Lit::Str` outright until 2026-08-15 (`ExportError::
/// StringLiteral`), which was consistent while the reader refused it too. Both
/// arms are open now, so the escape grammar is load-bearing in a way it was not
/// before: `strVal` payloads carry newlines, tabs, quotes, NULs and astral
/// scalars routinely, and Lean's `Json.escapeAux` gives a short escape to only
/// four of them. The corners are asserted here rather than assumed.
#[test]
fn a_string_literal_round_trips_with_its_payload() {
    let payloads = [
        "",
        "axeyum",
        "a\"b\\c",
        "\n\t\r",
        "\u{0}\u{1f}\u{7f}",
        "\u{e9}",
        "e\u{301}",
        "\u{2192}",
        "\u{1f642}",
    ];
    for payload in payloads {
        let (mut kernel, env) = lean_shaped_string::lean_shaped_kernel(Mutation::None);
        let anon = kernel.anon();
        let name = kernel.name_str(anon, "axeyumStringProbe");
        let value = kernel.lit(Lit::Str(payload.to_owned()));
        kernel
            .add_declaration(Declaration::Definition {
                name,
                uparams: Vec::new(),
                ty: env.string_type,
                value,
                hint: ReducibilityHint::Regular(0),
            })
            .unwrap_or_else(|error| panic!("{payload:?}: the probe must type-check: {error:?}"));

        let metadata = Lean4ExportMetadata::axeyum("4.30.0");
        let emitted = emit(&kernel, &metadata, "string probe");
        let (round_tripped, report) = import(&emitted, "string probe");
        let again = emit(&round_tripped, &metadata, "string probe (re-emitted)");
        assert_eq!(
            emitted, again,
            "{payload:?}: re-emission is not byte-stable"
        );
        let (_, second_report) = import(&again, "string probe (re-emitted)");
        assert_same_manifest(&report, &second_report, "string probe");

        // The payload itself, not merely a declaration of the same shape: the
        // identity manifest hashes `Lit::Str` by its raw UTF-8 bytes, so a
        // mangled escape would change it — but reading the literal back is the
        // check that says so in one line.
        let recovered = round_tripped
            .environment()
            .iter()
            .find_map(|(_, declaration)| {
                (round_tripped.display_name(declaration.name()).to_string() == "axeyumStringProbe")
                    .then(|| declaration.value())
                    .flatten()
            })
            .unwrap_or_else(|| panic!("{payload:?}: the probe survived import"));
        assert!(
            matches!(
                round_tripped.expr_node(recovered),
                axeyum_lean_kernel::ExprNode::Lit(Lit::Str(got)) if got == payload
            ),
            "{payload:?}: payload did not survive the round trip"
        );
    }
}

/// The reader decodes Lean's own escape grammar, and decodes it to **scalars**.
///
/// Our writer emits every character at or above `0x20` raw, so a round trip
/// alone never exercises `\uXXXX` — yet that is exactly what `lean4export` emits
/// for a name component and what a hand-written stream may use anywhere. This
/// rewrites one emitted payload into its escaped form and requires the identity
/// manifest to be unchanged, then into a byte-split form and requires it to
/// change. Equal manifests here mean the two spellings decoded to the same
/// Unicode scalar; the second half is what stops "unchanged" from being vacuous.
#[test]
fn escaped_and_raw_string_payloads_decode_to_the_same_scalars() {
    let (mut kernel, env) = lean_shaped_string::lean_shaped_kernel(Mutation::None);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "axeyumStringProbe");
    let value = kernel.lit(Lit::Str("\u{e9}".to_owned()));
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: Vec::new(),
            ty: env.string_type,
            value,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("the probe must type-check");

    let metadata = Lean4ExportMetadata::axeyum("4.30.0");
    let emitted = emit(&kernel, &metadata, "escape probe");
    assert!(
        emitted.contains("\"strVal\":\"\u{e9}\""),
        "the writer emits a printable non-ASCII scalar raw, as Lean does"
    );

    let escaped = emitted.replace("\"strVal\":\"\u{e9}\"", "\"strVal\":\"\\u00e9\"");
    assert_ne!(escaped, emitted, "the rewrite must have applied");
    let (_, baseline) = import(&emitted, "escape probe (raw)");
    let (_, from_escape) = import(&escaped, "escape probe (escaped)");
    assert_same_manifest(&baseline, &from_escape, "escape probe");

    // The control: the UTF-8 *bytes* of the same character, spelled as two
    // scalars, must NOT produce the same identity.
    let byte_split = emitted.replace("\"strVal\":\"\u{e9}\"", "\"strVal\":\"\\u00c3\\u00a9\"");
    let (_, from_bytes) = import(&byte_split, "escape probe (byte-split)");
    assert_ne!(
        baseline.declaration_identities, from_bytes.declaration_identities,
        "a byte-split payload must not hash like the scalar it encodes"
    );
}

/// A `strVal` that is not a JSON string, and one that is not valid Unicode.
#[test]
fn malformed_string_literal_wire_values_reject_before_the_typing_boundary() {
    let metadata = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"test","version":"4.30.0"}}}"#;
    for payload in ["123", "null", "true", "[\"a\"]", "{\"s\":\"a\"}"] {
        let text = format!("{metadata}\n{{\"ie\":0,\"strVal\":{payload}}}\n");
        let error = import_ndjson(Cursor::new(text.as_bytes()), ImportLimits::default())
            .expect_err("a non-string strVal payload must reject");
        assert!(
            matches!(
                error,
                axeyum_lean_import::ImportError::Malformed { line: 2, .. }
            ),
            "{payload}: {error:?}"
        );
    }

    // A lone surrogate is not a Unicode scalar value, so it is a JSON error
    // before the kernel ever sees it -- never repaired, never replaced.
    let text = format!("{metadata}\n{{\"ie\":0,\"strVal\":\"\\ud800\"}}\n");
    assert!(
        import_ndjson(Cursor::new(text.as_bytes()), ImportLimits::default()).is_err(),
        "a lone surrogate must not import"
    );

    // The positive companion: every well-formed payload class parses.
    for payload in [
        r#""""#,
        r#""ab""#,
        r#""\u0041\u00e9""#,
        r#""\n\t\r\u0000""#,
        r#""\ud83d\ude42""#,
    ] {
        let text = format!("{metadata}\n{{\"ie\":0,\"strVal\":{payload}}}\n");
        let completed = import_ndjson(Cursor::new(text.as_bytes()), ImportLimits::default())
            .unwrap_or_else(|error| panic!("{payload} must import: {error}"));
        assert_eq!(completed.report().expressions, 1, "{payload}");
    }
}
