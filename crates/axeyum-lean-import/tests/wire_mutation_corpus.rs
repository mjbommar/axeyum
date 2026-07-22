//! TL1.4 deterministic adversarial corpus for the format-3.1 wire boundary.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use serde_json::{Value, json};

const FIXTURE: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson");

#[derive(Debug, Clone, PartialEq, Eq)]
struct MutationCase {
    id: String,
    stream: String,
    expected: &'static str,
}

fn metadata() -> &'static str {
    r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"test","version":"4.30.0"}}}"#
}

fn stream(records: &[String]) -> String {
    let mut result = records.join("\n");
    result.push('\n');
    result
}

fn fixture_lines() -> Vec<String> {
    FIXTURE.lines().map(str::to_owned).collect()
}

fn replace_fixture_line(index: usize, replacement: String) -> String {
    let mut lines = fixture_lines();
    lines[index] = replacement;
    stream(&lines)
}

fn insert_fixture_line(index: usize, inserted: String) -> String {
    let mut lines = fixture_lines();
    lines.insert(index, inserted);
    stream(&lines)
}

fn nested_object(depth: usize) -> Value {
    let mut value = json!({});
    for _ in 0..depth {
        value = json!({"child": value});
    }
    value
}

fn mdata_stream(depth: usize) -> String {
    let record = json!({
        "ie": 1,
        "mdata": {
            "expr": 0,
            "data": nested_object(depth),
        }
    });
    stream(&[
        metadata().to_owned(),
        r#"{"ie":0,"bvar":0}"#.to_owned(),
        serde_json::to_string(&record).expect("serialize nested metadata record"),
    ])
}

fn unicode_stream(name_record: &str) -> String {
    stream(&[
        metadata().to_owned(),
        name_record.to_owned(),
        r#"{"ie":0,"sort":0}"#.to_owned(),
        r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#.to_owned(),
    ])
}

fn push_case(
    cases: &mut Vec<MutationCase>,
    id: impl Into<String>,
    stream: impl Into<String>,
    expected: &'static str,
) {
    cases.push(MutationCase {
        id: id.into(),
        stream: stream.into(),
        expected,
    });
}

#[allow(clippy::too_many_lines)]
fn build_corpus() -> Vec<MutationCase> {
    let mut cases = Vec::new();
    let lines = fixture_lines();

    // The upstream format has no footer. Empty input rejects, but every
    // complete-record prefix after metadata is a valid unsealed stream.
    for cut in 0..lines.len() {
        let prefix = if cut == 0 {
            String::new()
        } else {
            stream(&lines[..cut])
        };
        push_case(
            &mut cases,
            format!("truncation/prefix-before-record-{cut:03}"),
            prefix,
            if cut == 0 {
                "malformed"
            } else {
                "published-unsealed"
            },
        );
    }

    // Removing the closing byte from each actual record is syntactic
    // truncation and must reject at that record rather than panic.
    for (index, line) in lines.iter().enumerate() {
        let mut truncated = line.clone();
        assert_eq!(truncated.pop(), Some('}'));
        push_case(
            &mut cases,
            format!("truncation/record-body-{index:03}"),
            replace_fixture_line(index, truncated),
            "json",
        );
    }

    // Every official record rejects an additional top-level field.
    for (index, line) in lines.iter().enumerate() {
        let mut value: Value = serde_json::from_str(line).expect("official record parses");
        value
            .as_object_mut()
            .expect("official record is an object")
            .insert("unexpected".to_owned(), Value::Bool(true));
        push_case(
            &mut cases,
            format!("unknown-field/top-level-{index:03}"),
            replace_fixture_line(
                index,
                serde_json::to_string(&value).expect("serialize unknown-field mutation"),
            ),
            "malformed",
        );
    }

    let nested_unknowns = [
        (
            "metadata",
            stream(&[r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"test","version":"4.30.0"},"unexpected":true}}"#.to_owned()]),
        ),
        (
            "name",
            stream(&[
                metadata().to_owned(),
                r#"{"in":1,"str":{"pre":0,"str":"x","unexpected":true}}"#.to_owned(),
            ]),
        ),
        (
            "expression",
            stream(&[
                metadata().to_owned(),
                r#"{"ie":0,"bvar":0}"#.to_owned(),
                r#"{"ie":1,"app":{"fn":0,"arg":0,"unexpected":true}}"#.to_owned(),
            ]),
        ),
        (
            "declaration",
            stream(&[
                metadata().to_owned(),
                r#"{"in":1,"str":{"pre":0,"str":"A"}}"#.to_owned(),
                r#"{"ie":0,"sort":0}"#.to_owned(),
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false,"unexpected":true}}"#.to_owned(),
            ]),
        ),
    ];
    for (id, mutation) in nested_unknowns {
        push_case(
            &mut cases,
            format!("unknown-field/nested-{id}"),
            mutation,
            "malformed",
        );
    }

    for (kind, key) in [("name", "in"), ("level", "il"), ("expression", "ie")] {
        let index = lines
            .iter()
            .position(|line| {
                serde_json::from_str::<Value>(line)
                    .ok()
                    .and_then(|value| value.get(key).cloned())
                    .is_some()
            })
            .expect("fixture contains dense wire ID kind");
        push_case(
            &mut cases,
            format!("duplicate-id/{kind}"),
            insert_fixture_line(index + 1, lines[index].clone()),
            "malformed",
        );
    }

    let topology = [
        (
            "forward/name",
            r#"{"in":1,"str":{"pre":2,"str":"x"}}"#,
            "malformed",
        ),
        (
            "cycle/name-self",
            r#"{"in":1,"str":{"pre":1,"str":"x"}}"#,
            "malformed",
        ),
        ("forward/level", r#"{"il":1,"succ":2}"#, "malformed"),
        ("cycle/level-self", r#"{"il":1,"succ":1}"#, "malformed"),
        (
            "forward/expression",
            r#"{"ie":0,"app":{"fn":1,"arg":1}}"#,
            "malformed",
        ),
        (
            "cycle/expression-self",
            r#"{"ie":0,"app":{"fn":0,"arg":0}}"#,
            "malformed",
        ),
    ];
    for (id, record, expected) in topology {
        push_case(
            &mut cases,
            id,
            stream(&[metadata().to_owned(), record.to_owned()]),
            expected,
        );
    }

    let mut declaration_cycle = lines.clone();
    let theorem_index = declaration_cycle.len() - 1;
    declaration_cycle.insert(
        theorem_index,
        r#"{"ie":43,"const":{"name":13,"us":[]}}"#.to_owned(),
    );
    declaration_cycle[theorem_index + 1] =
        declaration_cycle[theorem_index + 1].replace(r#""value":42"#, r#""value":43"#);
    push_case(
        &mut cases,
        "cycle/declaration-self",
        stream(&declaration_cycle),
        "kernel",
    );

    push_case(
        &mut cases,
        "deep-json/bounded-16",
        mdata_stream(16),
        "published",
    );
    push_case(
        &mut cases,
        "deep-json/excessive-256",
        mdata_stream(256),
        "json",
    );

    push_case(
        &mut cases,
        "unicode/raw-name",
        unicode_stream(r#"{"in":1,"str":{"pre":0,"str":"λ😀"}}"#),
        "published",
    );
    push_case(
        &mut cases,
        "unicode/escaped-name",
        unicode_stream(r#"{"in":1,"str":{"pre":0,"str":"\u03bb\ud83d\ude00"}}"#),
        "published",
    );
    push_case(
        &mut cases,
        "unicode/lone-surrogate",
        stream(&[
            metadata().to_owned(),
            r#"{"in":1,"str":{"pre":0,"str":"\ud800"}}"#.to_owned(),
        ]),
        "json",
    );
    push_case(
        &mut cases,
        "unicode/non-ascii-nat-digits",
        stream(&[metadata().to_owned(), r#"{"ie":0,"natVal":"١"}"#.to_owned()]),
        "malformed",
    );

    let integers = [
        (
            "negative-id",
            r#"{"in":-1,"str":{"pre":0,"str":"x"}}"#,
            "malformed",
        ),
        (
            "floating-id",
            r#"{"in":1.0,"str":{"pre":0,"str":"x"}}"#,
            "malformed",
        ),
        (
            "u64-overflow",
            r#"{"in":18446744073709551616,"str":{"pre":0,"str":"x"}}"#,
            "malformed",
        ),
        (
            "u64-max-dense-mismatch",
            r#"{"in":18446744073709551615,"str":{"pre":0,"str":"x"}}"#,
            "malformed",
        ),
    ];
    for (id, record, expected) in integers {
        push_case(
            &mut cases,
            format!("integer/{id}"),
            stream(&[metadata().to_owned(), record.to_owned()]),
            expected,
        );
    }
    push_case(
        &mut cases,
        "integer/projection-u32-overflow",
        stream(&[
            metadata().to_owned(),
            r#"{"in":1,"str":{"pre":0,"str":"T"}}"#.to_owned(),
            r#"{"ie":0,"bvar":0}"#.to_owned(),
            r#"{"ie":1,"proj":{"typeName":1,"idx":4294967296,"struct":0}}"#.to_owned(),
        ]),
        "malformed",
    );

    push_case(
        &mut cases,
        "version/unsupported-format",
        metadata().replace(
            "\"format\":{\"version\":\"3.1.0\"}",
            "\"format\":{\"version\":\"4.0.0\"}",
        ),
        "unsupported:format-version",
    );
    push_case(
        &mut cases,
        "version/format-number",
        metadata().replace(
            "\"format\":{\"version\":\"3.1.0\"}",
            "\"format\":{\"version\":31}",
        ),
        "malformed",
    );
    let mut missing_version: Value = serde_json::from_str(metadata()).expect("metadata parses");
    missing_version["meta"]["format"]
        .as_object_mut()
        .expect("format object")
        .remove("version");
    push_case(
        &mut cases,
        "version/missing-format",
        serde_json::to_string(&missing_version).expect("serialize missing version"),
        "malformed",
    );
    push_case(
        &mut cases,
        "version/wrong-exporter",
        metadata().replace("\"name\":\"lean4export\"", "\"name\":\"other\""),
        "malformed",
    );

    push_case(
        &mut cases,
        "discriminant/unknown",
        stream(&[metadata().to_owned(), r#"{"mystery":{}}"#.to_owned()]),
        "malformed",
    );
    push_case(
        &mut cases,
        "discriminant/multiple-expression-kinds",
        stream(&[
            metadata().to_owned(),
            r#"{"ie":0,"bvar":0,"sort":0}"#.to_owned(),
        ]),
        "malformed",
    );

    cases
}

fn observed_class(stream: &str) -> String {
    match import_ndjson(Cursor::new(stream.as_bytes()), ImportLimits::default()) {
        Ok(_) => "published".to_owned(),
        Err(ImportError::Io(_)) => "io".to_owned(),
        Err(ImportError::LineLimit { .. }) => "line-limit".to_owned(),
        Err(ImportError::RecordLimit { .. }) => "record-limit".to_owned(),
        Err(ImportError::Json { .. }) => "json".to_owned(),
        Err(ImportError::Malformed { .. }) => "malformed".to_owned(),
        Err(ImportError::Unsupported { code, .. }) => format!("unsupported:{code}"),
        Err(ImportError::Kernel { .. }) => "kernel".to_owned(),
    }
}

fn run_corpus(cases: &[MutationCase]) -> (String, BTreeMap<String, usize>) {
    let mut summary = String::new();
    let mut counts = BTreeMap::new();
    for case in cases {
        let observed = observed_class(&case.stream);
        let stable = if case.expected == "published-unsealed" && observed == "published" {
            "published-unsealed"
        } else {
            observed.as_str()
        };
        assert_eq!(
            stable, case.expected,
            "mutation {} produced the wrong stable class",
            case.id
        );
        summary.push_str(&case.id);
        summary.push('|');
        summary.push_str(stable);
        summary.push('\n');
        *counts.entry(stable.to_owned()).or_insert(0) += 1;
    }
    (summary, counts)
}

#[test]
fn generated_wire_mutation_corpus_is_complete_stable_and_deterministic() {
    let first = build_corpus();
    let second = build_corpus();
    assert_eq!(first, second, "corpus generation must be deterministic");

    let unique: BTreeSet<_> = first.iter().map(|case| case.id.as_str()).collect();
    assert_eq!(unique.len(), first.len(), "mutation IDs must be unique");

    let (first_summary, first_counts) = run_corpus(&first);
    let (second_summary, second_counts) = run_corpus(&second);
    assert_eq!(first_summary, second_summary);
    assert_eq!(first_counts, second_counts);

    eprintln!(
        "LEAN_IMPORT_MUTATIONS|cases={}|{}",
        first.len(),
        first_counts
            .iter()
            .map(|(class, count)| format!("{class}={count}"))
            .collect::<Vec<_>>()
            .join("|")
    );
    assert_eq!(first.len(), 226, "the generated corpus lost population");
    assert_eq!(
        first_counts,
        BTreeMap::from([
            ("json".to_owned(), 67),
            ("kernel".to_owned(), 1),
            ("malformed".to_owned(), 90),
            ("published".to_owned(), 3),
            ("published-unsealed".to_owned(), 64),
            ("unsupported:format-version".to_owned(), 1),
        ])
    );
}

#[test]
fn raw_and_escaped_unicode_names_publish_the_same_checked_declaration() {
    let raw = import_ndjson(
        Cursor::new(unicode_stream(r#"{"in":1,"str":{"pre":0,"str":"λ😀"}}"#).into_bytes()),
        ImportLimits::default(),
    )
    .expect("raw Unicode fixture publishes");
    let escaped = import_ndjson(
        Cursor::new(
            unicode_stream(r#"{"in":1,"str":{"pre":0,"str":"\u03bb\ud83d\ude00"}}"#).into_bytes(),
        ),
        ImportLimits::default(),
    )
    .expect("escaped Unicode fixture publishes");

    let raw_names: Vec<_> = raw
        .kernel()
        .environment()
        .iter()
        .map(|(_, declaration)| raw.kernel().display_name(declaration.name()).to_string())
        .collect();
    let escaped_names: Vec<_> = escaped
        .kernel()
        .environment()
        .iter()
        .map(|(_, declaration)| {
            escaped
                .kernel()
                .display_name(declaration.name())
                .to_string()
        })
        .collect();
    assert_eq!(raw_names, ["λ😀"]);
    assert_eq!(escaped_names, raw_names);
}

#[test]
fn official_record_boundary_prefixes_are_explicitly_unsealed_not_full_credit() {
    let lines = fixture_lines();
    let mut published_prefixes = 0usize;
    for cut in 1..lines.len() {
        let completed = import_ndjson(
            Cursor::new(stream(&lines[..cut]).into_bytes()),
            ImportLimits::default(),
        )
        .expect("backward-only complete-record prefix is a valid unsealed stream");
        assert!(
            completed.report().declaration_records <= 5,
            "a prefix cannot contain more declarations than the full fixture"
        );
        published_prefixes += 1;
    }
    assert_eq!(published_prefixes, lines.len() - 1);

    let full = import_ndjson(Cursor::new(FIXTURE.as_bytes()), ImportLimits::default())
        .expect("full exact fixture publishes");
    assert_eq!(full.report().declaration_records, 5);
    assert_eq!(full.report().admitted_declarations, 8);
}
