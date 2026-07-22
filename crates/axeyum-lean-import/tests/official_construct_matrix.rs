//! Frozen current-product outcomes for the official Lean construct matrix.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use serde_json::{Value, json};

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
struct ExpectedOutcome {
    counts: (usize, usize, usize, usize, usize),
    required_names: &'static [&'static str],
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

fn assert_outcome(case_id: &str, fixture: &str, expected: ExpectedOutcome) {
    let completed = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .unwrap_or_else(|error| panic!("{case_id}: unexpected typed outcome: {error:?}"));
    let report = completed.report();
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        expected.counts,
        "{case_id}"
    );
    for required in expected.required_names {
        assert!(
            report
                .declaration_identities
                .iter()
                .any(|identity| identity.name == *required),
            "{case_id}: missing completed declaration {required}"
        );
    }
}

fn mutate_inductive_record(fixture: &str, line: usize, mutate: impl FnOnce(&mut Value)) -> String {
    let mut records: Vec<String> = fixture.lines().map(str::to_owned).collect();
    let record = records
        .get_mut(line - 1)
        .unwrap_or_else(|| panic!("fixture has no line {line}"));
    let mut value: Value = serde_json::from_str(record).unwrap();
    mutate(
        value
            .get_mut("inductive")
            .unwrap_or_else(|| panic!("line {line} is not an inductive record")),
    );
    *record = serde_json::to_string(&value).unwrap();
    records.join("\n") + "\n"
}

fn assert_unsupported(fixture: &str, line: usize, code: &'static str) {
    let error = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .expect_err("synthetic unsupported mutation published CompletedImport");
    assert!(
        matches!(
            &error,
            ImportError::Unsupported {
                line: actual_line,
                code: actual_code,
            } if (*actual_line, *actual_code) == (line, code)
        ),
        "unexpected mutation outcome: {error:?}"
    );
}

fn assert_malformed(fixture: &str, line: usize, message: &'static str) {
    let error = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .expect_err("synthetic malformed mutation published CompletedImport");
    assert!(
        matches!(
            &error,
            ImportError::Malformed {
                line: actual_line,
                message: actual_message,
            } if *actual_line == line && actual_message == message
        ),
        "unexpected mutation outcome: {error:?}"
    );
}

#[test]
fn frozen_matrix_outcomes_repeat_with_a_control_before_every_decline() {
    let cases = [
        (
            "recursive-indexed",
            RECURSIVE_INDEXED,
            ExpectedOutcome {
                counts: (34, 4, 132, 4, 12),
                required_names: &[
                    "AxeyumConstructMatrix.MiniVector",
                    "AxeyumConstructMatrix.MiniVector.rec",
                    "AxeyumConstructMatrix.recursiveIndexedWitness",
                ],
            },
        ),
        (
            "reflexive-higher-order",
            REFLEXIVE,
            ExpectedOutcome {
                counts: (47, 3, 139, 6, 11),
                required_names: &[
                    "AxeyumConstructMatrix.MiniAcc",
                    "AxeyumConstructMatrix.MiniAcc.rec",
                    "AxeyumConstructMatrix.reflexiveWitness",
                ],
            },
        ),
        (
            "mutual",
            MUTUAL,
            ExpectedOutcome {
                counts: (75, 4, 305, 10, 26),
                required_names: &[
                    "AxeyumConstructMatrix.EvenTree",
                    "AxeyumConstructMatrix.OddTree",
                    "AxeyumConstructMatrix.EvenTree.rec",
                    "AxeyumConstructMatrix.OddTree.rec",
                    "AxeyumConstructMatrix.mutualWitness",
                ],
            },
        ),
        (
            "nested",
            NESTED,
            ExpectedOutcome {
                counts: (70, 6, 322, 10, 22),
                required_names: &[
                    "AxeyumConstructMatrix.Rose",
                    "AxeyumConstructMatrix.Rose.node",
                    "AxeyumConstructMatrix.Rose.rec",
                    "AxeyumConstructMatrix.Rose.rec_1",
                    "AxeyumConstructMatrix.nestedWitness",
                ],
            },
        ),
        (
            "well-founded",
            WELL_FOUNDED,
            ExpectedOutcome {
                counts: (160, 5, 731, 23, 35),
                required_names: &[
                    "Acc.rec",
                    "AxeyumConstructMatrix.atomEmptyWellFounded",
                    "AxeyumConstructMatrix.wellFoundedWitness",
                ],
            },
        ),
    ];

    for _ in 0..2 {
        for (case_id, fixture, expected) in cases {
            assert_control();
            assert_outcome(case_id, fixture, expected);
        }
    }
}

#[test]
fn reflexive_metadata_is_descriptive_while_boundaries_remain_fail_closed() {
    let vector_flipped = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["types"][0]["isReflexive"] = json!(true);
    });
    let vector = import_ndjson(
        Cursor::new(vector_flipped.as_bytes()),
        ImportLimits::default(),
    )
    .expect("isReflexive=true must not grant or deny structurally valid support");
    assert_eq!(vector.report().admitted_declarations, 12);

    let acc_flipped = mutate_inductive_record(REFLEXIVE, 117, |group| {
        group["types"][0]["isReflexive"] = json!(false);
    });
    let acc = import_ndjson(Cursor::new(acc_flipped.as_bytes()), ImportLimits::default())
        .expect("isReflexive=false must not grant or deny structurally valid support");
    assert_eq!(acc.report().admitted_declarations, 11);

    let nested = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["types"][0]["numNested"] = json!(1);
    });
    assert_malformed(&nested, 148, "generated/exported numNested differs");

    let unsafe_group = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["types"][0]["isUnsafe"] = json!(true);
    });
    assert_unsupported(&unsafe_group, 148, "declaration-unsafe");

    let duplicate_group = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        let duplicate_type = group["types"][0].clone();
        let duplicate_recursor = group["recs"][0].clone();
        group["types"].as_array_mut().unwrap().push(duplicate_type);
        group["recs"]
            .as_array_mut()
            .unwrap()
            .push(duplicate_recursor);
    });
    assert_malformed(
        &duplicate_group,
        148,
        "inductive group repeats a family name",
    );
}

#[test]
fn nested_preflight_preserves_ordinary_singleton_recursor_validation() {
    for _ in 0..2 {
        assert_control();
        assert_outcome(
            "nested",
            NESTED,
            ExpectedOutcome {
                counts: (70, 6, 322, 10, 22),
                required_names: &[
                    "AxeyumConstructMatrix.Rose.rec",
                    "AxeyumConstructMatrix.Rose.rec_1",
                ],
            },
        );
    }

    let missing_auxiliary = mutate_inductive_record(NESTED, 248, |group| {
        let recursors = group["recs"].as_array_mut().unwrap();
        let auxiliary_index = recursors
            .iter()
            .position(|recursor| recursor["name"].as_u64() == Some(33))
            .expect("nested construct fixture must contain Rose.rec_1");
        recursors.remove(auxiliary_index);
    });
    assert_malformed(
        &missing_auxiliary,
        248,
        "nested inductive recursor count differs from numNested",
    );

    let extra_auxiliary = mutate_inductive_record(NESTED, 248, |group| {
        let duplicate = group["recs"][0].clone();
        group["recs"].as_array_mut().unwrap().push(duplicate);
    });
    assert_malformed(
        &extra_auxiliary,
        248,
        "nested inductive recursor count differs from numNested",
    );

    let missing_main = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["recs"].as_array_mut().unwrap().clear();
    });
    assert_malformed(
        &missing_main,
        148,
        "single-family inductive must export one recursor",
    );

    let extra_main = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        let duplicate = group["recs"][0].clone();
        group["recs"].as_array_mut().unwrap().push(duplicate);
    });
    assert_malformed(
        &extra_main,
        148,
        "single-family inductive must export one recursor",
    );

    let inconsistent_mutual_count = mutate_inductive_record(MUTUAL, 233, |group| {
        group["types"][0]["numNested"] = json!(1);
    });
    assert_malformed(
        &inconsistent_mutual_count,
        233,
        "mutual family numNested differs",
    );

    let nested_mutual_shape = mutate_inductive_record(MUTUAL, 233, |group| {
        group["types"][0]["numNested"] = json!(1);
        group["types"][1]["numNested"] = json!(1);
        let auxiliary = group["recs"][0].clone();
        group["recs"].as_array_mut().unwrap().push(auxiliary);
    });
    assert_malformed(
        &nested_mutual_shape,
        233,
        "generated/exported numNested differs",
    );
}

#[test]
fn late_recursor_mutations_never_publish_a_completed_import() {
    let wrong_type = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["recs"][0]["type"] = json!(0);
    });
    assert_malformed(
        &wrong_type,
        148,
        "generated/exported recursor types are not definitionally equal",
    );

    let wrong_minor_count = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["recs"][0]["numMinors"] = json!(3);
    });
    assert_malformed(
        &wrong_minor_count,
        148,
        "generated/exported recursor numMinors differs",
    );

    let wrong_rule = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["recs"][0]["rules"][1]["rhs"] = json!(0);
    });
    assert_malformed(&wrong_rule, 148, "generated/exported recursor rule differs");

    let wrong_nfields = mutate_inductive_record(RECURSIVE_INDEXED, 148, |group| {
        group["recs"][0]["rules"][1]["nfields"] = json!(4);
    });
    assert_malformed(
        &wrong_nfields,
        148,
        "generated/exported recursor rule differs",
    );
}
