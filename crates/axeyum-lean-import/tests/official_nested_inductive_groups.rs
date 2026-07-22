//! Official TL2.14 nested groups: exact import and fail-closed wire comparison.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, ImportReport, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, KernelError, NameId};
use serde_json::{Value, json};

const CONTROL: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson");
const CONSTRUCT: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-nested.ndjson");
const AUXILIARY: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nested-aux-computation.ndjson");
const INDEXED: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nested-indexed-computation.ndjson");
const REPEATED: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-nested-repeated-container-computation.ndjson"
);
const WELL_FOUNDED: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-well-founded.ndjson"
);

const AUXILIARY_GROUP_LINE: usize = 269;
const AUXILIARY_FINAL_LINE: usize = 642;
const AUXILIARY_RECURSOR_NAME: u64 = 35;
const MAIN_RECURSOR_NAME: u64 = 39;
const FOREIGN_RECURSOR_NAME: u64 = 30;

#[derive(Clone, Copy)]
struct OfficialCase {
    label: &'static str,
    fixture: &'static str,
    counts: (usize, usize, usize, usize, usize),
    namespace: &'static str,
    family: &'static str,
    container: &'static str,
    source_fields: u16,
    auxiliary_indices: u16,
    auxiliary_fields: &'static [u16],
    required: &'static [&'static str],
}

const CASES: &[OfficialCase] = &[
    OfficialCase {
        label: "construct-matrix-nested",
        fixture: CONSTRUCT,
        counts: (70, 6, 322, 10, 22),
        namespace: "AxeyumConstructMatrix",
        family: "Rose",
        container: "NestList",
        source_fields: 2,
        auxiliary_indices: 0,
        auxiliary_fields: &[0, 2],
        required: &[
            "AxeyumConstructMatrix.Rose",
            "AxeyumConstructMatrix.Rose.node",
            "AxeyumConstructMatrix.Rose.rec",
            "AxeyumConstructMatrix.Rose.rec_1",
            "AxeyumConstructMatrix.nestedWitness",
        ],
    },
    OfficialCase {
        label: "auxiliary-recursion-computation",
        fixture: AUXILIARY,
        counts: (122, 8, 494, 17, 34),
        namespace: "AxeyumNestedInductiveComputation",
        family: "Rose",
        container: "NestList",
        source_fields: 2,
        auxiliary_indices: 0,
        auxiliary_fields: &[0, 2],
        required: &[
            "AxeyumNestedInductiveComputation.Rose.rec",
            "AxeyumNestedInductiveComputation.Rose.rec_1",
            "AxeyumNestedInductiveComputation.roseAuxiliaryRecursorComputes",
        ],
    },
    OfficialCase {
        label: "indexed-container-computation",
        fixture: INDEXED,
        counts: (134, 8, 554, 17, 34),
        namespace: "AxeyumNestedInductiveComputation",
        family: "IndexedRose",
        container: "NestVec",
        source_fields: 3,
        auxiliary_indices: 1,
        auxiliary_fields: &[0, 3],
        required: &[
            "AxeyumNestedInductiveComputation.IndexedRose.rec",
            "AxeyumNestedInductiveComputation.IndexedRose.rec_1",
            "AxeyumNestedInductiveComputation.indexedAuxiliaryRecursorComputes",
        ],
    },
    OfficialCase {
        label: "repeated-container-computation",
        fixture: REPEATED,
        counts: (122, 8, 518, 17, 34),
        namespace: "AxeyumNestedInductiveComputation",
        family: "RepeatRose",
        container: "NestList",
        source_fields: 3,
        auxiliary_indices: 0,
        auxiliary_fields: &[0, 2],
        required: &[
            "AxeyumNestedInductiveComputation.RepeatRose.rec",
            "AxeyumNestedInductiveComputation.RepeatRose.rec_1",
            "AxeyumNestedInductiveComputation.repeatedContainerReusesAuxiliaryRecursor",
        ],
    },
];

fn qualified(kernel: &mut Kernel, components: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for component in components {
        name = kernel.name_str(name, *component);
    }
    name
}

fn assert_control() {
    let completed = import_ndjson(Cursor::new(CONTROL.as_bytes()), ImportLimits::default())
        .expect("direct-recursive control must admit before every rejection");
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
}

fn assert_report(report: &ImportReport, case: OfficialCase) {
    assert_eq!(
        (
            report.names,
            report.levels,
            report.expressions,
            report.declaration_records,
            report.admitted_declarations,
        ),
        case.counts,
        "{}",
        case.label
    );
    assert!(report.axioms.is_empty(), "{}", case.label);
    assert_eq!(
        report.declaration_identities.len(),
        report.admitted_declarations,
        "{}",
        case.label
    );
    for required in case.required {
        assert!(
            report
                .declaration_identities
                .iter()
                .any(|identity| identity.name == *required),
            "{}: missing declaration identity {required}",
            case.label
        );
    }
}

fn assert_recursor(
    kernel: &mut Kernel,
    name_components: &[&str],
    expected_counts: (u16, u16, u16, u16),
    expected_rules: &[(&str, u16)],
) {
    let name = qualified(kernel, name_components);
    let declaration = kernel
        .environment()
        .get(name)
        .unwrap_or_else(|| panic!("missing recursor {}", name_components.join(".")))
        .clone();
    let Declaration::Recursor {
        ty,
        rec_rules,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ..
    } = declaration
    else {
        panic!("{} is not a recursor", name_components.join("."));
    };
    assert_eq!(
        (num_params, num_indices, num_motives, num_minors),
        expected_counts
    );
    assert_eq!(rec_rules.len(), expected_rules.len());
    for (rule, (expected_ctor, expected_fields)) in rec_rules.iter().zip(expected_rules) {
        assert_eq!(
            kernel.display_name(rule.ctor_name).to_string(),
            *expected_ctor
        );
        assert_eq!(rule.num_fields, *expected_fields);
    }
    kernel.infer(ty).expect("public recursor type must infer");
}

fn assert_nested_surface(kernel: &mut Kernel, case: OfficialCase) {
    let main_name = format!("{}.{}.node", case.namespace, case.family);
    let nil_name = format!("{}.{}.nil", case.namespace, case.container);
    let cons_name = format!("{}.{}.cons", case.namespace, case.container);
    assert_recursor(
        kernel,
        &[case.namespace, case.family, "rec"],
        (1, 0, 2, 3),
        &[(main_name.as_str(), case.source_fields)],
    );
    assert_recursor(
        kernel,
        &[case.namespace, case.family, "rec_1"],
        (1, case.auxiliary_indices, 2, 3),
        &[
            (nil_name.as_str(), case.auxiliary_fields[0]),
            (cons_name.as_str(), case.auxiliary_fields[1]),
        ],
    );
}

fn mutate_record(fixture: &str, line: usize, mutate: impl FnOnce(&mut Value)) -> String {
    let mut records = fixture.lines().map(str::to_owned).collect::<Vec<_>>();
    let record = records
        .get_mut(line - 1)
        .unwrap_or_else(|| panic!("fixture has no line {line}"));
    let mut value: Value = serde_json::from_str(record).expect("fixture record must be JSON");
    mutate(&mut value);
    *record = serde_json::to_string(&value).unwrap();
    records.join("\n") + "\n"
}

fn mutate_group(fixture: &str, line: usize, mutate: impl FnOnce(&mut Value)) -> String {
    mutate_record(fixture, line, |record| {
        mutate(
            record
                .get_mut("inductive")
                .unwrap_or_else(|| panic!("line {line} is not an inductive record")),
        );
    })
}

fn recursor(group: &mut Value, name: u64) -> &mut Value {
    group["recs"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|recursor| recursor["name"].as_u64() == Some(name))
        .unwrap_or_else(|| panic!("group has no recursor name index {name}"))
}

fn assert_malformed(fixture: &str, line: usize, message: &str) {
    assert_control();
    let error = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .expect_err("malformed nested stream published CompletedImport");
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

fn assert_unsupported(fixture: &str, line: usize, code: &str) {
    assert_control();
    let error = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .expect_err("unsupported nested stream published CompletedImport");
    assert!(
        matches!(
            &error,
            ImportError::Unsupported {
                line: actual_line,
                code: actual_code,
            } if *actual_line == line && *actual_code == code
        ),
        "unexpected mutation outcome: {error:?}"
    );
}

#[test]
fn official_nested_streams_import_twice_with_exact_public_declarations() {
    for &case in CASES {
        let mut reports = Vec::new();
        for _ in 0..2 {
            let completed = import_ndjson(
                Cursor::new(case.fixture.as_bytes()),
                ImportLimits::default(),
            )
            .unwrap_or_else(|error| panic!("{} failed: {error:?}", case.label));
            let (mut kernel, report) = completed.into_parts();
            assert_report(&report, case);
            assert_nested_surface(&mut kernel, case);
            reports.push(report);
        }
        assert_eq!(reports[0], reports[1], "{}", case.label);
    }
}

#[test]
fn recursor_array_order_is_non_authoritative_and_well_founded_is_retained() {
    for &(case, line) in &[
        (CASES[0], 248),
        (CASES[1], 269),
        (CASES[2], 320),
        (CASES[3], 289),
    ] {
        let original = import_ndjson(
            Cursor::new(case.fixture.as_bytes()),
            ImportLimits::default(),
        )
        .unwrap();
        let swapped = mutate_group(case.fixture, line, |group| {
            group["recs"].as_array_mut().unwrap().reverse();
        });
        let swapped = import_ndjson(Cursor::new(swapped.as_bytes()), ImportLimits::default())
            .expect("recursor array order must not authorize semantics");
        assert_eq!(original.report(), swapped.report(), "{}", case.label);
    }

    let mut reports = Vec::new();
    for _ in 0..2 {
        let completed = import_ndjson(
            Cursor::new(WELL_FOUNDED.as_bytes()),
            ImportLimits::default(),
        )
        .expect("well-founded control must remain admitted");
        assert_eq!(
            (
                completed.report().names,
                completed.report().levels,
                completed.report().expressions,
                completed.report().declaration_records,
                completed.report().admitted_declarations,
                completed.report().axioms.len(),
            ),
            (160, 5, 731, 23, 35, 0)
        );
        reports.push(completed.report().clone());
    }
    assert_eq!(reports[0], reports[1]);
}

#[test]
fn derived_count_and_name_mutations_reject_at_the_registered_layer() {
    let zero_count = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        group["types"][0]["numNested"] = json!(0);
    });
    assert_malformed(
        &zero_count,
        AUXILIARY_GROUP_LINE,
        "generated/exported numNested differs",
    );

    let two_count = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        group["types"][0]["numNested"] = json!(2);
        let extra = group["recs"][0].clone();
        group["recs"].as_array_mut().unwrap().push(extra);
    });
    assert_malformed(
        &two_count,
        AUXILIARY_GROUP_LINE,
        "generated/exported numNested differs",
    );

    let missing_auxiliary = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        let recursors = group["recs"].as_array_mut().unwrap();
        let index = recursors
            .iter()
            .position(|recursor| recursor["name"].as_u64() == Some(AUXILIARY_RECURSOR_NAME))
            .expect("fixture must contain rec_1");
        recursors.remove(index);
    });
    assert_malformed(
        &missing_auxiliary,
        AUXILIARY_GROUP_LINE,
        "nested inductive recursor count differs from numNested",
    );

    let extra_recursor = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        let extra = group["recs"][0].clone();
        group["recs"].as_array_mut().unwrap().push(extra);
    });
    assert_malformed(
        &extra_recursor,
        AUXILIARY_GROUP_LINE,
        "nested inductive recursor count differs from numNested",
    );

    let duplicate_name = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, MAIN_RECURSOR_NAME)["name"] = json!(AUXILIARY_RECURSOR_NAME);
    });
    assert_malformed(
        &duplicate_name,
        AUXILIARY_GROUP_LINE,
        "inductive group repeats a recursor record",
    );

    let foreign_name = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, MAIN_RECURSOR_NAME)["name"] = json!(FOREIGN_RECURSOR_NAME);
    });
    assert_malformed(
        &foreign_name,
        AUXILIARY_GROUP_LINE,
        "exported recursor name does not belong to kernel-derived group",
    );
}

#[test]
fn recursor_metadata_mutations_reject_exactly() {
    let wrong_all = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["all"] = json!([]);
    });
    assert_malformed(
        &wrong_all,
        AUXILIARY_GROUP_LINE,
        "inductive recursor all list differs from ordered group",
    );

    let wrong_type = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["type"] = json!(0);
    });
    assert_malformed(
        &wrong_type,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor types are not definitionally equal",
    );

    for (field, value, message) in [
        (
            "numParams",
            0,
            "generated/exported recursor numParams differs",
        ),
        (
            "numMotives",
            1,
            "generated/exported recursor numMotives differs",
        ),
        (
            "numMinors",
            2,
            "generated/exported recursor numMinors differs",
        ),
    ] {
        let mutated = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
            recursor(group, AUXILIARY_RECURSOR_NAME)[field] = json!(value);
        });
        assert_malformed(&mutated, AUXILIARY_GROUP_LINE, message);
    }

    for name in [AUXILIARY_RECURSOR_NAME, MAIN_RECURSOR_NAME] {
        let wrong_indices = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
            recursor(group, name)["numIndices"] = json!(1);
        });
        assert_malformed(
            &wrong_indices,
            AUXILIARY_GROUP_LINE,
            "generated/exported recursor numIndices differs",
        );
    }

    let wrong_uparams = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["levelParams"]
            .as_array_mut()
            .unwrap()
            .pop();
    });
    assert_malformed(
        &wrong_uparams,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor universe-parameter arity differs",
    );
}

#[test]
fn recursor_rule_mutations_reject_exactly() {
    let missing_rule = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["rules"]
            .as_array_mut()
            .unwrap()
            .pop();
    });
    assert_malformed(
        &missing_rule,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor rule count differs",
    );

    let extra_rule = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        let recursor = recursor(group, AUXILIARY_RECURSOR_NAME);
        let extra = recursor["rules"][0].clone();
        recursor["rules"].as_array_mut().unwrap().push(extra);
    });
    assert_malformed(
        &extra_rule,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor rule count differs",
    );

    let wrong_ctor = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["rules"][0]["ctor"] = json!(34);
    });
    assert_malformed(
        &wrong_ctor,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor rule differs",
    );

    let wrong_nfields = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["rules"][1]["nfields"] = json!(1);
    });
    assert_malformed(
        &wrong_nfields,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor rule differs",
    );

    let wrong_rhs = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["rules"][0]["rhs"] = json!(0);
    });
    assert_malformed(
        &wrong_rhs,
        AUXILIARY_GROUP_LINE,
        "generated/exported recursor rule differs",
    );
}

#[test]
fn unsafe_k_and_late_publication_mutations_never_complete() {
    let unsafe_recursor = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
        recursor(group, AUXILIARY_RECURSOR_NAME)["isUnsafe"] = json!(true);
    });
    assert_unsupported(&unsafe_recursor, AUXILIARY_GROUP_LINE, "declaration-unsafe");

    for name in [AUXILIARY_RECURSOR_NAME, MAIN_RECURSOR_NAME] {
        let k_target = mutate_group(AUXILIARY, AUXILIARY_GROUP_LINE, |group| {
            recursor(group, name)["k"] = json!(true);
        });
        assert_malformed(
            &k_target,
            AUXILIARY_GROUP_LINE,
            "nested recursor may not be a K target",
        );
    }

    let late_duplicate = mutate_record(AUXILIARY, AUXILIARY_FINAL_LINE, |record| {
        record["thm"]["name"] = json!(1);
    });
    assert_control();
    let error = import_ndjson(
        Cursor::new(late_duplicate.as_bytes()),
        ImportLimits::default(),
    )
    .expect_err("late duplicate declaration published CompletedImport");
    assert!(
        matches!(
            error,
            ImportError::Kernel {
                line: AUXILIARY_FINAL_LINE,
                ref declaration,
                source: KernelError::DeclarationExists { .. },
            } if declaration == "Eq"
        ),
        "unexpected late-publication outcome: {error:?}"
    );
}
