//! Official TL2.13 mutual groups: exact import, computation, and fail-closed wire checks.

use std::io::Cursor;

use axeyum_lean_import::{ImportError, ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::{Value, json};

const CONSTRUCT: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson");
const CROSS: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-mutual-cross-computation.ndjson");
const INDEXED: &str =
    include_str!("../../../docs/plan/fixtures/lean4export-v4.30-mutual-indexed-computation.ndjson");

fn qualified(kernel: &mut Kernel, components: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for component in components {
        name = kernel.name_str(name, *component);
    }
    name
}

fn unfold_apps(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

fn normalize_application_spine(kernel: &mut Kernel, expression: ExprId) -> ExprId {
    let expression = kernel.whnf(expression);
    let ExprNode::App(function, argument) = kernel.expr_node(expression).clone() else {
        return expression;
    };
    let function = normalize_application_spine(kernel, function);
    let argument = normalize_application_spine(kernel, argument);
    kernel.app(function, argument)
}

fn assert_computation_theorem(kernel: &mut Kernel, theorem: &str, expected: ExprId) {
    let theorem_name = qualified(kernel, &["AxeyumMutualInductiveComputation", theorem]);
    let declaration = kernel
        .environment()
        .get(theorem_name)
        .unwrap_or_else(|| panic!("missing theorem {theorem}"))
        .clone();
    let Declaration::Theorem { ty, value, .. } = declaration else {
        panic!("selected computation result is not a theorem");
    };
    let inferred = kernel.infer(value).expect("computation proof must infer");
    assert!(kernel.def_eq(inferred, ty));

    let (head, arguments) = unfold_apps(kernel, ty);
    let ExprNode::Const(eq_name, _) = kernel.expr_node(head) else {
        panic!("computation theorem type is not headed by Eq");
    };
    assert_eq!(kernel.display_name(*eq_name).to_string(), "Eq");
    assert_eq!(arguments.len(), 3, "Eq must have type, lhs, and rhs");
    let lhs = arguments[1];
    let rhs = arguments[2];
    assert!(kernel.def_eq(lhs, rhs), "rfl theorem sides must be def-eq");
    assert!(
        kernel.def_eq(rhs, expected),
        "registered normal form drifted"
    );
    assert_eq!(
        normalize_application_spine(kernel, lhs),
        normalize_application_spine(kernel, expected)
    );
}

fn assert_recursor_metadata(
    kernel: &mut Kernel,
    family: &str,
    expected: (u16, u16, u16, u16, &[u16]),
) {
    let name = qualified(kernel, &["AxeyumMutualInductiveComputation", family, "rec"]);
    let declaration = kernel
        .environment()
        .get(name)
        .unwrap_or_else(|| panic!("missing generated recursor for {family}"));
    let Declaration::Recursor {
        rec_rules,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        ..
    } = declaration
    else {
        panic!("selected family is missing its generated recursor");
    };
    assert_eq!(
        (*num_params, *num_indices, *num_motives, *num_minors),
        (expected.0, expected.1, expected.2, expected.3)
    );
    assert_eq!(
        rec_rules
            .iter()
            .map(|rule| rule.num_fields)
            .collect::<Vec<_>>(),
        expected.4
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

fn assert_malformed(fixture: &str, line: usize, message: &str) {
    let error = import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .expect_err("malformed mutual stream published CompletedImport");
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

fn assert_rejected(fixture: &str) {
    import_ndjson(Cursor::new(fixture.as_bytes()), ImportLimits::default())
        .expect_err("invalid mutual stream published CompletedImport");
}

#[test]
fn official_construct_group_imports_twice_with_identical_declarations() {
    let mut reports = Vec::new();
    for _ in 0..2 {
        let completed = import_ndjson(Cursor::new(CONSTRUCT.as_bytes()), ImportLimits::default())
            .expect("official mutual construct stream must complete");
        let report = completed.report();
        assert_eq!(
            (
                report.names,
                report.levels,
                report.expressions,
                report.declaration_records,
                report.admitted_declarations,
                report.axioms.len(),
                report.declaration_identities.len(),
            ),
            (75, 4, 305, 10, 26, 0, 26)
        );
        for required in [
            "AxeyumConstructMatrix.EvenTree",
            "AxeyumConstructMatrix.OddTree",
            "AxeyumConstructMatrix.EvenTree.rec",
            "AxeyumConstructMatrix.OddTree.rec",
            "AxeyumConstructMatrix.mutualWitness",
        ] {
            assert!(
                report
                    .declaration_identities
                    .iter()
                    .any(|identity| identity.name == required),
                "missing exact declaration identity for {required}"
            );
        }
        reports.push(report.clone());
    }
    assert_eq!(reports[0], reports[1]);
}

#[test]
fn official_cross_family_computation_imports_twice_and_reduces() {
    let mut reports = Vec::new();
    for _ in 0..2 {
        let completed = import_ndjson(Cursor::new(CROSS.as_bytes()), ImportLimits::default())
            .expect("official cross-family computation stream must complete");
        let (mut kernel, report) = completed.into_parts();
        assert_eq!(
            (
                report.names,
                report.levels,
                report.expressions,
                report.declaration_records,
                report.admitted_declarations,
                report.axioms.len(),
            ),
            (60, 4, 246, 7, 21, 0)
        );
        assert_recursor_metadata(&mut kernel, "EvenTree", (1, 0, 2, 4, &[1, 1]));
        assert_recursor_metadata(&mut kernel, "OddTree", (1, 0, 2, 4, &[0, 1]));
        let zero_name = qualified(
            &mut kernel,
            &["AxeyumMutualInductiveComputation", "MiniNat", "zero"],
        );
        let succ_name = qualified(
            &mut kernel,
            &["AxeyumMutualInductiveComputation", "MiniNat", "succ"],
        );
        let zero = kernel.const_(zero_name, vec![]);
        let succ = kernel.const_(succ_name, vec![]);
        let one = kernel.app(succ, zero);
        let two = kernel.app(succ, one);
        assert_computation_theorem(&mut kernel, "crossFamilyComputes", two);
        reports.push(report);
    }
    assert_eq!(reports[0], reports[1]);
}

#[test]
fn official_indexed_cross_family_computation_imports_twice_and_reduces() {
    let mut reports = Vec::new();
    for _ in 0..2 {
        let completed = import_ndjson(Cursor::new(INDEXED.as_bytes()), ImportLimits::default())
            .expect("official indexed cross-family computation stream must complete");
        let (mut kernel, report) = completed.into_parts();
        assert_eq!(
            (
                report.names,
                report.levels,
                report.expressions,
                report.declaration_records,
                report.admitted_declarations,
                report.axioms.len(),
            ),
            (72, 4, 290, 7, 21, 0)
        );
        assert_recursor_metadata(&mut kernel, "EvenVec", (1, 1, 2, 4, &[0, 2]));
        assert_recursor_metadata(&mut kernel, "OddVec", (1, 1, 2, 4, &[0, 2]));
        let zero_name = qualified(
            &mut kernel,
            &["AxeyumMutualInductiveComputation", "MiniNat", "zero"],
        );
        let succ_name = qualified(
            &mut kernel,
            &["AxeyumMutualInductiveComputation", "MiniNat", "succ"],
        );
        let zero = kernel.const_(zero_name, vec![]);
        let succ = kernel.const_(succ_name, vec![]);
        let one = kernel.app(succ, zero);
        let two = kernel.app(succ, one);
        assert_computation_theorem(&mut kernel, "indexedCrossFamilyComputes", two);
        reports.push(report);
    }
    assert_eq!(reports[0], reports[1]);
}

#[test]
fn recursor_wire_order_is_non_authoritative_but_group_order_is_exact() {
    let baseline = import_ndjson(Cursor::new(CROSS.as_bytes()), ImportLimits::default())
        .expect("baseline mutual stream must complete");
    let reversed_recursor_wire = mutate_group(CROSS, 233, |group| {
        group["recs"].as_array_mut().unwrap().reverse();
    });
    let reversed = import_ndjson(
        Cursor::new(reversed_recursor_wire.as_bytes()),
        ImportLimits::default(),
    )
    .expect("recursor wire order must be matched by checked name");
    assert_eq!(baseline.report(), reversed.report());

    let reordered_type_all = mutate_group(CROSS, 233, |group| {
        group["types"][0]["all"].as_array_mut().unwrap().reverse();
    });
    assert_malformed(
        &reordered_type_all,
        233,
        "inductive type all list differs from ordered group",
    );

    let reordered_recursor_all = mutate_group(CROSS, 233, |group| {
        group["recs"][0]["all"].as_array_mut().unwrap().reverse();
    });
    assert_malformed(
        &reordered_recursor_all,
        233,
        "inductive recursor all list differs from ordered group",
    );

    let k_target = mutate_group(CROSS, 233, |group| {
        group["recs"][0]["k"] = json!(true);
    });
    assert_malformed(&k_target, 233, "mutual recursor may not be a K target");
}

#[test]
fn family_and_constructor_metadata_are_checked_before_publication() {
    let descriptive = mutate_group(CROSS, 233, |group| {
        group["types"][0]["isReflexive"] = json!(true);
        group["types"][1]["isReflexive"] = json!(true);
    });
    import_ndjson(Cursor::new(descriptive.as_bytes()), ImportLimits::default())
        .expect("descriptive reflexive bits must not grant or deny support");

    let is_recursive = mutate_group(CROSS, 233, |group| {
        group["types"][0]["isRec"] = json!(false);
    });
    assert_malformed(
        &is_recursive,
        233,
        "generated/exported family metadata or type differs",
    );

    let divergent_universes = mutate_group(CROSS, 233, |group| {
        group["types"][1]["levelParams"] = json!([]);
    });
    assert_malformed(
        &divergent_universes,
        233,
        "mutual family universe parameters differ",
    );

    let divergent_parameter_count = mutate_group(CROSS, 233, |group| {
        group["types"][1]["numParams"] = json!(0);
    });
    assert_malformed(
        &divergent_parameter_count,
        233,
        "mutual family numParams differs",
    );

    let family_indices = mutate_group(CROSS, 233, |group| {
        group["types"][0]["numIndices"] = json!(1);
    });
    assert_malformed(
        &family_indices,
        233,
        "generated/exported family metadata or type differs",
    );

    let wrong_parent = mutate_group(CROSS, 233, |group| {
        group["ctors"][0]["induct"] = group["types"][1]["name"].clone();
    });
    assert_malformed(
        &wrong_parent,
        233,
        "constructor parent/index/name differs from family list",
    );

    let wrong_index = mutate_group(CROSS, 233, |group| {
        group["ctors"][0]["cidx"] = json!(1);
    });
    assert_malformed(
        &wrong_index,
        233,
        "constructor parent/index/name differs from family list",
    );

    let wrong_ctor_params = mutate_group(CROSS, 233, |group| {
        group["ctors"][0]["numParams"] = json!(0);
    });
    assert_malformed(
        &wrong_ctor_params,
        233,
        "constructor numParams differs from family",
    );

    let wrong_fields = mutate_group(CROSS, 233, |group| {
        group["ctors"][0]["numFields"] = json!(2);
    });
    assert_malformed(
        &wrong_fields,
        233,
        "generated/exported constructor metadata or type differs",
    );

    let reordered_ctor_wire = mutate_group(CROSS, 233, |group| {
        group["ctors"].as_array_mut().unwrap().swap(0, 1);
    });
    assert_malformed(
        &reordered_ctor_wire,
        233,
        "constructor records differ from family/constructor order",
    );

    let malformed_ctor_type = mutate_group(CROSS, 233, |group| {
        group["ctors"][0]["type"] = json!(0);
    });
    assert_rejected(&malformed_ctor_type);
}

#[test]
fn recursor_mutations_and_later_failure_never_publish_completed_import() {
    let duplicate_recursor = mutate_group(CROSS, 233, |group| {
        group["recs"][1]["name"] = group["recs"][0]["name"].clone();
    });
    assert_malformed(
        &duplicate_recursor,
        233,
        "inductive group repeats a recursor record",
    );

    for (field, value, message) in [
        (
            "numParams",
            json!(0),
            "generated/exported recursor numParams differs",
        ),
        (
            "numIndices",
            json!(1),
            "generated/exported recursor numIndices differs",
        ),
        (
            "numMotives",
            json!(1),
            "generated/exported recursor numMotives differs",
        ),
        (
            "numMinors",
            json!(3),
            "generated/exported recursor numMinors differs",
        ),
    ] {
        let mutation = mutate_group(CROSS, 233, |group| {
            group["recs"][0][field] = value;
        });
        assert_malformed(&mutation, 233, message);
    }

    let wrong_type = mutate_group(CROSS, 233, |group| {
        group["recs"][0]["type"] = json!(0);
    });
    assert_malformed(
        &wrong_type,
        233,
        "generated/exported recursor types are not definitionally equal",
    );

    let wrong_rule = mutate_group(CROSS, 233, |group| {
        group["recs"][0]["rules"][0]["rhs"] = json!(0);
    });
    assert_malformed(&wrong_rule, 233, "generated/exported recursor rule differs");

    let wrong_rule_fields = mutate_group(CROSS, 233, |group| {
        group["recs"][0]["rules"][0]["nfields"] = json!(2);
    });
    assert_malformed(
        &wrong_rule_fields,
        233,
        "generated/exported recursor rule differs",
    );

    let later_theorem_failure = mutate_record(CROSS, 318, |record| {
        record["thm"]["value"] = json!(0);
    });
    assert_rejected(&later_theorem_failure);
}
