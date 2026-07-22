//! Official TL2.12 computation streams: exact import and recursor reduction.

use std::io::Cursor;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};

const VECTOR: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-recursive-ih-vector-computation.ndjson"
);
const ACC: &str = include_str!(
    "../../../docs/plan/fixtures/lean4export-v4.30-recursive-ih-acc-computation.ndjson"
);

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

/// Recursively normalize application spines after the kernel's trusted WHNF
/// step. The selected registered results contain only constructor applications,
/// so no broader normalizer is needed or credited here.
fn normalize_application_spine(kernel: &mut Kernel, expression: ExprId) -> ExprId {
    let expression = kernel.whnf(expression);
    let ExprNode::App(function, argument) = kernel.expr_node(expression).clone() else {
        return expression;
    };
    let function = normalize_application_spine(kernel, function);
    let argument = normalize_application_spine(kernel, argument);
    kernel.app(function, argument)
}

fn assert_computation_theorem(kernel: &mut Kernel, theorem_components: &[&str], expected: ExprId) {
    let theorem_name = qualified(kernel, theorem_components);
    let declaration = kernel
        .environment()
        .get(theorem_name)
        .unwrap_or_else(|| panic!("missing theorem {}", kernel.display_name(theorem_name)))
        .clone();
    let Declaration::Theorem { ty, value, .. } = declaration else {
        panic!("selected computation result is not a theorem");
    };
    let inferred = kernel.infer(value).expect("computation proof must infer");
    assert!(kernel.def_eq(inferred, ty));

    let (head, arguments) = unfold_apps(kernel, ty);
    assert_eq!(
        kernel
            .display_name(match kernel.expr_node(head) {
                ExprNode::Const(name, _) => *name,
                _ => panic!("computation theorem type is not headed by Eq"),
            })
            .to_string(),
        "Eq"
    );
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
    family_components: &[&str],
    expected: (u16, u16, u16, u16, &[u16]),
) {
    let mut recursor_components = family_components.to_vec();
    recursor_components.push("rec");
    let recursor_name = qualified(kernel, &recursor_components);
    let declaration = kernel.environment().get(recursor_name).unwrap();
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

#[test]
fn official_vector_computation_imports_twice_and_reduces() {
    let mut reports = Vec::new();
    for _ in 0..2 {
        let completed = import_ndjson(Cursor::new(VECTOR.as_bytes()), ImportLimits::default())
            .expect("official Vector computation stream must complete");
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
            (60, 4, 211, 8, 18, 0)
        );
        assert_recursor_metadata(
            &mut kernel,
            &["AxeyumRecursiveIHComputation", "MiniVector"],
            (1, 1, 1, 2, &[0, 3]),
        );
        let zero_name = qualified(
            &mut kernel,
            &["AxeyumRecursiveIHComputation", "MiniNat", "zero"],
        );
        let succ_name = qualified(
            &mut kernel,
            &["AxeyumRecursiveIHComputation", "MiniNat", "succ"],
        );
        let zero = kernel.const_(zero_name, vec![]);
        let succ = kernel.const_(succ_name, vec![]);
        let expected = kernel.app(succ, zero);
        assert_computation_theorem(
            &mut kernel,
            &["AxeyumRecursiveIHComputation", "vectorHeightComputes"],
            expected,
        );
        reports.push(report);
    }
    assert_eq!(reports[0], reports[1]);
}

#[test]
fn official_acc_computation_imports_twice_and_reduces() {
    let mut reports = Vec::new();
    for _ in 0..2 {
        let completed = import_ndjson(Cursor::new(ACC.as_bytes()), ImportLimits::default())
            .expect("official Acc computation stream must complete");
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
            (67, 3, 232, 11, 20, 0)
        );
        assert_recursor_metadata(
            &mut kernel,
            &["AxeyumRecursiveIHComputation", "MiniAcc"],
            (2, 1, 1, 1, &[2]),
        );
        let true_name = qualified(&mut kernel, &["True"]);
        let expected = kernel.const_(true_name, vec![]);
        assert_computation_theorem(
            &mut kernel,
            &["AxeyumRecursiveIHComputation", "accPropertyComputes"],
            expected,
        );
        reports.push(report);
    }
    assert_eq!(reports[0], reports[1]);
}
