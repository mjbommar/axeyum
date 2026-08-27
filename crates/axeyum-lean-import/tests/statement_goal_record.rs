//! Controls for the statement-only import goal-record layer
//! (`axeyum_lean_import::build_statement_goal_record`).
//!
//! These are deliberately at the INTEGRATION level (a fresh process per
//! test), complementing `tests/statement_adapter.rs`'s coverage of
//! `import_statement_ndjson` itself and `src/statement_goal_record.rs`'s own
//! `#[cfg(test)]` unit tests, which exercise the pure record-building logic
//! against the same synthetic stream shape.

use std::io::Cursor;

use axeyum_lean_import::{
    ImportLimits, StatementImportError, build_statement_goal_record, import_statement_ndjson,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, Lean4ExportMetadata, ReducibilityHint};

const TARGET: &str = "Axeyum.Autogenesis.Statement.target";

fn target_name(kernel: &mut Kernel) -> axeyum_lean_kernel::NameId {
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    let statement = kernel.name_str(autogenesis, "Statement");
    kernel.name_str(statement, "target")
}

fn proposition(kernel: &mut Kernel) -> (axeyum_lean_kernel::ExprId, axeyum_lean_kernel::ExprId) {
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);
    let p = kernel.bvar(0);
    let root = kernel.anon();
    let binder = kernel.name_str(root, "p");
    let goal = kernel.pi(binder, prop, p, BinderInfo::Default);
    (prop, goal)
}

fn render(kernel: &Kernel) -> String {
    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("test stream must render")
}

fn definition_stream() -> String {
    let mut kernel = Kernel::new();
    let name = target_name(&mut kernel);
    let (prop, goal) = proposition(&mut kernel);
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: prop,
            value: goal,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("goal definition must check");
    render(&kernel)
}

/// A malformed (not-even-JSON) byte stream must be refused by the ordinary
/// wire-import path before the statement-adapter's own trusted-declaration
/// gate ever runs, and must yield no [`axeyum_lean_import::CompletedStatementImport`]
/// to build a goal record from -- fail-closed is a *type-level* guarantee
/// here (there is no way to call `build_statement_goal_record` without one).
#[test]
fn a_malformed_statement_stream_admits_nothing() {
    let error = import_statement_ndjson(
        Cursor::new(b"this is not ndjson at all\n{{{\n".to_vec()),
        ImportLimits::default(),
        TARGET,
    )
    .expect_err("garbage bytes must never import");
    assert!(matches!(error, StatementImportError::Import(_)));
}

/// A valid proof-free statement yields a goal record whose kernel-rendered
/// type is exactly the source proposition, and whose declaration/dependency
/// counts describe what was actually admitted (never a hardcoded "1").
#[test]
fn a_valid_statement_yields_a_goal_record_matching_the_source() {
    let completed = import_statement_ndjson(
        Cursor::new(definition_stream()),
        ImportLimits::default(),
        TARGET,
    )
    .expect("proof-free statement must import");
    let record = build_statement_goal_record(&completed, TARGET)
        .expect("a successfully imported target must yield a goal record");
    assert_eq!(record.goal_lean4, "((p : Prop) -> p)");
    assert_eq!(record.target_name, TARGET);
    assert_eq!(record.admitted_declaration_count, 1);
    assert!(record.substituted_theorems.is_empty());
    // The identity is structural (kernel content), independent of the
    // rendered-text hash -- the two must not be conflated.
    assert_ne!(record.target_content_sha256, record.goal_sha256);
}

/// Mirrors the real failure this task exists to characterize
/// (`docs/autogenesis/292-…`: `Nat.Coprime` statement-only import reaching
/// `Nat.mod_lt` through `Nat.gcd`'s well-founded-recursion definiens) at
/// minimal scale: a `Theorem`-kind declaration reached only through an
/// ADMITTED, non-target `Definition`'s VALUE -- never through the target's
/// own syntax, and never as a bare unrelated top-level declaration (which
/// `tests/statement_adapter.rs::unrelated_axiom_is_rejected` already
/// covers for `Axiom`). This is the shape that makes the refusal a property
/// of "what got admitted into the stream", not "what the goal's own type
/// mentions".
#[test]
fn a_theorem_reachable_only_through_an_auxiliary_definition_still_poisons_the_stream() {
    let mut kernel = Kernel::new();
    let zero = kernel.level_zero();
    let prop_sort = kernel.sort(zero);
    let root = kernel.anon();

    // `id_prop := (p : Prop) -> p -> p` -- impredicative, so this whole Pi
    // itself has sort `Prop`, making it usable both as a proposition and as
    // the type of a proof of that proposition.
    //
    // De Bruijn bookkeeping: the inner Pi's DOMAIN is built one binder deep
    // (only the outer `p` is open), so `p` there is `bvar(0)`; the inner
    // Pi's BODY is built two binders deep (`p` then `h`), so `p` there is
    // `bvar(1)` (index 0 is the nearer `h`).
    let inner_binder = kernel.name_str(root, "h");
    let p_in_inner_domain = kernel.bvar(0);
    let p_in_inner_body = kernel.bvar(1);
    let inner_pi = kernel.pi(
        inner_binder,
        p_in_inner_domain,
        p_in_inner_body,
        BinderInfo::Default,
    );
    let outer_binder = kernel.name_str(root, "p");
    let id_prop_ty = kernel.pi(outer_binder, prop_sort, inner_pi, BinderInfo::Default);

    // `helper : id_prop := fun p h => h` -- a genuine, independently checked
    // proof, admitted as `Declaration::Theorem`. Same bookkeeping: the inner
    // lambda's DOMAIN (the type annotation on `h`) is one binder deep, so
    // `p` there is `bvar(0)`; the inner lambda's BODY is `h` itself, two
    // binders deep, so `bvar(0)` there is the nearer `h`.
    let p_for_h_domain = kernel.bvar(0);
    let h_itself = kernel.bvar(0);
    let inner_lam = kernel.lam(inner_binder, p_for_h_domain, h_itself, BinderInfo::Default);
    let helper_value = kernel.lam(outer_binder, prop_sort, inner_lam, BinderInfo::Default);
    let helper_name = kernel.name_str(root, "Helper");
    kernel
        .add_declaration(Declaration::Theorem {
            name: helper_name,
            uparams: vec![],
            ty: id_prop_ty,
            value: helper_value,
        })
        .expect("helper theorem must check");

    // `wrapped : id_prop := Helper` -- an ordinary, non-trusted `Definition`
    // whose VALUE is exactly the theorem above, standing in for
    // `Nat.gcd`'s definiens embedding `Nat.mod_lt`'s proof.
    let helper_const = kernel.const_(helper_name, vec![]);
    let wrapped_name = kernel.name_str(root, "Wrapped");
    kernel
        .add_declaration(Declaration::Definition {
            name: wrapped_name,
            uparams: vec![],
            ty: id_prop_ty,
            value: helper_const,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("wrapped definition must check");

    // The target's own Prop never mentions `Helper` or `Wrapped` at all --
    // it is a completely independent, syntactically unrelated proposition,
    // exactly like `unrelated_axiom_is_rejected`'s control, but here the
    // trusted declaration is reached only through an admitted auxiliary
    // DEFINITION rather than sitting bare at top level.
    let target = target_name(&mut kernel);
    let (target_prop, target_goal) = proposition(&mut kernel);
    kernel
        .add_declaration(Declaration::Definition {
            name: target,
            uparams: vec![],
            ty: target_prop,
            value: target_goal,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("target definition must check");

    let error = import_statement_ndjson(
        Cursor::new(render(&kernel)),
        ImportLimits::default(),
        TARGET,
    )
    .expect_err(
        "a theorem reachable only via an auxiliary definition must still poison the stream",
    );
    assert!(matches!(
        error,
        StatementImportError::TrustedDeclaration {
            kind: axeyum_lean_import::DeclarationKind::Theorem,
            ..
        }
    ));
    // Confirm which name -- `wrapped`'s own admission never referenced the
    // stream's untrusted claim about the theorem; the wire fed a real proof
    // term into an independent kernel type-check.
    if let StatementImportError::TrustedDeclaration { name, .. } = error {
        assert_eq!(name, "Helper");
    }
}
