//! ADR-0317 typed source-contract bridge and authenticated MIR gates.

include!("fixtures/mir-contract-target/src/lib.rs");

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval, render};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::ast::{BinOp, Expr, Stmt, Ty};
use axeyum_verify::reflect::contracts::{
    SourceContractBridgeErrorKind, scalar_contract_from_source,
};
use axeyum_verify::reflect::llvm::loops::{ScalarCallContract, ScalarContractExpr};
use axeyum_verify::reflect::mir::checked::{
    MirScalarConfig, MirVerifiedContractResolver, ReflectErrorKind, reflect_scalar_into_checked,
    reflect_scalar_into_checked_with_contracts,
};
use sha2::{Digest, Sha256};

const CAPTURED_MIR: &str = include_str!("fixtures/mir-contract-target/artifacts/wrapping_inc.mir");

fn boxed(expression: ScalarContractExpr) -> Box<ScalarContractExpr> {
    Box::new(expression)
}

fn expected_contract() -> ScalarCallContract {
    ScalarCallContract::new_relational(
        "wrapping_inc",
        vec![8],
        8,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Eq(
            boxed(ScalarContractExpr::Result),
            boxed(ScalarContractExpr::BvAdd(
                boxed(ScalarContractExpr::Argument(0)),
                boxed(ScalarContractExpr::BitVec { width: 8, value: 1 }),
            )),
        ),
        ScalarContractExpr::Bool(true),
    )
    .expect("hand-built wrapping contract")
}

fn source_contract() -> axeyum_verify::ContractProgram {
    wrapping_inc__axeyum_program()
}

fn bridge_kind(
    contract: &axeyum_verify::ContractProgram,
    config: &SolverConfig,
) -> SourceContractBridgeErrorKind {
    scalar_contract_from_source(contract, config)
        .expect_err("mutation must not become a scalar summary")
        .kind()
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-contract-target")
}

fn sha256(path: &Path) -> String {
    let bytes = fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(output, "{byte:02x}").expect("writing to a String cannot fail");
    }
    output
}

fn eval_bool(arena: &TermArena, term: TermId, assignment: &Assignment) -> bool {
    match eval(arena, term, assignment).expect("complete bridge assignment must evaluate") {
        Value::Bool(value) => value,
        other => panic!("expected Bool evaluation, got {other:?}"),
    }
}

fn eval_bv(arena: &TermArena, term: TermId, assignment: &Assignment) -> u128 {
    match eval(arena, term, assignment).expect("complete bridge assignment must evaluate") {
        Value::Bv { value, .. } => value,
        other => panic!("expected bit-vector evaluation, got {other:?}"),
    }
}

fn assert_proved(arena: &mut TermArena, hypotheses: &[TermId], goal: TermId, label: &str) {
    let outcome = prove(arena, hypotheses, goal, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: solver hard error: {error}"));
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "{label}: expected proof, got {outcome:?}"
    );
}

fn exercise_resolver(resolver: &MirVerifiedContractResolver) -> (String, String, String, String) {
    let mut arena = TermArena::new();
    let input_symbol = arena.declare("input", Sort::BitVec(8)).unwrap();
    let input = arena.var(input_symbol);
    let modular = reflect_scalar_into_checked_with_contracts(
        &mut arena,
        &[input],
        CAPTURED_MIR,
        &MirScalarConfig::new("call_wrapping_inc", 64),
        resolver,
    )
    .expect("captured direct caller must consume one verified contract");
    let inlined = reflect_scalar_into_checked(
        &mut arena,
        &[input],
        CAPTURED_MIR,
        &MirScalarConfig::new("inlined_wrapping_inc", 64),
    )
    .expect("captured inlined control must reflect independently");
    assert_eq!(modular.call_sites().len(), 1);
    let call = &modular.call_sites()[0];
    assert_eq!(call.callee(), "wrapping_inc");

    let panic_equal = arena.eq(modular.panic, inlined.panic).unwrap();
    assert_proved(
        &mut arena,
        &[],
        panic_equal,
        "modular and inlined wrapping panic predicates",
    );
    let result_equal = arena
        .eq(modular.result.value, inlined.result.value)
        .unwrap();
    assert_proved(
        &mut arena,
        &[modular.assumptions],
        result_equal,
        "verified modular wrapping result equals the inlined control",
    );
    let unconstrained = prove(&mut arena, &[], result_equal, &SolverConfig::default())
        .expect("mutation check must not hard-error");
    assert!(
        matches!(unconstrained, ProofOutcome::Disproved(_)),
        "dropping the contract relation must expose the fresh result"
    );

    let mut normal_rows = 0_u32;
    for value in 0_u128..=u128::from(u8::MAX) {
        let expected = (value + 1) & u128::from(u8::MAX);
        let mut assignment = Assignment::new();
        assignment.set(input_symbol, Value::Bv { width: 8, value });
        assignment.set(
            call.result_symbol(),
            Value::Bv {
                width: 8,
                value: expected,
            },
        );
        assert!(!eval_bool(&arena, modular.panic, &assignment));
        assert!(!eval_bool(&arena, inlined.panic, &assignment));
        assert!(eval_bool(&arena, modular.assumptions, &assignment));
        assert_eq!(eval_bv(&arena, modular.result.value, &assignment), expected);
        assert_eq!(eval_bv(&arena, inlined.result.value, &assignment), expected);
        normal_rows += 1;
    }
    assert_eq!(normal_rows, 256);

    (
        render(&arena, modular.result.value),
        render(&arena, modular.panic),
        render(&arena, modular.assumptions),
        render(&arena, call.relation()),
    )
}

#[test]
fn generated_contract_exactly_matches_the_hand_built_declaration() {
    let generated = scalar_contract_from_source(&source_contract(), &SolverConfig::default())
        .expect("annotated wrapping contract must bridge");
    assert_eq!(generated, expected_contract());
    for x in u8::MIN..=u8::MAX {
        assert_eq!(wrapping_inc(x), x.wrapping_add(1));
    }
}

/// # Refreshing the fixture's `Cargo.lock`
///
/// `Cargo.lock` below is one of the six authenticated files, and the fixture
/// builds itself with `--locked`. So the lock goes stale on its own schedule —
/// a yanked upstream version, or the workspace graph moving under it — and
/// `cargo_mir_build`'s `scalar_profile_reproduces_the_committed_root_independent_capture`
/// fails with "cannot update the lock file ... because --locked was passed".
///
/// **The lock and the hash here must move in the same commit.** Refreshing one
/// alone trades one red test for another; that is exactly what happened on
/// 2026-08-13 (see `docs/plan/rado-publishable-result-2026-08-13.md`) and it
/// happened again on 2026-08-16, which is why this note exists. Precedent for
/// the class: 6261fae11, 083a5f7df.
///
/// Regenerate with `cargo generate-lockfile` in the fixture directory, then
/// verify against the toolchain CI actually pins for that job —
/// `nightly-2026-05-01` (ADR-0287, rustc `f53b654a8`) — with
/// `cargo +nightly-2026-05-01 metadata --locked`, NOT with the repo's default
/// nightly. Resolving on a newer toolchain can select crates whose
/// `rust-version` the pinned one cannot satisfy, and `--locked` would then fail
/// only in CI.
///
/// # There is a THIRD copy of these hashes, and nothing checks it
///
/// `artifacts/SHA256SUMS` records the same six digests. **No test reads it** —
/// this function carries its own copy — so it silently went stale when the lock
/// was refreshed on 2026-08-16 and every gate stayed green. Verify it by hand
/// after any change here:
///
/// ```sh
/// (cd crates/axeyum-verify/tests/fixtures/mir-contract-target && \
///   sha256sum -c artifacts/SHA256SUMS)
/// ```
///
/// # A solver-internal module move invalidates the capture
///
/// `wrapping_inc.mir` is byte-exact MIR, and MIR names types by their
/// **canonical defining path** — not by any re-export. Moving `SolverError`
/// from `axeyum_solver::backend` to `axeyum_solver::error` kept every one of the
/// ~60 `use` sites compiling and still changed two lines of the captured module:
///
/// ```text
/// -  let mut _2: Result<Verdict, axeyum_solver::backend::SolverError>;
/// +  let mut _2: Result<Verdict, axeyum_solver::error::SolverError>;
/// ```
///
/// So this artifact is coupled to the solver's *internal* module layout, and a
/// refactor that touches a type appearing in the fixture's MIR must refresh it.
/// That is the artifact being honest, not a defect — but it means the refresh is
/// part of such a change, and `mir_bytes` in `capture-summary.json` plus
/// `CAPTURED_MIR.len()` below move with it. Re-capture with the
/// `axeyum-mir-build` binary using the pinned cargo/rustc, exactly as
/// `run_scalar_contract_capture` invokes it; two independent captures must come
/// out byte-identical, which is what `provenance.json`'s
/// `fresh_capture_byte_identical` records.
#[test]
fn committed_capture_is_authenticated_and_root_independent() {
    let root = fixture_root();
    for (relative, expected) in [
        (
            "Cargo.toml",
            "fc237aa090cd9cac30866890a1b2dda2b8808ae08c9e3e21f69e3ec35777b50b",
        ),
        (
            "Cargo.lock",
            "b2ee38c3d6ebcf74fea25cc089a1f8fd629318ccec66c34da8dfded55af40c19",
        ),
        (
            "src/lib.rs",
            "432d903ab3757723c02003ce4b9e2c5c7460a3b8e9a0a4deb81eca08f0efaf85",
        ),
        (
            "artifacts/wrapping_inc.mir",
            "1f22a92d96c21c0946a31ea2b279f7d5e71cdff490f00aeacbc36a13d73f12f0",
        ),
        (
            "artifacts/capture-summary.json",
            "97ec4c1d5966efc295e72bf8f34c10f571d4bd533825b5be9d16f10df62470df",
        ),
        (
            "artifacts/provenance.json",
            "46ab0db3273b1010d59beaa201e0a2939c37423e5fc0d0460554642e562e619a",
        ),
    ] {
        assert_eq!(sha256(&root.join(relative)), expected, "{relative}");
    }
    let summary = fs::read_to_string(root.join("artifacts/capture-summary.json")).unwrap();
    assert!(summary.contains("\"manifest\":\"$MANIFEST\""));
    assert!(summary.contains("\"target_dir\":\"$TARGET_DIR\""));
    assert!(summary.contains("\"output\":\"$OUTPUT\""));
    assert!(!summary.contains(env!("CARGO_MANIFEST_DIR")));
    assert_eq!(CAPTURED_MIR.len(), 10_276);
}

#[test]
fn source_generated_and_hand_built_contracts_authenticate_the_same_mir() {
    let generated = scalar_contract_from_source(&source_contract(), &SolverConfig::default())
        .expect("source contract must bridge");
    let hand_built = expected_contract();
    let generated_resolver =
        MirVerifiedContractResolver::from_contracts(&[(generated, CAPTURED_MIR)])
            .expect("source-generated declaration must authenticate the exact MIR body");
    let hand_built_resolver =
        MirVerifiedContractResolver::from_contracts(&[(hand_built, CAPTURED_MIR)])
            .expect("hand-built declaration must independently authenticate the exact MIR body");
    assert_eq!(generated_resolver.contract_names(), vec!["wrapping_inc"]);
    assert_eq!(
        exercise_resolver(&generated_resolver),
        exercise_resolver(&hand_built_resolver)
    );
}

#[test]
fn captured_body_and_resource_mutations_fail_closed() {
    let generated = scalar_contract_from_source(&source_contract(), &SolverConfig::default())
        .expect("source contract must bridge");
    let wrong_body = CAPTURED_MIR.replacen("const 1_u8", "const 2_u8", 1);
    let error = MirVerifiedContractResolver::from_contracts(&[(generated.clone(), &wrong_body)])
        .expect_err("compiler-body drift must be refuted");
    assert_eq!(error.kind(), ReflectErrorKind::ContractDisproved);

    let unsupported_intrinsic = CAPTURED_MIR.replacen(
        "core::num::<impl u8>::wrapping_add",
        "core::num::<impl u8>::saturating_add",
        1,
    );
    let error =
        MirVerifiedContractResolver::from_contracts(&[(generated.clone(), &unsupported_intrinsic)])
            .expect_err("unregistered qualified calls must remain rejected");
    assert_eq!(error.kind(), ReflectErrorKind::Syntax);

    let error = MirVerifiedContractResolver::from_contracts_with_config(
        &[(generated, CAPTURED_MIR)],
        &SolverConfig::default().with_node_budget(0),
    )
    .expect_err("zero verification resources must fail closed");
    assert_eq!(error.kind(), ReflectErrorKind::ContractUnknown);
}

#[test]
fn source_contract_mutations_fail_closed_before_summary_use() {
    let mut wrong_postcondition = source_contract();
    wrong_postcondition.ensures = Expr::Binary {
        op: BinOp::Eq,
        lhs: Box::new(Expr::Var(wrong_postcondition.result_name.clone())),
        rhs: Box::new(Expr::Var("x".into())),
    };
    assert_eq!(
        bridge_kind(&wrong_postcondition, &SolverConfig::default()),
        SourceContractBridgeErrorKind::SourceCounterexample
    );

    let mut wrong_body = source_contract();
    wrong_body.result = Expr::Binary {
        op: BinOp::WrappingAdd,
        lhs: Box::new(Expr::Var("x".into())),
        rhs: Box::new(Expr::IntLit {
            value: 2,
            ty: Ty::Int {
                width: 8,
                signed: false,
            },
        }),
    };
    assert_eq!(
        bridge_kind(&wrong_body, &SolverConfig::default()),
        SourceContractBridgeErrorKind::SourceCounterexample
    );

    let mut partial_postcondition = source_contract();
    partial_postcondition.ensures = Expr::Binary {
        op: BinOp::Eq,
        lhs: Box::new(Expr::Var(partial_postcondition.result_name.clone())),
        rhs: Box::new(Expr::Binary {
            op: BinOp::Add,
            lhs: Box::new(Expr::Var("x".into())),
            rhs: Box::new(Expr::IntLit {
                value: 1,
                ty: Ty::Int {
                    width: 8,
                    signed: false,
                },
            }),
        }),
    };
    assert_eq!(
        bridge_kind(&partial_postcondition, &SolverConfig::default()),
        SourceContractBridgeErrorKind::SourceUnknown
    );

    let mut prefix_statement = source_contract();
    prefix_statement.program.body.push(Stmt::Let {
        name: "copy".into(),
        ty: Ty::Int {
            width: 8,
            signed: false,
        },
        value: Expr::Var("x".into()),
    });
    assert_eq!(
        bridge_kind(&prefix_statement, &SolverConfig::default()),
        SourceContractBridgeErrorKind::UnsupportedShape
    );

    let mut nonliteral_requirement = source_contract();
    nonliteral_requirement.requires = Expr::Binary {
        op: BinOp::Eq,
        lhs: Box::new(Expr::Var("x".into())),
        rhs: Box::new(Expr::Var("x".into())),
    };
    assert_eq!(
        bridge_kind(&nonliteral_requirement, &SolverConfig::default()),
        SourceContractBridgeErrorKind::UnsupportedShape
    );

    assert_eq!(
        bridge_kind(
            &source_contract(),
            &SolverConfig::default().with_node_budget(0),
        ),
        SourceContractBridgeErrorKind::SourceUnknown
    );
}
