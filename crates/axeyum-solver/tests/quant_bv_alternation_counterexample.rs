//! ADR-0124/0125 source-bound counterexamples for alternating Bool/BV formulas.

use std::io::{Read as _, Write as _};
use std::path::PathBuf;
use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{
    BvAlternationCounterexampleCertificate, Evidence, ProofFragment, SolverConfig,
    check_bv_alternation_counterexample, produce_evidence, prove_unsat_to_lean_module,
    reconstruct_bv_alternation_counterexample_to_lean_module,
};

const PIPELINE: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__small-pipeline-fixpoint-3.smt2"
);
const BUG802: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__bug802.smt2"
);

fn assertions(script: &axeyum_smtlib::Script) -> Vec<axeyum_ir::TermId> {
    script
        .commands
        .iter()
        .filter_map(|command| match command {
            ScriptCommand::Assert(term) => Some(*term),
            _ => None,
        })
        .collect()
}

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

struct ModuleSpool(PathBuf);

impl Drop for ModuleSpool {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn assert_routed_module_equals(
    label: &str,
    direct: String,
    route: impl FnOnce() -> (ProofFragment, String),
) -> ProofFragment {
    let path = std::env::temp_dir().join(format!(
        "axeyum-alternation-equality-{}-{label}.lean",
        std::process::id()
    ));
    let spool = ModuleSpool(path);
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&spool.0)
        .expect("create direct-module equality spool");
    output
        .write_all(direct.as_bytes())
        .expect("spool direct Lean module");
    drop(output);
    drop(direct);

    let (fragment, routed) = route();
    let mut input = std::fs::File::open(&spool.0).expect("open direct-module equality spool");
    let direct_len = input
        .metadata()
        .expect("read direct-module equality metadata")
        .len();
    assert_eq!(u64::try_from(routed.len()).unwrap(), direct_len);
    let mut offset = 0_usize;
    let mut buffer = vec![0_u8; 1024 * 1024];
    loop {
        let read = input.read(&mut buffer).expect("read direct Lean module");
        if read == 0 {
            break;
        }
        assert_eq!(&routed.as_bytes()[offset..offset + read], &buffer[..read]);
        offset += read;
    }
    assert_eq!(offset, routed.len());
    fragment
}

fn assert_replacement_rejected(
    arena: &TermArena,
    certificate: &BvAlternationCounterexampleCertificate,
    assertion: axeyum_ir::TermId,
) {
    let mut changed = certificate.clone();
    changed.assertion = assertion;
    assert!(!check_bv_alternation_counterexample(arena, &[assertion], &changed).unwrap());
}

fn pipeline_certificate() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    BvAlternationCounterexampleCertificate,
) {
    let mut script = parse_script(PIPELINE).unwrap();
    let assertions = assertions(&script);
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBvAlternationCounterexample(certificate) = report.evidence else {
        panic!("pipeline must use ADR-0124 evidence")
    };
    assert!(report.trusted_steps.is_empty());
    assert!(certificate.residual_proof.recheck().unwrap());
    assert!(check_bv_alternation_counterexample(&script.arena, &assertions, &certificate).unwrap());
    (script, assertions, certificate)
}

#[test]
fn public_pipeline_has_source_bound_checked_evidence() {
    let (script, assertions, certificate) = pipeline_certificate();
    assert_eq!(certificate.outer_bindings.len(), 32);
    assert!(check_bv_alternation_counterexample(&script.arena, &assertions, &certificate).unwrap());
}

#[test]
fn small_alternation_counterexample_reconstructs_and_routes() {
    let text = "(set-logic BV)
        (assert (forall ((x (_ BitVec 2))) (exists ((y (_ BitVec 2)))
          (=> (= x (_ bv3 2)) (not (= y y))))))
        (check-sat)";
    let mut script = parse_script(text).expect("small alternation parses");
    let assertions = assertions(&script);
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("small alternation has evidence");
    let Evidence::UnsatBvAlternationCounterexample(certificate) = report.evidence else {
        panic!("small alternation must use ADR-0124 evidence")
    };
    let direct = reconstruct_bv_alternation_counterexample_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("small alternation reconstructs");
    assert!(direct.contains("Exists.rec"));
    assert!(direct.contains("theorem axeyum_refutation : False"));
    assert!(!direct.contains("sorryAx"));

    let (fragment, routed) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("small alternation routes");
    assert_eq!(fragment, ProofFragment::BvAlternationCounterexample);
    assert_eq!(routed, direct);
}

#[test]
#[ignore = "release-only public-corpus ADR-0124 Lean reconstruction stress gate"]
fn public_pipeline_reconstructs_from_the_full_alternating_source() {
    let (mut script, assertions, certificate) = pipeline_certificate();
    let direct = reconstruct_bv_alternation_counterexample_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("public pipeline alternation reconstructs");
    assert!(direct.contains("Exists.rec"));
    assert!(!direct.contains("sorryAx"));
    let fragment = assert_routed_module_equals("pipeline", direct, || {
        prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("public pipeline alternation routes")
    });
    assert_eq!(fragment, ProofFragment::BvAlternationCounterexample);
}

#[test]
#[ignore = "release-only public-corpus ADR-0125 Lean reconstruction stress gate"]
fn bug802_reconstructs_all_530_quantified_binders() {
    let mut script = parse_script(BUG802).expect("bug802 parses");
    let assertions = assertions(&script);
    let report =
        produce_evidence(&mut script.arena, &assertions, &config()).expect("bug802 has evidence");
    let Evidence::UnsatBvAlternationCounterexample(certificate) = report.evidence else {
        panic!("bug802 must use ADR-0125 evidence")
    };
    let direct = reconstruct_bv_alternation_counterexample_to_lean_module(
        &script.arena,
        &assertions,
        &certificate,
    )
    .expect("bug802 alternation reconstructs");
    assert!(direct.contains("Exists.rec"));
    assert!(!direct.contains("sorryAx"));
    let fragment = assert_routed_module_equals("bug802", direct, || {
        prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("bug802 alternation routes")
    });
    assert_eq!(fragment, ProofFragment::BvAlternationCounterexample);
}

#[test]
fn large_public_hardware_fixpoint_has_checked_evidence() {
    let mut script = parse_script(BUG802).unwrap();
    let assertions = assertions(&script);
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    let Evidence::UnsatBvAlternationCounterexample(certificate) = report.evidence else {
        panic!("bug802 must use scaled source-bound alternation evidence")
    };
    assert_eq!(certificate.outer_bindings.len(), 318);
    assert!(report.trusted_steps.is_empty());
    assert!(check_bv_alternation_counterexample(&script.arena, &assertions, &certificate).unwrap());
}

#[test]
fn binding_and_proof_mutations_fail_closed() {
    let (mut script, assertions, certificate) = pipeline_certificate();

    let mut missing = certificate.clone();
    missing.outer_bindings.pop();
    assert!(!check_bv_alternation_counterexample(&script.arena, &assertions, &missing).unwrap());

    let mut reordered = certificate.clone();
    reordered.outer_bindings.swap(0, 1);
    assert!(!check_bv_alternation_counterexample(&script.arena, &assertions, &reordered).unwrap());

    let mut changed = certificate.clone();
    changed.outer_bindings[0].1 = Value::Bv {
        width: 32,
        value: 1,
    };
    assert!(!check_bv_alternation_counterexample(&script.arena, &assertions, &changed).unwrap());

    let mut proof = certificate.clone();
    proof.residual_proof.dimacs.push_str("c tampered\n");
    assert!(!check_bv_alternation_counterexample(&script.arena, &assertions, &proof).unwrap());

    let mut stale = certificate;
    stale.assertion = script.arena.bool_const(false);
    assert!(!check_bv_alternation_counterexample(&script.arena, &assertions, &stale).unwrap());
}

#[test]
fn admission_boundary_mutations_fail_closed() {
    let (mut script, _, certificate) = pipeline_certificate();

    let x = script.arena.declare("boundary_x", Sort::BitVec(2)).unwrap();
    let y = script.arena.declare("boundary_y", Sort::BitVec(2)).unwrap();
    let free = script.arena.declare("boundary_free", Sort::Bool).unwrap();
    let x_term = script.arena.var(x);
    let y_term = script.arena.var(y);
    let free_term = script.arena.var(free);
    let x_eq_y = script.arena.eq(x_term, y_term).unwrap();
    let inner_in_guard = script.arena.implies(x_eq_y, free_term).unwrap();
    let exists = script.arena.exists(y, inner_in_guard).unwrap();
    let assertion = script.arena.forall(x, exists).unwrap();
    assert_replacement_rejected(&script.arena, &certificate, assertion);

    let true_term = script.arena.bool_const(true);
    let free_body = script.arena.implies(true_term, free_term).unwrap();
    let exists = script.arena.exists(y, free_body).unwrap();
    let assertion = script.arena.forall(x, exists).unwrap();
    assert_replacement_rejected(&script.arena, &certificate, assertion);

    let non_implication = script.arena.exists(y, x_eq_y).unwrap();
    let assertion = script.arena.forall(x, non_implication).unwrap();
    assert_replacement_rejected(&script.arena, &certificate, assertion);

    let reversed = script.arena.forall(x, x_eq_y).unwrap();
    let assertion = script.arena.exists(y, reversed).unwrap();
    assert_replacement_rejected(&script.arena, &certificate, assertion);

    let i = script.arena.declare("boundary_i", Sort::Int).unwrap();
    let zero = script.arena.int_const(0);
    let i_term = script.arena.var(i);
    let i_eq_zero = script.arena.eq(i_term, zero).unwrap();
    let matrix = script.arena.implies(i_eq_zero, free_term).unwrap();
    let exists = script.arena.exists(y, matrix).unwrap();
    let assertion = script.arena.forall(i, exists).unwrap();
    assert_replacement_rejected(&script.arena, &certificate, assertion);
}

#[test]
fn satisfiable_neighbor_does_not_get_counterexample_evidence() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(2)).unwrap();
    let y = arena.declare("y", Sort::BitVec(2)).unwrap();
    let x_term = arena.var(x);
    let y_term = arena.var(y);
    let three = arena.bv_const(2, 3).unwrap();
    let guard = arena.eq(x_term, three).unwrap();
    let witness = arena.eq(y_term, x_term).unwrap();
    let matrix = arena.implies(guard, witness).unwrap();
    let exists = arena.exists(y, matrix).unwrap();
    let assertion = arena.forall(x, exists).unwrap();

    let report = produce_evidence(&mut arena, &[assertion], &config()).unwrap();
    assert!(!matches!(
        report.evidence,
        Evidence::UnsatBvAlternationCounterexample(_)
    ));
}

#[test]
fn binder_cap_rejects_oversized_prefix() {
    let (_, _, mut certificate) = pipeline_certificate();
    let mut arena = TermArena::new();
    let existential = arena.declare("cap_exists", Sort::Bool).unwrap();
    let antecedent = arena.bool_const(true);
    let consequent = arena.bool_const(false);
    let matrix = arena.implies(antecedent, consequent).unwrap();
    let mut assertion = arena.exists(existential, matrix).unwrap();
    for index in 0..1024 {
        let binder = arena
            .declare(&format!("cap_forall_{index}"), Sort::Bool)
            .unwrap();
        assertion = arena.forall(binder, assertion).unwrap();
    }
    certificate.assertion = assertion;
    assert!(!check_bv_alternation_counterexample(&arena, &[assertion], &certificate).unwrap());
}
