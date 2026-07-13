//! Compile/runtime contract for the dependency-minimal `QF_BV` feature profile.

use axeyum_ir::TermArena;
use axeyum_solver::{
    CheckResult, IncrementalBvSolver, SatBvBackend, SolverBackend, SolverConfig, Value,
    export_qf_bv_unsat_proof,
};

#[test]
fn qfbv_profile_exposes_cold_warm_model_and_proof_surfaces() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let x_plus_one = arena.bv_add(x, one).unwrap();
    let same = arena.eq(x_plus_one, x).unwrap();
    let differs = arena.not(same).unwrap();

    let mut backend = SatBvBackend::new();
    let cold = backend
        .check(&arena, &[differs], &SolverConfig::default())
        .unwrap();
    let CheckResult::Sat(model) = cold else {
        panic!("8-bit x+1 != x must be satisfiable");
    };
    assert!(matches!(
        model.get(arena.symbols().next().unwrap().0),
        Some(Value::Bv { .. })
    ));

    let mut warm = IncrementalBvSolver::new();
    warm.assert_configured(&mut arena, differs).unwrap();
    assert!(matches!(warm.check(&arena).unwrap(), CheckResult::Sat(_)));

    let reflexive = arena.eq(x, x).unwrap();
    let contradiction = arena.not(reflexive).unwrap();
    let proof = export_qf_bv_unsat_proof(&arena, &[contradiction])
        .unwrap()
        .expect_proved("reflexive contradiction should produce a proof");
    assert!(proof.recheck().unwrap());
}

trait ExpectProved {
    fn expect_proved(self, message: &str) -> axeyum_solver::UnsatProof;
}

impl ExpectProved for axeyum_solver::UnsatProofOutcome {
    fn expect_proved(self, message: &str) -> axeyum_solver::UnsatProof {
        match self {
            Self::Proved(proof) => proof,
            Self::Satisfiable | Self::Inconclusive => panic!("{message}"),
        }
    }
}
