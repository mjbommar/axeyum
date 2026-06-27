//! Integration tests for the typed property SDK.

use axeyum_property::Property;
use axeyum_solver::ProofOutcome;

type TestResult = Result<(), Box<dyn std::error::Error>>;

#[test]
fn proves_trivial_bv_identity_with_evidence() -> TestResult {
    let mut property = Property::new();
    let x = property.bv::<8>("x")?;
    let goal = x.eq(&mut property, x)?;

    let outcome = property.prove(goal)?;
    assert!(matches!(outcome, ProofOutcome::Proved(_)));
    Ok(())
}

#[test]
fn minimized_counterexample_lifts_through_typed_bv_handle() -> TestResult {
    let mut property = Property::new();
    let x = property.bv::<8>("x")?;
    let five = property.bv_const::<8>(5)?;
    let goal = x.ule(&mut property, five)?;

    let outcome = property.prove_minimized(goal)?;
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("expected a minimized counterexample, got {outcome:?}");
    };
    assert_eq!(x.value_u128(&model)?, Some(6));
    Ok(())
}

#[test]
fn assumptions_and_int_terms_use_the_same_proof_front_door() -> TestResult {
    let mut property = Property::new();
    let x = property.int("x")?;
    let three = property.int_const(3);
    let four = property.int_const(4);
    let pre = x.le(&mut property, three)?;
    property.assume(pre);
    let goal = x.le(&mut property, four)?;

    let outcome = property.prove(goal)?;
    assert!(matches!(outcome, ProofOutcome::Proved(_)));
    Ok(())
}

#[test]
fn overflow_helper_is_available_on_typed_bv_handles() -> TestResult {
    let mut property = Property::new();
    let x = property.bv::<256>("x")?;
    let y = property.bv::<256>("y")?;
    let overflow = x.umul_overflows(&mut property, y)?;

    assert_eq!(
        property.arena().sort_of(overflow.term()),
        axeyum_ir::Sort::Bool
    );
    assert_eq!(property.counterexample_symbols().len(), 2);
    Ok(())
}
