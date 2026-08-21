//! Tests for the one-axiom negative control.
//!
//! The claims: the control environment carries **exactly one** axiom; that axiom
//! is discharged by a proved law in the same environment; an ordinary refutation
//! run over it reaches exactly that one name; and the same refutation over the
//! untouched `Int` development reaches nothing. The last two are the control and
//! its own control — a run in which both came back empty would mean the
//! measurement stopped seeing assumptions, not that the control became free.

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::{Declaration, Kernel};

use super::{CONTROL_AXIOM_NAME, CONTROL_DISCHARGE_NAME, ControlCarrier, build_control_carrier};
use crate::reconstruct::arithmetic::ordered_ring::{carrier_axioms_of, refutation_axiom_footprint};
use crate::reconstruct::arithmetic::{LraReconstructCtx, reconstruct_lra_proof};

/// `x ≤ 0 ∧ 1 ≤ x` — the smallest refutation that reaches the kernel, and one
/// that ends on irreflexivity like every other Farkas chain.
fn baby_farkas() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let upper = arena.real_le(x, zero).unwrap();
    let lower = arena.real_le(one, x).unwrap();
    (arena, vec![upper, lower])
}

/// The whole control, counted: **one** `Declaration::Axiom` in the environment,
/// and it is the one this module declares on purpose.
///
/// The `Int` development underneath it contributes none — that is the measured
/// `integer: axiom=0` row of the axiom ledger, re-read here from the same
/// environment the control lives in rather than taken on trust.
#[test]
fn the_control_environment_carries_exactly_one_axiom() {
    let mut kernel = Kernel::new();
    let control = build_control_carrier(&mut kernel).expect("the control carrier builds");

    let axioms: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert_eq!(
        axioms,
        vec![CONTROL_AXIOM_NAME.to_owned()],
        "the control must be exactly one axiom, and it must be the declared one"
    );
    assert_eq!(
        kernel.display_name(control.axiom).to_string(),
        CONTROL_AXIOM_NAME
    );
    assert_eq!(
        kernel.display_name(control.discharge).to_string(),
        CONTROL_DISCHARGE_NAME
    );
}

/// The property the 30-axiom control does not have: the control assumption is
/// **provably redundant**, and the proof is in the same environment.
///
/// `AxReal`'s 30 are only *relatively* consistent. This one is discharged
/// outright, so shrinking the control also removed the last way the control
/// itself could make the system unsound.
#[test]
fn the_control_axiom_is_discharged_by_a_proved_law_in_the_same_environment() {
    let mut kernel = Kernel::new();
    let control = build_control_carrier(&mut kernel).expect("the control carrier builds");

    assert!(
        kernel.axiom_footprint(control.discharge).is_empty(),
        "the discharge must rest on nothing: {:?}",
        kernel.axiom_footprint(control.discharge)
    );
    // …and it really is a *different* declaration from the axiom it discharges,
    // so "empty footprint" is not being read off the axiom itself.
    assert_ne!(control.axiom, control.discharge);
    assert_ne!(control.axiom, control.proved);
    let ControlCarrier { proved, axiom, .. } = control;
    let proved_ty = kernel.environment().get(proved).map(Declaration::ty);
    let axiom_ty = kernel.environment().get(axiom).map(Declaration::ty);
    assert_eq!(
        proved_ty, axiom_ty,
        "the control axiom must state exactly the law it stands in for"
    );
}

/// **The control, measured.** An ordinary LRA refutation run over the control
/// carrier rests on exactly one carrier axiom — the control's — while the same
/// refutation over the untouched `Int` development rests on none.
///
/// Both halves are the point. A run where the control came back empty would mean
/// the measurement broke; a run where the `Int` side came back non-empty would
/// mean the axiom-free carrier is not.
#[test]
fn a_refutation_reaches_the_control_axiom_and_nothing_over_the_integers() {
    let (arena, assertions) = baby_farkas();

    let (mut control_ctx, control) =
        LraReconstructCtx::try_new_over_the_control_carrier().expect("the control context builds");
    let proof = reconstruct_lra_proof(&mut control_ctx, &arena, &assertions)
        .expect("the refutation reconstructs over the control carrier");
    let control_footprint = refutation_axiom_footprint(&mut control_ctx, proof)
        .expect("the control refutation is a proof of False");
    assert_eq!(
        carrier_axioms_of(&control_footprint),
        vec![CONTROL_AXIOM_NAME.to_owned()],
        "the control must reach its one axiom and no other carrier assumption"
    );
    assert_eq!(
        control_ctx.kernel().display_name(control.axiom).to_string(),
        CONTROL_AXIOM_NAME
    );

    let (arena, assertions) = baby_farkas();
    let mut honest_ctx =
        LraReconstructCtx::try_new_over_integers().expect("the integer context builds");
    let proof = reconstruct_lra_proof(&mut honest_ctx, &arena, &assertions)
        .expect("the refutation reconstructs over the integers");
    let honest_footprint = refutation_axiom_footprint(&mut honest_ctx, proof)
        .expect("the integer refutation is a proof of False");
    assert!(
        carrier_axioms_of(&honest_footprint).is_empty(),
        "the untouched integer development must reach no carrier axiom: {:?}",
        carrier_axioms_of(&honest_footprint)
    );
    // The two runs really did produce comparable refutations, so the zero above
    // is not the zero of a run that did nothing.
    assert!(!honest_footprint.is_empty());
    assert_eq!(honest_footprint.len() + 1, control_footprint.len());
}

/// The discharge guard, reached: a control built on a law that is **assumed**
/// rather than proved is refused.
///
/// Handed the `AxReal` package's interface, the discharge's value is
/// `AxReal.lt_irrefl`, an axiom — so the control would stand in for an assumption
/// and the trusted base would grow by one rather than merely become visible.
/// Deleting the guard in `control_carrier_over` kills this test and no other
/// (measured; see the lane note).
#[test]
fn a_control_built_on_an_assumed_law_is_refused() {
    use axeyum_lean_kernel::build_arith_prelude;

    use crate::reconstruct::arithmetic::RingSignature;
    use crate::reconstruct::arithmetic::control::control_carrier_over;

    let mut kernel = Kernel::new();
    let arith = build_arith_prelude(&mut kernel).expect("the AxReal package builds");
    let err = control_carrier_over(&mut kernel, RingSignature::from(arith))
        .expect_err("a control standing in for an AXIOM must be refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("is not itself axiom-free"),
        "the refusal must say the discharge failed: {rendered}"
    );
    assert!(
        rendered.contains("AxReal.lt_irrefl"),
        "the refusal must name what the discharge rests on: {rendered}"
    );
}
