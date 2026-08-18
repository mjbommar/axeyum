//! Tests for the ordered-ring generalization of an LRA refutation.
//!
//! The claims under test are (1) the generalized theorem's measured axiom
//! footprint is empty, (2) instantiating it at `Real` recovers the original
//! statement, (3) under [`RingTelescope::Used`] the recovery is footprint-exact,
//! and (4) the telescope this module abstracts is *all* of the `Real` package —
//! a 31st axiom cannot slip past it.

use axeyum_ir::{Rational, TermArena, TermId};

use super::{
    RING_BINDER_NAMES, RING_LAW_BINDERS, RING_SYMBOL_BINDERS, RingTelescope,
    generalize_over_ordered_ring, ring_telescope,
};
use crate::reconstruct::arithmetic::{LraReconstructCtx, reconstruct_lra_proof};

/// `x ≤ 0 ∧ 1 ≤ x` — the baby-Farkas order chain, the smallest refutation that
/// reaches the kernel.
fn baby_farkas() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let upper = arena.real_le(x, zero).unwrap();
    let lower = arena.real_le(one, x).unwrap();
    (arena, vec![upper, lower])
}

/// A three-constraint instance over two variables that goes through the general
/// Farkas engine (a ring sum, not a pure order chain), so the generalization is
/// exercised on a proof term that uses the additive laws too.
fn general_farkas() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    // x + y ≤ 0, 1 ≤ x, 1 ≤ y  (the last two sum to a contradiction of the first).
    let sum = arena.real_add(x, y).unwrap();
    let a1 = arena.real_le(sum, zero).unwrap();
    let a2 = arena.real_le(one, x).unwrap();
    let a3 = arena.real_le(one, y).unwrap();
    (arena, vec![a1, a2, a3])
}

/// **The result.** A reconstructed Farkas refutation, parameterised over the
/// ordered-ring interface, has an EMPTY axiom footprint — measured by
/// `Kernel::axiom_footprint`, not asserted — while the un-generalized statement
/// it came from rests on `Real` declarations plus its own variable and
/// hypothesis axioms.
#[test]
fn generalized_refutation_has_an_empty_axiom_footprint() {
    let (arena, assertions) = baby_farkas();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions)
        .expect("baby-Farkas instance reconstructs to False");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("the refutation generalizes");

    assert!(
        generalized.footprint.is_empty(),
        "the ordered-ring refutation must be axiom-free, got {:?}",
        generalized.footprint
    );
    // The baseline is NOT empty, so the assertion above discriminates rather
    // than passing vacuously: 15 Real declarations + 1 variable + 2 hypotheses.
    assert_eq!(
        generalized.original_footprint.len(),
        18,
        "baseline footprint changed: {:?}",
        generalized.original_footprint
    );
    assert_eq!(
        generalized.ring_used.len(),
        15,
        "the baby-Farkas chain uses 15 of the 30 Real declarations: {:?}",
        generalized.ring_used
    );
    assert_eq!(generalized.ring_binders, 30);
    assert_eq!(generalized.var_binders, 1);
    assert_eq!(generalized.hyp_binders, 2);
    assert_eq!(generalized.binder_count(), 30 + 1 + 2);
}

/// **Nothing is lost.** Applying the generalized theorem to the 30 `Real`
/// constants and to the refutation's own variable/hypothesis axioms is a proof
/// of `False` the kernel re-checks, and every axiom the original rested on is
/// back. The generalization is a strengthening, not a different claim.
#[test]
fn instantiating_at_real_recovers_the_original_statement() {
    let (arena, assertions) = baby_farkas();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("generalizes");

    assert!(
        generalized.instantiation_recovers_original(),
        "instantiation footprint {:?} does not cover the original {:?}",
        generalized.instantiated_footprint,
        generalized.original_footprint
    );
    // Under the full interface the instantiation mentions all 30 (the unused
    // laws are supplied and ignored), so the recovery is a superset, not an
    // identity. Stated here rather than left for a reader to be surprised by.
    assert_eq!(
        generalized.instantiated_footprint.len(),
        30 + 1 + 2,
        "{:?}",
        generalized.instantiated_footprint
    );
    assert!(!generalized.instantiation_footprint_is_exact());
}

/// Abstracting only the declarations the proof rests on makes the recovery
/// **footprint-exact**: the instantiated theorem depends on precisely what the
/// original did, name for name.
#[test]
fn used_scope_instantiation_reproduces_the_original_footprint_exactly() {
    let (arena, assertions) = baby_farkas();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs");
    let generalized =
        generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::Used).expect("generalizes");

    assert!(generalized.footprint.is_empty());
    assert_eq!(generalized.ring_binders, 15);
    assert!(
        generalized.instantiation_footprint_is_exact(),
        "instantiated {:?} vs original {:?}",
        generalized.instantiated_footprint,
        generalized.original_footprint
    );
}

/// The same holds for a refutation that needs the ring engine (a Farkas sum),
/// not just the order chain — the generalization is over the interface, not
/// over one proof shape.
#[test]
fn general_farkas_refutation_also_generalizes_axiom_free() {
    let (arena, assertions) = general_farkas();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions)
        .expect("the two-variable Farkas instance reconstructs");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("generalizes");

    assert!(
        generalized.footprint.is_empty(),
        "ring-engine refutation must generalize axiom-free, got {:?}",
        generalized.footprint
    );
    assert!(
        generalized.instantiation_recovers_original(),
        "instantiation must recover the original footprint"
    );
    assert_eq!(generalized.var_binders, 2);
    assert_eq!(generalized.hyp_binders, 3);
}

/// The **sum-of-squares** route generalizes too, and it is the one that matters
/// most for coverage: it is the only reconstructor that reaches `sq_nonneg` and
/// the multiplicative symbols, so without it the generalization would be
/// demonstrated only over the additive/order fragment.
#[test]
fn sum_of_squares_refutation_generalizes_axiom_free() {
    use crate::reconstruct::arithmetic::reconstruct_sos_proof;

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let square = arena.real_mul(x, x).unwrap();
    let negative = arena.real_lt(square, zero).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_sos_proof(&mut ctx, &arena, &[negative])
        .expect("x*x < 0 reconstructs to False");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::Used)
        .expect("the SOS refutation generalizes");

    assert!(
        generalized.footprint.is_empty(),
        "the SOS refutation must generalize axiom-free, got {:?}",
        generalized.footprint
    );
    assert!(
        generalized.ring_used.iter().any(|n| n == "Real.sq_nonneg"),
        "the SOS route must reach sq_nonneg, else this covers nothing new: {:?}",
        generalized.ring_used
    );
    assert!(generalized.instantiation_footprint_is_exact());
}

/// A strict cycle `x < y ∧ y < x` reaches `lt_trans`, which no `≤`-shaped
/// Farkas refutation does.
#[test]
fn strict_cycle_refutation_generalizes_axiom_free() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let a1 = arena.real_lt(x, y).unwrap();
    let a2 = arena.real_lt(y, x).unwrap();

    let mut ctx = LraReconstructCtx::new();
    let proof =
        reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2]).expect("strict cycle reconstructs");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::Used)
        .expect("the strict-cycle refutation generalizes");

    assert!(generalized.footprint.is_empty());
    assert!(
        generalized.ring_used.iter().any(|n| n == "Real.lt_trans"),
        "expected lt_trans in {:?}",
        generalized.ring_used
    );
    assert!(generalized.instantiation_footprint_is_exact());
}

/// The abstraction telescope must cover the **whole** `Real` package. If a 31st
/// declaration is added and not listed here, a refutation using it would keep a
/// non-empty footprint; this fails first, and loudly, at the source.
#[test]
fn the_ring_telescope_is_every_real_declaration() {
    use axeyum_lean_kernel::{Declaration, Kernel, build_arith_prelude};

    let mut kernel = Kernel::new();
    let arith = build_arith_prelude(&mut kernel).expect("Real prelude builds");
    let signature = crate::reconstruct::arithmetic::RingSignature::from(arith);
    let telescope: std::collections::BTreeSet<_> = ring_telescope(&signature).into_iter().collect();
    assert_eq!(telescope.len(), RING_BINDER_NAMES.len());
    assert_eq!(RING_SYMBOL_BINDERS + RING_LAW_BINDERS, telescope.len());

    let declared: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => Some(*name),
            _ => None,
        })
        .filter(|&name| kernel.display_name(name).to_string().starts_with("Real"))
        .collect();
    assert_eq!(
        declared.len(),
        RING_BINDER_NAMES.len(),
        "the Real package is no longer 30 declarations"
    );
    for name in declared {
        assert!(
            telescope.contains(&name),
            "`{}` is a Real axiom the ordered-ring telescope does not abstract",
            kernel.display_name(name)
        );
    }
}

// ---------------------------------------------------------------------------
// ADR-0468 phase R3: the equality slot.
// ---------------------------------------------------------------------------

/// Reconstruct `fixture` twice in one context — once with the kernel's `Eq`,
/// once with the equality slot — generalize each, and specialize the setoid form
/// back at `Eq`.
///
/// One context deliberately: the two statements are then interned in the same
/// kernel, so comparing them is an [`ExprId`] equality (structural identity, no
/// rendering and no definitional-equality check that could accept a reshaped
/// statement).
fn round_trip(
    fixture: (TermArena, Vec<TermId>),
) -> (
    LraReconstructCtx,
    super::OrderedRingRefutation,
    super::OrderedRingRefutation,
    super::EqSpecialization,
) {
    let (arena, assertions) = fixture;
    let mut ctx = LraReconstructCtx::new();
    let eq_proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs");
    let full = generalize_over_ordered_ring(&mut ctx, eq_proof, RingTelescope::FullInterface)
        .expect("the Eq-shaped refutation generalizes");
    ctx.enable_setoid_equality()
        .expect("the equality slot declares");
    let setoid_proof =
        reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs again");
    let setoid =
        generalize_over_ordered_ring(&mut ctx, setoid_proof, RingTelescope::SetoidInterface)
            .expect("the setoid refutation generalizes");
    let specialized =
        super::specialize_setoid_to_eq(&mut ctx, &setoid, &full).expect("specializes at Eq");
    (ctx, full, setoid, specialized)
}

/// **The R3 result.** The 39-binder setoid statement, instantiated at `Eq`,
/// is the very expression the 30-binder statement already is — not merely
/// definitionally equal to it.
///
/// This is what makes widening the interface a *generalization* rather than a
/// silent change of claim: if the rewrite through `eq` had reshaped a law, the
/// specialization would still typecheck (the kernel normalizes) and would still
/// be axiom-free, and only this identity would notice.
#[test]
fn the_setoid_telescope_specializes_back_to_todays_statement() {
    for fixture in [baby_farkas(), general_farkas()] {
        let (ctx, full, setoid, specialized) = round_trip(fixture);
        assert_eq!(
            full.ring_binders,
            RING_BINDER_NAMES.len(),
            "the Eq-shaped telescope is no longer 30"
        );
        assert_eq!(
            setoid.ring_binders,
            super::SETOID_RING_BINDERS,
            "the setoid telescope is not 39"
        );
        assert_eq!(
            setoid.ring_binders,
            full.ring_binders + super::EQUALITY_SLOT_BINDERS,
            "the equality slot did not widen the interface, so reproducing the statement \
             would be the trivial claim that 30 binders reproduce 30 binders"
        );
        assert!(
            specialized.reproduces_reference,
            "instantiating the setoid telescope at Eq did not reproduce today's statement\n\
             at Eq : {}\ntoday : {}",
            specialized.statement_rendered, specialized.reference_rendered
        );
        assert!(
            specialized.binder_type_mismatches.is_empty(),
            "a binder type did not come back verbatim: {:?}",
            specialized.binder_type_mismatches
        );
        assert_eq!(
            specialized.binder_types_reproduced, full.ring_binders,
            "the two telescopes did not line up over all {} non-slot positions, so the \
             comparison above only covered a prefix",
            full.ring_binders
        );
        assert!(
            specialized.footprint.is_empty(),
            "the specialization rests on {:?}",
            specialized.footprint
        );
        drop(ctx);
    }
}

/// The setoid-generalized statement assumes nothing — the same measurement the
/// `Eq`-shaped form already passes, re-run over 39 binders instead of 30.
#[test]
fn the_setoid_generalization_is_axiom_free() {
    let (_ctx, _full, setoid, _specialized) = round_trip(general_farkas());
    assert!(
        setoid.footprint.is_empty(),
        "the setoid generalization rests on {:?}",
        setoid.footprint
    );
    assert!(
        !setoid.original_footprint.is_empty(),
        "the negative control is empty, so the measurement above is vacuous"
    );
}

/// The setoid proof mentions **no** kernel `Eq` constant, and the `Eq`-shaped
/// proof of the same query mentions several.
///
/// The second half is the control that makes the first half a measurement.
/// `Eq`, `Eq.refl` and `Eq.rec` are an inductive, a constructor and a recursor,
/// not axioms, so a proof that kept using them still generalizes to an
/// axiom-free 39-binder theorem — every other number in this module still reads
/// as success — while being uninstantiable at a carrier whose equality is a
/// defined relation, which is the whole point of the slot.
#[test]
fn the_setoid_proof_mentions_no_kernel_equality_and_the_eq_proof_does() {
    let (arena, assertions) = general_farkas();
    let mut ctx = LraReconstructCtx::new();
    let eq_proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs");
    let with_eq = super::residual_eq_constants(&ctx, eq_proof);
    ctx.enable_setoid_equality()
        .expect("the equality slot declares");
    let setoid_proof =
        reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs again");
    let with_slot = super::residual_eq_constants(&ctx, setoid_proof);

    assert!(
        !with_eq.is_empty(),
        "the Eq-shaped proof mentions no equality constant, so the scanner cannot \
         distinguish the two modes and the assertion below proves nothing"
    );
    assert!(
        with_slot.is_empty(),
        "the setoid proof still mentions {with_slot:?}"
    );
}

/// The setoid telescope requires the slot to have been declared **before**
/// reconstruction. Asking for it over an `Eq`-shaped proof is refused rather
/// than generalized over the wrong thing.
#[test]
fn the_setoid_telescope_refuses_an_eq_shaped_proof() {
    let (arena, assertions) = baby_farkas();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("reconstructs");
    let refused = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::SetoidInterface);
    assert!(
        refused.is_err(),
        "a proof built against `Eq` was generalized over the setoid telescope"
    );

    // And once the slot exists, the OLD proof is still refused — it rests on the
    // Eq-shaped `Real` laws, which the setoid telescope does not bind.
    ctx.enable_setoid_equality()
        .expect("the equality slot declares");
    let still_refused =
        generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::SetoidInterface);
    assert!(
        still_refused.is_err(),
        "declaring the slot made an Eq-shaped proof look setoid-shaped"
    );
}

/// The setoid telescope is exactly the `Eq`-shaped one with nine positions
/// added, and the 22 laws keep their relative order — which is what lets the
/// specialization hand the law binders through positionally rather than by name.
#[test]
fn the_setoid_binder_table_extends_the_eq_shaped_one() {
    assert_eq!(super::SETOID_RING_BINDER_NAMES.len(), 39);
    assert_eq!(
        &super::SETOID_RING_BINDER_NAMES[..RING_SYMBOL_BINDERS],
        &RING_BINDER_NAMES[..RING_SYMBOL_BINDERS],
        "the eight carrier/operation binders moved"
    );
    assert_eq!(
        &super::SETOID_RING_BINDER_NAMES[RING_SYMBOL_BINDERS + super::EQUALITY_SLOT_BINDERS..],
        &RING_BINDER_NAMES[RING_SYMBOL_BINDERS..],
        "the 22 law binders are not in the same order in both telescopes"
    );
}
