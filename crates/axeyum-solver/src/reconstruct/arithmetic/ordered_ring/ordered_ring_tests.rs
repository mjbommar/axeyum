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
    let telescope: std::collections::BTreeSet<_> = ring_telescope(&arith).into_iter().collect();
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
