//! Tests for the ordered-ring signature and the parameterized constructor.
//!
//! Two claims. (1) The `Real` package satisfies the interface this module states
//! independently of `build_arith_prelude`, and the numbers that fall out of the
//! check — carrier universe 1, nine `Eq`-shaped laws — are *measured*. (2) Each
//! of the five guards refuses on its own: every negative test below breaks
//! exactly one guard, so deleting that guard kills exactly that test.

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::{Kernel, build_arith_prelude, build_creal_prelude};

use super::{RingEquality, RingSignature};
use crate::reconstruct::arithmetic::ordered_ring::{RingTelescope, generalize_over_ordered_ring};
use crate::reconstruct::arithmetic::{LraReconstructCtx, reconstruct_lra_proof};

/// A kernel with the `Real` package built, and the package as a signature.
fn real_signature() -> (Kernel, RingSignature) {
    let mut kernel = Kernel::new();
    let arith = build_arith_prelude(&mut kernel).expect("the real prelude builds");
    let sig = RingSignature::from(arith);
    (kernel, sig)
}

/// `x ≤ 0 ∧ 1 ≤ x` — the smallest refutation that reaches the kernel.
fn baby_farkas() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let upper = arena.real_le(x, zero).unwrap();
    let lower = arena.real_le(one, x).unwrap();
    (arena, vec![upper, lower])
}

/// The `Real` package satisfies this module's independent statement of the
/// ordered-ring interface, and the two numbers the check reads out of the kernel
/// are the ones ADR-0456 and ADR-0468 recorded.
#[test]
fn the_real_package_satisfies_the_ring_interface() {
    let (mut kernel, sig) = real_signature();
    let report = sig
        .validate_in(&mut kernel)
        .expect("the Real package is an ordered-ring signature");

    assert_eq!(
        report.carrier_level, 1,
        "`Real : Type` is `Sort 1`; the reconstruction builds `Eq` at that level"
    );
    assert_eq!(
        report.equality_laws,
        vec![
            "Real.add_comm",
            "Real.add_assoc",
            "Real.add_zero",
            "Real.add_neg",
            "Real.mul_comm",
            "Real.mul_assoc",
            "Real.mul_one",
            "Real.mul_zero",
            "Real.left_distrib",
        ],
        "exactly nine of the 22 laws are stated with an equality -- the nine \
         `enable_setoid_equality` restates through the equality slot"
    );
    assert_eq!(sig.declarations().len(), 30);
    assert_eq!(sig.equality, RingEquality::KernelEq);
}

/// Guard 1. A signature naming a declaration the kernel does not have is refused.
#[test]
fn a_signature_entry_absent_from_the_environment_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    let anon = kernel.anon();
    sig.sq_nonneg = kernel.name_str(anon, "never.declared");

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("an undeclared signature entry must be refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("not in this kernel's environment")
            && rendered.contains("never.declared"),
        "the refusal must name the missing declaration, got: {rendered}"
    );
}

/// Guard 2. A "carrier" that is not a type is refused. `Real.zero` is declared,
/// so guard 1 passes and this is the guard under test.
#[test]
fn a_carrier_that_is_not_a_type_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    sig.r = sig.zero;

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("a carrier whose type is not a Sort must be refused");
    assert!(format!("{err:?}").contains("is not a type"), "got: {err:?}");
}

/// Guard 3. An operation whose arity is wrong is refused even though every name
/// is declared and every name is a genuine `Real` symbol.
#[test]
fn an_operation_of_the_wrong_shape_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    // `Real.neg : Real → Real` in the slot that must be `Real → Real → Real`.
    sig.add = sig.neg;

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("a mis-shaped operation must be refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("R -> R -> R") && rendered.contains("Real.neg"),
        "the refusal must name the symbol and the shape it failed, got: {rendered}"
    );
}

/// Guard 4. A law slot holding something that is not a proposition is refused.
#[test]
fn a_law_that_is_not_a_proposition_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    // `Real.add : Real → Real → Real` inhabits `Sort 1`, not `Prop`.
    sig.le_refl = sig.add;

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("a non-Prop law must be refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("do not state a proposition") && rendered.contains("Real.add"),
        "got: {rendered}"
    );
}

/// Guard 5, and the reason [`RingEquality`] is part of the signature rather than
/// an assumption in the code: claiming a *defined* equality over a package whose
/// laws are still stated with the kernel's `Eq` is refused, and the refusal
/// names the offending laws.
///
/// This is precisely the check a `CReal` signature has to pass — its laws are
/// stated with `CReal.Equiv`, and a route that silently accepted `Eq` here would
/// be generalizing over the wrong relation.
#[test]
fn claiming_a_defined_equality_while_the_laws_still_use_eq_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    sig.equality = RingEquality::Defined(sig.le);

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("nine laws still mention `Eq`, which this signature says is not its equality");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("outside the ordered-ring language") && rendered.contains("Eq"),
        "got: {rendered}"
    );
    assert!(
        rendered.contains("Real.add_comm") && rendered.contains("Real.left_distrib"),
        "the refusal must name the offending laws, got: {rendered}"
    );
}

/// The seam carries the real route: a context built through the parameterized
/// constructor — kernel supplied by the caller, carrier named by a signature —
/// reconstructs and generalizes a Farkas refutation identically to
/// [`LraReconstructCtx::new`].
#[test]
fn the_parameterized_constructor_reproduces_the_default_route() {
    let (arena, assertions) = baby_farkas();

    let mut default_ctx = LraReconstructCtx::new();
    let default_proof = reconstruct_lra_proof(&mut default_ctx, &arena, &assertions)
        .expect("baby-Farkas reconstructs");
    let default_general = generalize_over_ordered_ring(
        &mut default_ctx,
        default_proof,
        RingTelescope::FullInterface,
    )
    .expect("it generalizes");

    let (kernel, sig) = real_signature();
    let mut param_ctx = LraReconstructCtx::with_ring_signature(kernel, sig)
        .expect("the Real package is an admissible signature");
    let param_proof = reconstruct_lra_proof(&mut param_ctx, &arena, &assertions)
        .expect("baby-Farkas reconstructs over the supplied signature");
    let param_general =
        generalize_over_ordered_ring(&mut param_ctx, param_proof, RingTelescope::FullInterface)
            .expect("it generalizes");

    assert_eq!(param_general.footprint, default_general.footprint);
    assert!(param_general.footprint.is_empty());
    assert_eq!(param_general.ring_binders, default_general.ring_binders);
    assert_eq!(param_general.var_binders, default_general.var_binders);
    assert_eq!(param_general.hyp_binders, default_general.hyp_binders);
    assert_eq!(param_general.ring_used, default_general.ring_used);
    assert_eq!(
        param_general.instantiated_footprint,
        default_general.instantiated_footprint
    );
    assert_eq!(
        param_general.original_footprint,
        default_general.original_footprint
    );
}

/// The parameterized constructor refuses a bad signature instead of building a
/// context that would mint proof terms over the wrong constants.
#[test]
fn the_parameterized_constructor_refuses_an_invalid_signature() {
    let (mut kernel, mut sig) = real_signature();
    let anon = kernel.anon();
    sig.mul = kernel.name_str(anon, "never.declared");

    LraReconstructCtx::with_ring_signature(kernel, sig)
        .expect_err("a context must not be built over a signature the kernel does not support");
}

/// `try_new` is `new` without the panic, and agrees with it.
#[test]
fn try_new_agrees_with_new() {
    let a = LraReconstructCtx::try_new().expect("the Real package builds");
    let b = LraReconstructCtx::new();
    assert_eq!(a.arith().declarations(), b.arith().declarations());
    assert_eq!(a.equality(), RingEquality::KernelEq);
}

/// **The measurement this seam exists for.** The *constructed* reals satisfy the
/// ordered-ring signature, with `CReal.Equiv` in the equality slot, and nothing
/// about them has to change for the check to pass.
///
/// Read out of the kernel here, not asserted:
///
/// - all five guards pass, so `CReal`'s 30 declarations are a signature the
///   reconstruction context would accept ([`LraReconstructCtx::with_ring_signature`]);
/// - the carrier is `Sort 1` — the *same* universe the reconstruction hard-wires
///   its `Eq`/`Eq.rec` applications at, so that hard-wiring is not an obstacle
///   for this carrier (it would be for any other level);
/// - exactly the same nine laws are stated with `CReal.Equiv` as the `Real`
///   package states with `Eq Real`, which is what makes the 39-binder setoid
///   telescope the right shape to instantiate at.
///
/// What this does *not* yet show is that a refutation reconstructs over it: the
/// proof-term route still mints its equality slot by declaring axioms and
/// restating the `Real` laws (`enable_setoid_equality`), and `CReal` needs those
/// slots *adopted* from `CRealPrelude` instead. That is the next slice, and this
/// test is its precondition.
#[test]
fn the_constructed_reals_satisfy_the_ring_signature() {
    let (mut kernel, sig) = creal_signature();
    let report = sig
        .validate_in(&mut kernel)
        .expect("CReal is an ordered-ring signature with CReal.Equiv as its equality");

    assert_eq!(
        report.carrier_level, 1,
        "`CReal : Type` is `Sort 1`, like `Real` -- the universe the reconstruction \
         builds `Eq` at"
    );
    assert_eq!(
        report.equality_laws,
        vec![
            "CReal.add_comm",
            "CReal.add_assoc",
            "CReal.add_zero",
            "CReal.add_neg",
            "CReal.mul_comm",
            "CReal.mul_assoc",
            "CReal.mul_one",
            "CReal.mul_zero",
            "CReal.left_distrib",
        ],
        "the same nine laws that the Real package states with `Eq` are the nine \
         CReal states with `Equiv`"
    );
}

/// The same signature, but claiming the kernel's `Eq` is its equality, is
/// refused: `CReal`'s nine laws are stated over `CReal.Equiv`, which under
/// [`RingEquality::KernelEq`] is a constant outside the ring language.
///
/// The discrimination that keeps the test above from being vacuous — guard 5
/// really is reading `CReal.Equiv` out of those statements.
#[test]
fn the_constructed_reals_are_refused_when_the_signature_claims_kernel_eq() {
    let (mut kernel, mut sig) = creal_signature();
    sig.equality = RingEquality::KernelEq;

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("CReal's laws are not stated with the kernel's `Eq`");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("outside the ordered-ring language") && rendered.contains("CReal.Equiv"),
        "got: {rendered}"
    );
}

/// The constructed reals as a [`RingSignature`], built entirely out of
/// [`CRealPrelude`](axeyum_lean_kernel::CRealPrelude) — no `Real` package in
/// this kernel at all.
fn creal_signature() -> (Kernel, RingSignature) {
    let mut kernel = Kernel::new();
    let c = build_creal_prelude(&mut kernel).expect("the CReal development builds");
    let sig = RingSignature {
        // `CRealPrelude` has no `logic` field; the propositional prelude is
        // three hops down its rational/integer tower.
        logic: c.rat.int.logic,
        equality: RingEquality::Defined(c.equiv),
        r: c.creal,
        add: c.add,
        mul: c.mul,
        neg: c.neg,
        zero: c.zero,
        one: c.one,
        le: c.le,
        lt: c.lt,
        le_refl: c.le_refl,
        le_trans: c.le_trans,
        lt_irrefl: c.lt_irrefl,
        lt_trans: c.lt_trans,
        lt_of_lt_of_le: c.lt_of_lt_of_le,
        lt_of_le_of_lt: c.lt_of_le_of_lt,
        le_of_lt: c.le_of_lt,
        add_le_add: c.add_le_add,
        add_comm: c.add_comm,
        add_assoc: c.add_assoc,
        add_zero: c.add_zero,
        add_neg: c.add_neg,
        mul_le_mul_of_nonneg_left: c.mul_le_mul_of_nonneg_left,
        zero_lt_one: c.zero_lt_one,
        add_lt_add_of_le_of_lt: c.add_lt_add_of_le_of_lt,
        mul_comm: c.mul_comm,
        mul_assoc: c.mul_assoc,
        mul_one: c.mul_one,
        mul_zero: c.mul_zero,
        left_distrib: c.left_distrib,
        mul_nonneg: c.mul_nonneg,
        sq_nonneg: c.sq_nonneg,
    };
    (kernel, sig)
}
