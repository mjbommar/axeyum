//! Tests for the ordered-ring signature and the parameterized constructor.
//!
//! Three claims. (1) The `AxReal` package satisfies the interface this module
//! states independently of `build_arith_prelude`, and the numbers that fall out
//! of the check — carrier universe 1, nine `Eq`-shaped laws — are *measured*.
//! (2) Each of the five guards refuses on its own: every negative test below
//! breaks exactly one guard, so deleting that guard kills exactly that test.
//! (3) The **constructed** reals are a carrier this route reconstructs over: the
//! equality slot is adopted from `CRealPrelude` at a measured cost of zero new
//! declarations, and the resulting Farkas refutation's Lean module mentions no
//! `AxReal` declaration at all.

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::{
    CRealPrelude, Kernel, NameId, build_arith_prelude, build_creal_prelude,
    build_int_model_of_arith, build_int_prelude,
};

use super::{RingEquality, RingSignature, SIGNATURE_LAWS, SIGNATURE_SYMBOLS};
use crate::reconstruct::arithmetic::ordered_ring::setoid::EqualitySlot;
use crate::reconstruct::arithmetic::ordered_ring::{
    EQUALITY_SLOT_BINDERS, RingTelescope, generalize_over_ordered_ring, render_ordered_ring_module,
    residual_eq_constants,
};
use crate::reconstruct::arithmetic::{LraReconstructCtx, reconstruct_lra_proof};

/// A kernel with the `AxReal` package built, and the package as a signature.
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

/// The `AxReal` package satisfies this module's independent statement of the
/// ordered-ring interface, and the two numbers the check reads out of the kernel
/// are the ones ADR-0456 and ADR-0512 recorded.
#[test]
fn the_real_package_satisfies_the_ring_interface() {
    let (mut kernel, sig) = real_signature();
    let report = sig
        .validate_in(&mut kernel)
        .expect("the AxReal package is an ordered-ring signature");

    assert_eq!(
        report.carrier_level, 1,
        "`AxReal : Type` is `Sort 1`; the reconstruction builds `Eq` at that level"
    );
    assert_eq!(
        report.equality_laws,
        vec![
            "AxReal.add_comm",
            "AxReal.add_assoc",
            "AxReal.add_zero",
            "AxReal.add_neg",
            "AxReal.mul_comm",
            "AxReal.mul_assoc",
            "AxReal.mul_one",
            "AxReal.mul_zero",
            "AxReal.left_distrib",
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

/// Guard 2. A "carrier" that is not a type is refused. `AxReal.zero` is declared,
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
/// is declared and every name is a genuine `AxReal` symbol.
#[test]
fn an_operation_of_the_wrong_shape_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    // `AxReal.neg : AxReal → AxReal` in the slot that must be `AxReal → AxReal → AxReal`.
    sig.add = sig.neg;

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("a mis-shaped operation must be refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("R -> R -> R") && rendered.contains("AxReal.neg"),
        "the refusal must name the symbol and the shape it failed, got: {rendered}"
    );
}

/// Guard 4. A law slot holding something that is not a proposition is refused.
#[test]
fn a_law_that_is_not_a_proposition_is_refused() {
    let (mut kernel, mut sig) = real_signature();
    // `AxReal.add : AxReal → AxReal → AxReal` inhabits `Sort 1`, not `Prop`.
    sig.le_refl = sig.add;

    let err = sig
        .validate_in(&mut kernel)
        .expect_err("a non-Prop law must be refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("do not state a proposition") && rendered.contains("AxReal.add"),
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
        rendered.contains("AxReal.add_comm") && rendered.contains("AxReal.left_distrib"),
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
        .expect("the AxReal package is an admissible signature");
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
    let a = LraReconstructCtx::try_new().expect("the AxReal package builds");
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
/// - exactly the same nine laws are stated with `CReal.Equiv` as the `AxReal`
///   package states with `Eq AxReal`, which is what makes the 39-binder setoid
///   telescope the right shape to instantiate at.
///
/// What this does *not* yet show is that a refutation reconstructs over it: the
/// proof-term route still mints its equality slot by declaring axioms and
/// restating the `AxReal` laws (`enable_setoid_equality`), and `CReal` needs those
/// slots *adopted* from `CRealPrelude` instead. That is the next slice, and this
/// test is its precondition.
#[test]
fn the_constructed_reals_satisfy_the_ring_signature() {
    let (mut kernel, sig, _slot) = creal_signature();
    let report = sig
        .validate_in(&mut kernel)
        .expect("CReal is an ordered-ring signature with CReal.Equiv as its equality");

    assert_eq!(
        report.carrier_level, 1,
        "`CReal : Type` is `Sort 1`, like `AxReal` -- the universe the reconstruction \
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
        "the same nine laws that the AxReal package states with `Eq` are the nine \
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
    let (mut kernel, mut sig, _slot) = creal_signature();
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

/// The constructed reals as a [`RingSignature`] plus the [`EqualitySlot`] that
/// `CRealPrelude` already proves, built entirely out of
/// [`CRealPrelude`](axeyum_lean_kernel::CRealPrelude) — no `AxReal` package in
/// this kernel at all.
fn creal_signature() -> (Kernel, RingSignature, EqualitySlot) {
    // Built ONCE per process and cloned, for the same reason and on the same
    // argument as `prelude_cache` (ADR-0464): a clone is a bit-exact copy of a
    // state this caller could have reached itself, and no declaration enters an
    // environment by any route other than `Kernel::add_declaration`. Measured
    // 2026-08-18, one `build_creal_prelude` costs ~45 s in a debug test binary,
    // and this file wants eight of them.
    static TEMPLATE: std::sync::OnceLock<(Kernel, CRealPrelude)> = std::sync::OnceLock::new();
    let (template, c) = TEMPLATE.get_or_init(|| {
        let mut kernel = Kernel::new();
        let c = build_creal_prelude(&mut kernel).expect("the CReal development builds");
        (kernel, c)
    });
    let kernel = template.clone();
    let c = *c;
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
    // Every one of the nine is `CRealPrelude`'s own theorem; none is minted
    // here, which is what `declarations_added == 0` below measures.
    let slot = EqualitySlot {
        eq: c.equiv,
        eq_refl: c.equiv_refl,
        eq_symm: c.equiv_symm,
        eq_trans: c.equiv_trans,
        add_congr: c.add_congr,
        mul_congr: c.mul_congr,
        neg_congr: c.neg_congr,
        le_congr: c.le_congr,
        lt_congr: c.lt_congr,
    };
    (kernel, sig, slot)
}

// ===========================================================================
// ADR-0512 phase R4: the equality slot, ADOPTED from the constructed reals.
// ===========================================================================

/// A `CReal` reconstruction context with the equality slot adopted, plus the
/// adoption report.
fn creal_ctx() -> (LraReconstructCtx, crate::reconstruct::SetoidAdoption) {
    let (kernel, sig, slot) = creal_signature();
    let mut ctx = LraReconstructCtx::with_ring_signature(kernel, sig)
        .expect("CReal is an admissible ordered-ring signature");
    let report = ctx
        .adopt_setoid_equality(&slot)
        .expect("CRealPrelude proves every member of the equality slot");
    (ctx, report)
}

/// **The measurement this slice exists for.** Filling the equality slot from
/// `CRealPrelude` adds **zero** declarations to the kernel, against eighteen for
/// the `AxReal` route that has to axiomatize it.
///
/// Both numbers are read out of `Environment::len` before and after, not
/// asserted. The `AxReal` figure is the control: without it, "adoption is free"
/// would be a claim about a number nothing else produces.
#[test]
fn adopting_the_slot_from_the_constructed_reals_declares_nothing() {
    let (_ctx, report) = creal_ctx();

    assert_eq!(
        report.declarations_added, 0,
        "adoption must not add to the trusted base; it took CRealPrelude's own theorems"
    );
    assert_eq!(report.relation, "CReal.Equiv");
    assert_eq!(report.members_checked.len(), EQUALITY_SLOT_BINDERS);
    assert_eq!(
        report.members_checked,
        vec![
            "CReal.Equiv",
            "CReal.Equiv.refl",
            "CReal.Equiv.symm",
            "CReal.Equiv.trans",
            "CReal.add_congr",
            "CReal.mul_congr",
            "CReal.neg_congr",
            "CReal.le_congr",
            "CReal.lt_congr",
        ]
    );
    assert_eq!(
        report.laws_from_signature,
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
        "the nine Eq-shaped ring laws come from the signature, not from the caller"
    );

    // The control: the same slot over `AxReal`, which cannot prove any of it.
    let mut real_ctx = LraReconstructCtx::new();
    let before = real_ctx.kernel().environment().len();
    real_ctx
        .enable_setoid_equality()
        .expect("the AxReal route declares the slot");
    let declared = real_ctx.kernel().environment().len() - before;
    assert_eq!(
        declared, 18,
        "the AxReal route mints nine slot members plus nine restated laws as AXIOMS"
    );
}

/// **The payoff.** A Farkas refutation reconstructs over the *constructed*
/// reals, generalizes over the 39-binder setoid interface, and comes back to a
/// closed `False` whose axiom footprint contains **no `AxReal` declaration and no
/// `CReal` declaration** — only the query's own variable and hypothesis axioms.
///
/// Every number below is read out of the kernel:
///
/// - the generalized theorem's footprint is empty (`generalize_over_ordered_ring`
///   refuses to return otherwise, so this is a redundant read, not the check);
/// - the *instantiated* `False` — the one that mentions the carrier — has a
///   footprint containing nothing from the `AxReal` package and nothing from the
///   `CReal` development, because the construction has no trusted surface to
///   contribute;
/// - the proof term mentions no kernel `Eq` constant at the carrier, which is
///   what made a defined equality admissible in the first place;
/// - the rendered Lean module contains no `AxReal`.
#[test]
fn a_farkas_refutation_reconstructs_over_the_constructed_reals() {
    let (arena, assertions) = baby_farkas();
    let (mut ctx, _) = creal_ctx();

    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions)
        .expect("baby-Farkas reconstructs over CReal");
    assert!(
        residual_eq_constants(&ctx, proof).is_empty(),
        "the proof term must mention no kernel `Eq` constant, or a defined equality \
         could not interpret it"
    );

    let general = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::SetoidInterface)
        .expect("it generalizes over the 39-binder setoid interface");
    assert_eq!(general.ring_binders, 39);
    assert!(general.footprint.is_empty());

    // The instantiation at CReal is the closed `False`. This is where an `AxReal`
    // dependency would show up if one had survived.
    let carrier_axioms: Vec<&String> = general
        .instantiated_footprint
        .iter()
        .filter(|n| n.starts_with("AxReal") || n.starts_with("CReal"))
        .collect();
    assert!(
        carrier_axioms.is_empty(),
        "the closed refutation over CReal must rest on no carrier axiom; got {carrier_axioms:?} \
         out of {:?}",
        general.instantiated_footprint
    );
    assert!(
        !general.instantiated_footprint.is_empty(),
        "it does still rest on the query's own variable/hypothesis axioms -- an empty \
         footprint here would mean the fixture stopped asserting anything"
    );

    let module = render_ordered_ring_module(&ctx, &general);
    assert!(
        !module.contains("AxReal"),
        "the emitted Lean module still names the AxReal package"
    );
}

/// Guard 1: a signature whose equality is the kernel's `Eq` has no relation to
/// adopt, and says so rather than accepting a slot over the wrong thing.
#[test]
fn adopting_a_slot_over_the_kernels_own_eq_is_refused() {
    let (_kernel, _sig, slot) = creal_signature();
    let mut real_ctx = LraReconstructCtx::new();

    let err = real_ctx
        .adopt_setoid_equality(&slot)
        .expect_err("the AxReal package's equality is `Eq`, not a declared relation");
    assert!(
        format!("{err:?}").contains("there is no slot to adopt"),
        "got: {err:?}"
    );
}

/// Guard 2: a slot whose relation is not the one the signature's nine laws are
/// stated over is refused — congruences of some other relation prove nothing
/// about the ring laws.
#[test]
fn adopting_a_slot_for_a_different_relation_is_refused() {
    let (kernel, sig, mut slot) = creal_signature();
    slot.eq = sig.le;
    let mut ctx = LraReconstructCtx::with_ring_signature(kernel, sig)
        .expect("CReal is an admissible signature");

    let err = ctx
        .adopt_setoid_equality(&slot)
        .expect_err("`CReal.le` is not the equality CReal's laws are stated over");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("this signature's laws are stated over") && rendered.contains("CReal.le"),
        "got: {rendered}"
    );
}

/// Guard 3: a slot member that is not declared in this kernel is refused before
/// any type is read.
#[test]
fn adopting_a_slot_with_an_undeclared_member_is_refused() {
    let (mut kernel, sig, mut slot) = creal_signature();
    let anon = kernel.anon();
    slot.eq_symm = kernel.name_str(anon, "never.declared");
    let mut ctx = LraReconstructCtx::with_ring_signature(kernel, sig)
        .expect("CReal is an admissible signature");

    let err = ctx
        .adopt_setoid_equality(&slot)
        .expect_err("an absent slot member must not be adopted");
    assert!(
        format!("{err:?}").contains("not in this kernel's environment"),
        "got: {err:?}"
    );
}

/// Guard 4: a slot member with the wrong *shape* is refused. Swapping the `le`
/// and `lt` congruences keeps both members present, declared, and true — and
/// makes each of them a congruence of the other relation, which is exactly the
/// error a name-only check waves through.
#[test]
fn adopting_a_slot_whose_member_has_the_wrong_shape_is_refused() {
    let (kernel, sig, mut slot) = creal_signature();
    core::mem::swap(&mut slot.le_congr, &mut slot.lt_congr);
    let mut ctx = LraReconstructCtx::with_ring_signature(kernel, sig)
        .expect("CReal is an admissible signature");

    let err = ctx
        .adopt_setoid_equality(&slot)
        .expect_err("`lt_congr` is not a congruence for `le`");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("do not have the interface's type")
            && rendered.contains("le_congr")
            && rendered.contains("lt_congr"),
        "got: {rendered}"
    );
}

/// Guard 5: a context that already has an equality slot refuses a second one —
/// two relations playing equality in one proof term is not a configuration.
#[test]
fn adopting_a_second_equality_slot_is_refused() {
    let (_kernel, _sig, slot) = creal_signature();
    let (mut ctx, _) = creal_ctx();

    let err = ctx
        .adopt_setoid_equality(&slot)
        .expect_err("one context, one equality");
    assert!(
        format!("{err:?}").contains("already has an equality slot"),
        "got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// The constructed **integers** as the third instance of the interface.
// ---------------------------------------------------------------------------

/// A kernel with the `Int` development built, and it as a signature.
///
/// Built once per process and cloned by `PreludeKey::Int` for the same reason
/// `creal_signature` is; `Int` is far cheaper than `CReal` but not free.
fn int_signature() -> (Kernel, RingSignature) {
    let mut kernel = Kernel::new();
    let int = build_int_prelude(&mut kernel).expect("the integer development builds");
    let sig = RingSignature::from(int);
    (kernel, sig)
}

/// `ℤ` satisfies the interface **at the kernel's own `Eq`** — the combination
/// neither of the other two instances offers.
///
/// `AxReal` has kernel equality and costs 30 axioms; `CReal` costs nothing and
/// has a *defined* equality. This is the third corner: nothing assumed, and the
/// nine `Eq`-shaped laws really are stated with `Eq`, so a consumer that wants
/// `Eq.rec` transport back does not have to go through the equality slot.
#[test]
fn the_integers_satisfy_the_ring_signature_at_kernel_equality() {
    let (mut kernel, sig) = int_signature();
    assert_eq!(
        sig.equality,
        RingEquality::KernelEq,
        "ℤ is a one-constructor inductive with no setoid over it, so `Eq Int` IS its equality"
    );

    let report = sig
        .validate_in(&mut kernel)
        .expect("the Int development is an ordered-ring signature");

    assert_eq!(
        report.carrier_level, 1,
        "`Int : Type` is `Sort 1`, like `AxReal` and `CReal`"
    );
    assert_eq!(
        report.equality_laws,
        vec![
            "Int.add_comm",
            "Int.add_assoc",
            "Int.add_zero",
            "Int.add_neg",
            "Int.mul_comm",
            "Int.mul_assoc",
            "Int.mul_one",
            "Int.mul_zero",
            "Int.left_distrib",
        ],
        "the same nine laws the AxReal package states with `Eq`, stated with `Eq` here too"
    );
}

/// **The number this instance exists for.** All 30 of the integer signature's
/// declarations have an *empty* axiom footprint; all 30 of the `AxReal`
/// package's do not.
///
/// The `AxReal` column is the negative control in the same test: without it an
/// empty-footprint assertion would pass just as happily against a kernel where
/// `axiom_footprint` had stopped reporting anything.
#[test]
fn the_integer_signature_assumes_nothing_and_the_real_package_assumes_thirty() {
    let (kernel, sig) = int_signature();
    let assumed: Vec<String> = sig
        .symbols()
        .into_iter()
        .chain(sig.laws())
        .filter(|&n| !kernel.axiom_footprint(n).is_empty())
        .map(|n| kernel.display_name(n).to_string())
        .collect();
    assert!(
        assumed.is_empty(),
        "the integer instance of the interface must assume nothing; these do: {assumed:?}"
    );

    let (real_kernel, real_sig) = real_signature();
    let real_assumed: Vec<String> = real_sig
        .symbols()
        .into_iter()
        .chain(real_sig.laws())
        .filter(|&n| !real_kernel.axiom_footprint(n).is_empty())
        .map(|n| real_kernel.display_name(n).to_string())
        .collect();
    assert_eq!(
        real_assumed.len(),
        30,
        "the control: every one of the AxReal package's 30 declarations is its own assumption, \
         so the measurement above is reading something real; got {real_assumed:?}"
    );
}

/// **The mapping is not taken on trust.** Field by field, the 30 names
/// `From<IntPrelude>` picks are exactly the ones the kernel's own
/// `build_int_model_of_arith` proved model the corresponding `AxReal`
/// declaration.
///
/// That model admits, for each `AxReal` law, a witness whose type is the
/// *computed* interpretation of the axiom and whose proof is the paired `Int`
/// theorem — so the kernel refused it unless ℤ really satisfies that law. This
/// test says the signature reads the same pairing. Without it a transposed
/// field (`le_refl := Int.le_trans`) still validates — both are propositions in
/// the ring language — and only a fixture that happens to use the transposed
/// law would notice.
#[test]
fn the_integer_signature_is_the_kernel_checked_model_field_for_field() {
    let mut kernel = Kernel::new();
    let model = build_int_model_of_arith(&mut kernel).expect("the Int model of AxReal builds");

    let real_sig = RingSignature::from(model.arith);
    let int_sig = RingSignature::from(model.int);

    let expected: Vec<(NameId, NameId)> = model
        .symbols
        .iter()
        .copied()
        .chain(model.laws.iter().map(|law| (law.real, law.int)))
        .collect();
    assert_eq!(
        expected.len(),
        SIGNATURE_SYMBOLS + SIGNATURE_LAWS,
        "the model must account for all 30 positions"
    );

    let actual: Vec<(NameId, NameId)> = real_sig
        .symbols()
        .into_iter()
        .chain(real_sig.laws())
        .zip(int_sig.symbols().into_iter().chain(int_sig.laws()))
        .collect();

    let mismatched: Vec<(String, String, String)> = expected
        .iter()
        .zip(&actual)
        .filter(|(want, got)| want != got)
        .map(|(want, got)| {
            (
                kernel.display_name(want.0).to_string(),
                kernel.display_name(want.1).to_string(),
                kernel.display_name(got.1).to_string(),
            )
        })
        .collect();
    assert!(
        mismatched.is_empty(),
        "the signature's Int name disagrees with the kernel-checked model \
         (AxReal law, model's Int theorem, signature's pick): {mismatched:?}"
    );
}

/// A Farkas refutation reconstructs in a context built by
/// [`LraReconstructCtx::try_new_over_integers`], generalizes over the 30-binder
/// interface, and the *instantiated* `False` rests on **no carrier axiom** —
/// with the kernel's `Eq` still doing the equality reasoning.
///
/// The `CReal` payoff test above proves the same thing through the equality
/// slot (39 binders, no `Eq` in the term). This one keeps `Eq` and still reaches
/// zero, which is what makes the `AxReal` package replaceable in the consumers
/// that are not about ℝ.
#[test]
fn a_farkas_refutation_reconstructs_over_the_integers() {
    let (arena, assertions) = baby_farkas();
    let mut ctx = LraReconstructCtx::try_new_over_integers().expect("the integer context builds");

    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions)
        .expect("baby-Farkas reconstructs over the integers");

    let general = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("it generalizes over the 30-binder interface");
    assert_eq!(general.ring_binders, 30);
    assert!(general.footprint.is_empty());

    let carrier_axioms: Vec<&String> = general
        .instantiated_footprint
        .iter()
        .filter(|n| n.starts_with("AxReal") || n.starts_with("Int"))
        .collect();
    assert!(
        carrier_axioms.is_empty(),
        "the closed refutation over ℤ must rest on no carrier axiom; got {carrier_axioms:?} \
         out of {:?}",
        general.instantiated_footprint
    );
    assert!(
        !general.instantiated_footprint.is_empty(),
        "it does still rest on the query's own variable/hypothesis axioms"
    );

    let module = render_ordered_ring_module(&ctx, &general);
    assert!(
        !module.contains("AxReal"),
        "the emitted Lean module still names the AxReal package"
    );
}
