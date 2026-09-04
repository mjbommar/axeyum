//! Tests for `creal/omniscience.rs` — roadmap W0-2, what the classical order
//! on ℝ buys when it is carried as a hypothesis rather than admitted as an
//! axiom.
//!
//! In its own file rather than in `creal_tests.rs` because that file is the
//! append point every concurrent `creal` lane collides on; the inventory
//! shards under `creal/inventory/` exist for the same reason.
//!
//! **What these tests have to rule out.** All four declarations are
//! implications, and an implication with a hypothesis nothing can satisfy —
//! or with a conclusion weaker than advertised — type-checks and says
//! nothing. So each test does two things: apply the theorem at a GENUINELY
//! FREE order-decision hypothesis and pin the inferred conclusion verbatim
//! against an independently rebuilt term, then feed the hypothesis slot
//! something else and require rejection.
//!
//! The hypothesis is rebuilt HERE, independently of `omniscience.rs`. If it
//! simply called that module's own private builder, every check would be
//! comparing a term with itself.

use super::creal_tests::built;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, CRealPrelude, Kernel, LocalContext, LocalDecl, on_a_deep_stack};

/// `OrderDecision := ∀ (x y : CReal), Or (lt x y) (le y x)`, rebuilt.
fn order_decision(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = d.kernel().const_(p.creal, vec![]);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let strict = d.const_app(p.lt, &[x, y]);
    let weak = d.const_app(p.le, &[y, x]);
    let body = d.or(strict, weak);
    let with_y = d.pi_fv(y_fv, carrier, body);
    d.pi_fv(x_fv, carrier, with_y)
}

/// The WEAKER decision `∀ x y, Or (le x y) (le y x)` — i.e. `le_total`
/// itself. Used as the negative control: it must NOT discharge the
/// `OrderDecision` slot, because the whole point of the strict-left form is
/// that it is LPO-strength and this one is only LLPO-strength.
fn le_total_shape(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = d.kernel().const_(p.creal, vec![]);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let forward = d.const_app(p.le, &[x, y]);
    let backward = d.const_app(p.le, &[y, x]);
    let body = d.or(forward, backward);
    let with_y = d.pi_fv(y_fv, carrier, body);
    d.pi_fv(x_fv, carrier, with_y)
}

/// Push one free variable of type `ty` into `ctx` and return it.
fn free_of(d: &mut IntDev<'_>, ctx: &mut LocalContext, ty: ExprId) -> ExprId {
    let anon = d.anon_name();
    let fv = d.fresh_fvar();
    ctx.push(LocalDecl {
        fvar: fv,
        name: anon,
        ty,
        info: BinderInfo::Default,
    });
    d.kernel().fvar(fv)
}

/// Two free reals, in a context that also carries a free `OrderDecision`.
fn od_and_two_reals(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    ctx: &mut LocalContext,
) -> (ExprId, ExprId, ExprId) {
    let od_ty = order_decision(d, p);
    let od = free_of(d, ctx, od_ty);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let x = free_of(d, ctx, carrier);
    let y = free_of(d, ctx, carrier);
    (od, x, y)
}

// --- admission and the footprint --------------------------------------------

/// The four names are admitted, all as `Theorem`s, all with an EMPTY
/// `Kernel::axiom_footprint`.
///
/// This is the claim ADR-1601's whole measurement rests on: the classical
/// order enters as a hypothesis, so the trusted base does not move. Read from
/// `axiom_footprint`, never from a rendered name.
#[test]
fn the_order_decision_family_is_admitted_and_axiom_free() {
    on_a_deep_stack(the_order_decision_family_is_admitted_and_axiom_free_body);
}

fn the_order_decision_family_is_admitted_and_axiom_free_body() {
    let (kernel, p) = built();
    let names = [
        p.omniscience.le_total_of_order_decision,
        p.omniscience.trichotomy_of_order_decision,
        p.omniscience.apart_of_not_equiv_of_order_decision,
        p.omniscience.abs_cases_of_order_decision,
    ];
    assert_eq!(
        names.len(),
        4,
        "the W0-2 measurement family has four members"
    );
    for name in names {
        let shown = kernel.display_name(name).to_string();
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{shown} must be admitted"))
            .clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a Theorem, not {decl:?}"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must be axiom-free, found {:?}",
            footprint
                .iter()
                .map(|n| kernel.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

// --- `le_total`, the theorem the field docs say does not exist over ℝ -------

/// `CReal.le_total_of_order_decision` at a free hypothesis and two free reals
/// lands on `Or (le x y) (le y x)` — `CReal.le_total`, exactly.
///
/// NEGATIVE CONTROL: `le_total` itself must NOT discharge the hypothesis
/// slot. The two terms differ in ONE subterm — `lt x y` against `le x y` in
/// the left disjunct — and that difference is the whole strength gap the ADR
/// prices. If the weaker form were accepted here, the theorem would be
/// `le_total → le_total` and would measure nothing.
#[test]
fn le_total_of_order_decision_lands_on_le_total_and_rejects_le_total_as_its_hypothesis() {
    on_a_deep_stack(le_total_of_order_decision_body);
}

fn le_total_of_order_decision_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();
    let (od, x, y) = od_and_two_reals(&mut d, p, &mut ctx);

    let applied = d.lemma(p.omniscience.le_total_of_order_decision, &[od, x, y]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("le_total_of_order_decision must apply at a free hypothesis");

    let forward = d.const_app(p.le, &[x, y]);
    let backward = d.const_app(p.le, &[y, x]);
    let expected = d.or(forward, backward);
    assert!(
        d.kernel().def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (le x y) (le y x)`"
    );

    let weak_ty = le_total_shape(&mut d, p);
    let weak = free_of(&mut d, &mut ctx, weak_ty);
    let bogus = d.lemma(p.omniscience.le_total_of_order_decision, &[weak, x, y]);
    assert!(
        d.kernel().infer_in(bogus, &mut ctx).is_err(),
        "the weaker `Or (le x y) (le y x)` decision must NOT discharge the \
         strict-left `Or (lt x y) (le y x)` hypothesis"
    );
}

// --- trichotomy -------------------------------------------------------------

/// `CReal.trichotomy_of_order_decision` lands on
/// `Or (lt x y) (Or (Equiv x y) (lt y x))`.
///
/// NEGATIVE CONTROL: the `le_total`-shaped decision must be rejected in the
/// hypothesis slot. This is the one that matters mathematically — trichotomy
/// is LPO-strength and `le_total` is only LLPO-strength, so a proof that went
/// through the weaker form would be wrong.
#[test]
fn trichotomy_of_order_decision_lands_on_trichotomy_and_needs_the_strict_decision() {
    on_a_deep_stack(trichotomy_of_order_decision_body);
}

fn trichotomy_of_order_decision_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();
    let (od, x, y) = od_and_two_reals(&mut d, p, &mut ctx);

    let applied = d.lemma(p.omniscience.trichotomy_of_order_decision, &[od, x, y]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("trichotomy_of_order_decision must apply at a free hypothesis");

    let lt_xy = d.const_app(p.lt, &[x, y]);
    let lt_yx = d.const_app(p.lt, &[y, x]);
    let eq_xy = d.const_app(p.equiv, &[x, y]);
    let tail = d.or(eq_xy, lt_yx);
    let expected = d.or(lt_xy, tail);
    assert!(
        d.kernel().def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (lt x y) (Or (Equiv x y) (lt y x))`"
    );

    let weak_ty = le_total_shape(&mut d, p);
    let weak = free_of(&mut d, &mut ctx, weak_ty);
    let bogus = d.lemma(p.omniscience.trichotomy_of_order_decision, &[weak, x, y]);
    assert!(
        d.kernel().infer_in(bogus, &mut ctx).is_err(),
        "trichotomy must NOT be derivable from the `le_total`-shaped decision"
    );
}

// --- the Markov direction on apartness --------------------------------------

/// `CReal.apart_of_not_equiv_of_order_decision` lands on `Apart x y` — the
/// direction `CReal.not_equiv_of_apart`'s own field documentation names as
/// **Markov's principle** and records as neither proved nor assumed.
///
/// NEGATIVE CONTROL: `Equiv x y` must not be accepted where `Not (Equiv x y)`
/// is demanded. That is a one-symbol difference in the premise, and it is the
/// difference between the theorem and its own negation.
#[test]
fn apart_of_not_equiv_lands_on_apart_and_needs_the_negated_premise() {
    on_a_deep_stack(apart_of_not_equiv_body);
}

fn apart_of_not_equiv_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();
    let (od, x, y) = od_and_two_reals(&mut d, p, &mut ctx);

    let eq_xy = d.const_app(p.equiv, &[x, y]);
    let not_name = p.rat.int.logic.not;
    let neq_ty = d.const_app(not_name, &[eq_xy]);
    let neq = free_of(&mut d, &mut ctx, neq_ty);

    let applied = d.lemma(
        p.omniscience.apart_of_not_equiv_of_order_decision,
        &[od, x, y, neq],
    );
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("apart_of_not_equiv_of_order_decision must apply at free hypotheses");

    let expected = d.const_app(p.apart, &[x, y]);
    assert!(
        d.kernel().def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Apart x y`"
    );

    let positive = free_of(&mut d, &mut ctx, eq_xy);
    let bogus = d.lemma(
        p.omniscience.apart_of_not_equiv_of_order_decision,
        &[od, x, y, positive],
    );
    assert!(
        d.kernel().infer_in(bogus, &mut ctx).is_err(),
        "`Equiv x y` must NOT be accepted where `Not (Equiv x y)` is demanded"
    );
}

// --- the `abs` decision -----------------------------------------------------

/// `CReal.abs_cases_of_order_decision` lands on
/// `Or (Equiv (abs x) x) (Equiv (abs x) (neg x))` — the statement
/// `CReal.abs`'s own field documentation marks as "**not** available".
///
/// The conclusion is pinned with `CReal.abs` on both sides, not with
/// `CReal.max x (neg x)`, so the test also confirms the kernel's conversion
/// unfolds `abs` on its own and no bridge lemma is hiding in the statement.
///
/// NEGATIVE CONTROL: `Or (Equiv (abs x) x) (Equiv (abs x) x)` — the same term
/// with `neg x` replaced by `x` in the right disjunct, one subterm — must not
/// be definitionally equal to the inferred conclusion. Without it a theorem
/// that had lost the `neg` would pass.
#[test]
fn abs_cases_of_order_decision_lands_on_the_sign_decision_with_neg_intact() {
    on_a_deep_stack(abs_cases_of_order_decision_body);
}

fn abs_cases_of_order_decision_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let mut ctx = LocalContext::new();
    let od_ty = order_decision(&mut d, p);
    let od = free_of(&mut d, &mut ctx, od_ty);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let x = free_of(&mut d, &mut ctx, carrier);

    let applied = d.lemma(p.omniscience.abs_cases_of_order_decision, &[od, x]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("abs_cases_of_order_decision must apply at a free hypothesis");

    let ax = d.const_app(p.abs, &[x]);
    let nx = d.const_app(p.neg, &[x]);
    let same = d.const_app(p.equiv, &[ax, x]);
    let flipped = d.const_app(p.equiv, &[ax, nx]);
    let expected = d.or(same, flipped);
    assert!(
        d.kernel().def_eq_in(inferred, expected, &mut ctx),
        "conclusion must be `Or (Equiv (abs x) x) (Equiv (abs x) (neg x))`"
    );

    let degenerate = {
        let left = d.const_app(p.equiv, &[ax, x]);
        let right = d.const_app(p.equiv, &[ax, x]);
        d.or(left, right)
    };
    assert!(
        !d.kernel().def_eq_in(inferred, degenerate, &mut ctx),
        "NEGATIVE CONTROL: the right disjunct must mention `neg x`; a \
         conclusion with `x` on both sides decides nothing"
    );
}

// --- the whole point: none of the four is unconditionally available ---------

/// **None of the four conclusions is declared anywhere in the environment
/// without the hypothesis.**
///
/// If `CReal.le_total` (or trichotomy, or the Markov direction, or the `abs`
/// decision) were already a theorem here, every declaration in
/// `creal/omniscience.rs` would be measuring nothing and ADR-1601's cost
/// figure would be meaningless.
///
/// POSITIVE CONTROL: the identical scan run for the type of
/// `CReal.le_total_of_order_decision` must find exactly one declaration, so a
/// scan that has stopped matching anything fails rather than reporting a
/// clean zero.
#[test]
fn no_unconditional_order_decision_is_declared_over_creal() {
    on_a_deep_stack(no_unconditional_order_decision_is_declared_over_creal_body);
}

fn no_unconditional_order_decision_is_declared_over_creal_body() {
    let (mut kernel, p) = built();
    let (le_total_ty, od_ty, control_ty) = {
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let a = le_total_shape(&mut d, p);
        let b = order_decision(&mut d, p);
        let control = {
            let hyp = order_decision(&mut d, p);
            let concl = le_total_shape(&mut d, p);
            d.arrow(hyp, concl)
        };
        (a, b, control)
    };

    let declared: Vec<(crate::NameId, Declaration)> = kernel
        .environment()
        .iter()
        .map(|(name, decl)| (*name, decl.clone()))
        .collect();
    let ty_of = |decl: &Declaration| -> Option<ExprId> {
        match decl {
            Declaration::Theorem { ty, .. }
            | Declaration::Definition { ty, .. }
            | Declaration::Axiom { ty, .. }
            | Declaration::Opaque { ty, .. } => Some(*ty),
            _ => None,
        }
    };
    let holders = |target: ExprId, kernel: &Kernel| -> Vec<String> {
        declared
            .iter()
            .filter(|(_, decl)| ty_of(decl) == Some(target))
            .map(|(name, _)| kernel.display_name(*name).to_string())
            .collect()
    };

    let control = holders(control_ty, &kernel);
    assert_eq!(
        control.len(),
        1,
        "POSITIVE CONTROL: the scan must find exactly \
         `CReal.le_total_of_order_decision` by its type; found {control:?}. A \
         zero here means the scan is broken, not that the principles are absent."
    );

    for (label, ty) in [("le_total", le_total_ty), ("OrderDecision", od_ty)] {
        let found = holders(ty, &kernel);
        assert!(
            found.is_empty(),
            "{label} is already declared unconditionally as {found:?} -- every \
             theorem in `creal/omniscience.rs` would then be measuring nothing"
        );
    }
}
