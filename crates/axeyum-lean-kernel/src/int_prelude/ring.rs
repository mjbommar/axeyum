//! `Int.IsCommRing` — the `rings` curriculum node (`docs/curriculum/02-structures/rings.md`),
//! the missing rung between `groups` (`nat_prelude::group::Nat.IsGroupOn`) and
//! `fields` (`rat_prelude::field::Rat.IsField`).
//!
//! ## Why over `Int`, not `Rat`
//!
//! `Rat` already satisfies `IsField`, and the whole content of "ring but not a
//! field" is what `ℤ` has that `ℚ` does not: no multiplicative inverses, and —
//! as a strictly stronger fact than "not a field" — genuinely **no** general
//! division, yet still an *integral domain* (`Int.mul_eq_zero`, `sign.rs`). `ℤ`
//! is the node's canonical teaching instance for exactly that reason.
//!
//! ## Why this is NOT `Rat.IsField` with `inv`/`one_ne_zero` dropped
//!
//! It is that shape, but it cannot be *the same declaration* with two leaves
//! removed, and not only because the carrier differs (`Int` vs `Rat`). This
//! kernel has no typeclasses, no structures and no polymorphism over a bound
//! carrier type — `nat_prelude::group::Nat.IsGroupOn` is one Rust function
//! generating one `Prop` for `Nat`, and `rat_prelude::field::Rat.IsField` is a
//! second, independent one for `Rat`, sharing nothing but a hand-written
//! resemblance. So `Int.IsCommRing` is a **third** copy of the same shape, one
//! prefix shorter than `IsField`'s, over `Int`'s own `Eq`/operations. Composing
//! `Rat.IsField := Int.IsCommRing ∧ (…)` the way `rat_prelude::field`'s
//! `IsOrderedField` composes from `IsField` is not available here: that
//! composition works because both sides are propositions **about the same
//! bound operations over the same carrier** (`Rat`, `Rat.add`, `Rat.mul`, …);
//! `Int.IsCommRing`'s leaves are stated over `Int`, so an application
//! `Int.IsCommRing Rat.add Rat.mul …` is a straight type error (`Rat.add : Rat
//! → Rat → Rat`, not `Int → Int → Int`).
//!
//! ## What's declared
//!
//! - `Int.IsCommRing (add mul : Int → Int → Int) (neg : Int → Int) (zero one :
//!   Int) : Prop := add_comm ∧ (add_assoc ∧ (add_zero ∧ (add_neg ∧ (mul_comm ∧
//!   (mul_assoc ∧ (mul_one ∧ distrib))))))` — `Rat.IsField`'s own first eight
//!   leaves verbatim (right-nested `And`, the same packing convention), minus
//!   the two leaves that make a ring a field (`one_ne_zero`, `inv_cancel`).
//!   Like `IsField`/`IsGroupOn`, every operation is a caller-supplied free
//!   variable, and there is no closure condition: `Int` (like `Rat`, like
//!   `Nat.IsGroupOn`'s bounded `{0,…,n-1}`) is already the whole carrier, so
//!   every operation is already total on it.
//! - `Int.int_isCommRing : Int.IsCommRing Int.add Int.mul Int.neg Int.zero
//!   Int.one` — the worked instance, assembled entirely from the eight ring
//!   laws this development already proved before this module existed
//!   (`algebra.rs`/`sign.rs`): `add_comm`, `add_assoc`, `add_zero`, `add_neg`,
//!   `mul_comm`, `mul_assoc`, `mul_one`, `left_distrib`. Every leaf proof is a
//!   bare reference to an existing constant, exactly
//!   `rat_prelude::field::declare_rat_is_field`'s pattern — no new algebra.
//!
//! ## Status
//!
//! Both declared here and axiom-free (`derived_laws` in
//! `int_prelude_tests.rs`).

use super::IntPrelude;
use super::ops::IntDev;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.IsCommRing`: above every height this prelude uses
/// elsewhere (`wilson::INVERSE_INDEX_HEIGHT` is the previous high point, 25),
/// following the same "single monotone sequence over the whole prelude"
/// convention `rat_prelude::field::FIELD_HEIGHT` documents — even though, as
/// there, `IsCommRing`'s value never unfolds through a named `Definition` (its
/// five operations are caller-supplied free variables, never called), so no
/// earlier height is actually reachable from it.
const RING_HEIGHT: u16 = 26;

/// `Int → Int → Int`.
fn ring_binop_ty(d: &mut IntDev<'_>) -> ExprId {
    let z = d.int_ty();
    let inner = d.arrow(z, z);
    d.arrow(z, inner)
}

/// `Int → Int`.
fn ring_unop_ty(d: &mut IntDev<'_>) -> ExprId {
    let z = d.int_ty();
    d.arrow(z, z)
}

/// `∀ a b, add a b = add b a`.
fn ring_add_comm_prop(d: &mut IntDev<'_>, add: ExprId) -> ExprId {
    let z = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ab = d.apply(add, &[a, b]);
    let ba = d.apply(add, &[b, a]);
    let eq = d.ieq(ab, ba);
    let with_b = d.pi_fv(b_fv, z, eq);
    d.pi_fv(a_fv, z, with_b)
}

/// `∀ a b c, add (add a b) c = add a (add b c)`.
fn ring_add_assoc_prop(d: &mut IntDev<'_>, add: ExprId) -> ExprId {
    let z = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ab = d.apply(add, &[a, b]);
    let ab_c = d.apply(add, &[ab, c]);
    let bc = d.apply(add, &[b, c]);
    let a_bc = d.apply(add, &[a, bc]);
    let eq = d.ieq(ab_c, a_bc);
    let with_c = d.pi_fv(c_fv, z, eq);
    let with_b = d.pi_fv(b_fv, z, with_c);
    d.pi_fv(a_fv, z, with_b)
}

/// `∀ a, add a zero = a`.
fn ring_add_zero_prop(d: &mut IntDev<'_>, add: ExprId, zero: ExprId) -> ExprId {
    let z = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let az = d.apply(add, &[a, zero]);
    let eq = d.ieq(az, a);
    d.pi_fv(a_fv, z, eq)
}

/// `∀ a, add a (neg a) = zero`.
fn ring_add_neg_prop(d: &mut IntDev<'_>, add: ExprId, neg: ExprId, zero: ExprId) -> ExprId {
    let z = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let na = d.apply(neg, &[a]);
    let a_na = d.apply(add, &[a, na]);
    let eq = d.ieq(a_na, zero);
    d.pi_fv(a_fv, z, eq)
}

/// `∀ a b, mul a b = mul b a`.
fn ring_mul_comm_prop(d: &mut IntDev<'_>, mul: ExprId) -> ExprId {
    ring_add_comm_prop(d, mul)
}

/// `∀ a b c, mul (mul a b) c = mul a (mul b c)`.
fn ring_mul_assoc_prop(d: &mut IntDev<'_>, mul: ExprId) -> ExprId {
    ring_add_assoc_prop(d, mul)
}

/// `∀ a, mul a one = a`.
fn ring_mul_one_prop(d: &mut IntDev<'_>, mul: ExprId, one: ExprId) -> ExprId {
    ring_add_zero_prop(d, mul, one)
}

/// `∀ a b c, mul a (add b c) = add (mul a b) (mul a c)`.
fn ring_distrib_prop(d: &mut IntDev<'_>, add: ExprId, mul: ExprId) -> ExprId {
    let z = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let bc = d.apply(add, &[b, c]);
    let left = d.apply(mul, &[a, bc]);
    let ab = d.apply(mul, &[a, b]);
    let ac = d.apply(mul, &[a, c]);
    let right = d.apply(add, &[ab, ac]);
    let eq = d.ieq(left, right);
    let with_c = d.pi_fv(c_fv, z, eq);
    let with_b = d.pi_fv(b_fv, z, with_c);
    d.pi_fv(a_fv, z, with_b)
}

/// `IsCommRing add mul neg zero one`'s eight leaf components — the same
/// "rebuild the unfolded `Prop`s directly, never through the folded constant"
/// convention `rat_prelude::field::FieldParts` uses.
struct RingParts {
    add_comm: ExprId,
    add_assoc: ExprId,
    add_zero: ExprId,
    add_neg: ExprId,
    mul_comm: ExprId,
    mul_assoc: ExprId,
    mul_one: ExprId,
    distrib: ExprId,
}

fn ring_parts(
    d: &mut IntDev<'_>,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    zero: ExprId,
    one: ExprId,
) -> RingParts {
    RingParts {
        add_comm: ring_add_comm_prop(d, add),
        add_assoc: ring_add_assoc_prop(d, add),
        add_zero: ring_add_zero_prop(d, add, zero),
        add_neg: ring_add_neg_prop(d, add, neg, zero),
        mul_comm: ring_mul_comm_prop(d, mul),
        mul_assoc: ring_mul_assoc_prop(d, mul),
        mul_one: ring_mul_one_prop(d, mul, one),
        distrib: ring_distrib_prop(d, add, mul),
    }
}

/// Right-nested `And` of [`RingParts`]'s eight leaves:
///
/// `add_comm ∧ (add_assoc ∧ (add_zero ∧ (add_neg ∧ (mul_comm ∧ (mul_assoc ∧
/// (mul_one ∧ distrib))))))`.
fn ring_body(d: &mut IntDev<'_>, parts: &RingParts) -> ExprId {
    let p7 = d.and(parts.mul_one, parts.distrib);
    let p6 = d.and(parts.mul_assoc, p7);
    let p5 = d.and(parts.mul_comm, p6);
    let p4 = d.and(parts.add_neg, p5);
    let p3 = d.and(parts.add_zero, p4);
    let p2 = d.and(parts.add_assoc, p3);
    d.and(parts.add_comm, p2)
}

/// `d.const_app(p.is_comm_ring, &[add, mul, neg, zero, one])`.
fn is_comm_ring(
    d: &mut IntDev<'_>,
    p: &IntPrelude,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    zero: ExprId,
    one: ExprId,
) -> ExprId {
    d.const_app(p.is_comm_ring, &[add, mul, neg, zero, one])
}

/// `And.intro left right lp rp : And left right`.
fn ring_and_intro(
    d: &mut IntDev<'_>,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = d.int().logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// Admit `Int.IsCommRing : (Int → Int → Int) → (Int → Int → Int) → (Int →
/// Int) → Int → Int → Prop`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_is_comm_ring(d: &mut IntDev<'_>, p: &IntPrelude) -> Result<(), KernelError> {
    let p = *p;
    let z = d.int_ty();
    let prop = d.kernel().sort_zero();
    let binop = ring_binop_ty(d);
    let unop = ring_unop_ty(d);

    let add_fv = d.fresh_fvar();
    let add = d.kernel().fvar(add_fv);
    let mul_fv = d.fresh_fvar();
    let mul = d.kernel().fvar(mul_fv);
    let neg_fv = d.fresh_fvar();
    let neg = d.kernel().fvar(neg_fv);
    let zero_fv = d.fresh_fvar();
    let zero = d.kernel().fvar(zero_fv);
    let one_fv = d.fresh_fvar();
    let one = d.kernel().fvar(one_fv);

    let parts = ring_parts(d, add, mul, neg, zero, one);
    let body = ring_body(d, &parts);

    let value = {
        let with_one = d.lam_fv(one_fv, z, body);
        let with_zero = d.lam_fv(zero_fv, z, with_one);
        let with_neg = d.lam_fv(neg_fv, unop, with_zero);
        let with_mul = d.lam_fv(mul_fv, binop, with_neg);
        d.lam_fv(add_fv, binop, with_mul)
    };
    let ty = {
        let over_one = d.arrow(z, prop);
        let over_zero = d.arrow(z, over_one);
        let over_neg = d.arrow(unop, over_zero);
        let over_mul = d.arrow(binop, over_neg);
        d.arrow(binop, over_mul)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_comm_ring,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(RING_HEIGHT),
    })
}

/// Admit `Int.int_isCommRing : Int.IsCommRing Int.add Int.mul Int.neg
/// Int.zero Int.one` — assembled entirely from already-admitted theorems.
/// Each of the eight leaves' STATED type already matches [`ring_parts`]'s
/// corresponding component verbatim (`Int.add_comm : ∀ a b, add a b = add b
/// a`, …, `Int.left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a
/// c)`), so every leaf proof is a bare reference to the existing constant —
/// no new algebra, only `And.intro` bookkeeping, exactly
/// `rat_prelude::field::declare_rat_is_field`'s pattern.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_int_is_comm_ring(d: &mut IntDev<'_>, p: IntPrelude) -> Result<(), KernelError> {
    let add = d.kernel().const_(p.add, vec![]);
    let mul = d.kernel().const_(p.mul, vec![]);
    let neg = d.kernel().const_(p.neg, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let ty = is_comm_ring(d, &p, add, mul, neg, zero, one);
    let parts = ring_parts(d, add, mul, neg, zero, one);

    let add_comm = d.lemma(p.add_comm, &[]);
    let add_assoc = d.lemma(p.add_assoc, &[]);
    let add_zero = d.lemma(p.add_zero, &[]);
    let add_neg = d.lemma(p.add_neg, &[]);
    let mul_comm = d.lemma(p.mul_comm, &[]);
    let mul_assoc = d.lemma(p.mul_assoc, &[]);
    let mul_one = d.lemma(p.mul_one, &[]);
    let distrib = d.lemma(p.left_distrib, &[]);

    let t6 = d.and(parts.mul_one, parts.distrib);
    let t5 = d.and(parts.mul_assoc, t6);
    let t4 = d.and(parts.mul_comm, t5);
    let t3 = d.and(parts.add_neg, t4);
    let t2 = d.and(parts.add_zero, t3);
    let t1 = d.and(parts.add_assoc, t2);

    let p7v = ring_and_intro(d, parts.mul_one, parts.distrib, mul_one, distrib);
    let p6v = ring_and_intro(d, parts.mul_assoc, t6, mul_assoc, p7v);
    let p5v = ring_and_intro(d, parts.mul_comm, t5, mul_comm, p6v);
    let p4v = ring_and_intro(d, parts.add_neg, t4, add_neg, p5v);
    let p3v = ring_and_intro(d, parts.add_zero, t3, add_zero, p4v);
    let p2v = ring_and_intro(d, parts.add_assoc, t2, add_assoc, p3v);
    let value = ring_and_intro(d, parts.add_comm, t1, add_comm, p2v);

    d.declare_theorem(p.int_is_comm_ring, ty, value)
}

/// Admit `Int.IsCommRing` and `Int.int_isCommRing`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_ring_all(d: &mut IntDev<'_>, p: &IntPrelude) -> Result<(), KernelError> {
    declare_is_comm_ring(d, p)?;
    declare_int_is_comm_ring(d, *p)?;
    Ok(())
}
