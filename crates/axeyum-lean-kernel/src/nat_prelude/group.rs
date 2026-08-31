//! `Nat.IsGroupOn` — the bundled-predicate shape (`rat_prelude/probability.rs`'s
//! `Rat.IsDistribution` is the house pattern) for "this operation, identity and
//! inverse make a group on `{0, …, n-1}`" — plus the three facts that
//! distinguish a group from a monoid, and a worked instance.
//!
//! ## Why a bundled `Prop`, not a typeclass
//!
//! This kernel has no typeclasses and no structure/record type, so "satisfies
//! the group axioms" cannot be a bundle a caller instantiates; it has to be a
//! `Prop`-valued `Definition` over explicit `op`/`e`/`inv`/`n` arguments,
//! exactly the shape `Rat.IsDistribution p n` already uses over `p`/`n`.
//!
//! ## What's declared
//!
//! - `Nat.IsGroupOn (op : Nat → Nat → Nat) (e : Nat) (inv : Nat → Nat) (n : Nat)
//!   : Prop := closure ∧ (associativity ∧ (identity ∧ inverse))`
//!   (right-nested `And`, the same packing convention `relation.rs`'s
//!   `EquivalenceOn` uses), where every quantifier is bounded on `n`:
//!     - `closure := ∀ a b, a<n → b<n → op a b < n`
//!     - `associativity := ∀ a b c, a<n → b<n → c<n → op (op a b) c = op a (op b c)`
//!     - `identity := e<n ∧ ∀ a, a<n → op a e = a ∧ op e a = a`
//!     - `inverse := ∀ a, a<n → inv a < n ∧ (op a (inv a) = e ∧ op (inv a) a = e)`
//!
//!   `identity` bundles `e<n` because [`declare_group_identity_unique`] needs
//!   to apply the *other* candidate identity's own defining property at `a
//!   := e`, which requires `e` inside its bound.
//! - `Nat.group_identity_unique : IsGroupOn op e inv n → ∀ e', e'<n →
//!   (∀ a, a<n → op a e' = a) → e' = e` — an identity element is unique
//!   among candidates satisfying the same (right-identity) property. Two
//!   substitutions and a `trans`: `e' = op e e' = e`, using `e`'s
//!   left-identity law at `a := e'` for the first step and the hypothesis at
//!   `a := e` for the second — no associativity needed.
//! - `Nat.group_inverse_unique : IsGroupOn op e inv n → ∀ a b c, a<n→b<n→c<n
//!   → op b a = e → op a c = e → b = c` — a left inverse of `a` equals a
//!   right inverse of `a` (the classical monoid-with-associativity argument:
//!   `b = b*e = b*(a*c) = (b*a)*c = e*c = c`), stated more generally than
//!   "inverses are unique" because it never needs `b`/`c` to be *two-sided*
//!   inverses, only one-sided in the direction actually used.
//! - `Nat.group_left_cancel : IsGroupOn op e inv n → ∀ a b c, a<n→b<n→c<n →
//!   op a b = op a c → b = c` — left cancellation, via `b = e*b =
//!   (inv a*a)*b = inv a*(a*b) = inv a*(a*c) = (inv a*a)*c = e*c = c`.
//! - `Nat.modAdd_isGroup : ∀ n, 0<n → IsGroupOn (fun a b => mod (add a b) n)
//!   0 (fun a => mod (sub n a) n) n` — the worked instance, ℤ/n under
//!   addition. Closure and the identity laws are direct
//!   (`mod_lt`/`add_zero`/`zero_add`/`mod_eq_self_of_lt`). Associativity and
//!   the inverse laws go through a small private modular-arithmetic toolkit
//!   built once here from the existing balanced-witness `Nat.modEq`
//!   (`modular.rs`) and the executable/relational division bridge
//!   (`division.rs`'s `div_mod_exec`, reached through `n`'s own
//!   `n = succ (pred n)` witness via [`pos_implies_succ_pred`], since
//!   `div_mod_exec` is stated at a successor divisor):
//!     - [`div_mod_reconstructed`] connects the *executable* `Nat.mod`/`Nat.div`
//!       to the *relational* `divMod`, for the general (non-successor-literal)
//!       divisor `n` this file works with throughout.
//!     - [`mod_self_congr`] is `Nat.modEq n x (mod x n)` for any `x` — the
//!       bridge from "the actual remainder" back to the congruence relation
//!       `modular.rs` already has closure lemmas for.
//!     - [`mod_eq_of_mod_eq_rel`] is the converse bridge, `modEq n u v → mod
//!       u n = mod v n`, via `div_mod_remainder_eq_of_mod_eq`'s
//!       remainder-uniqueness applied to two `div_mod_reconstructed` witnesses.
//!     - [`mod_self`] is `mod n n = 0`, via `div_mod_unique` against the
//!       candidate witness `n = n*1+0`.
//!
//!   Associativity then reduces to `Nat.add_assoc` under one `mod` congruence
//!   on each side (moving between `mod (add a b) n` and `add a b` inside a
//!   further sum via [`mod_self_congr`]); the inverse laws reduce to
//!   `add_sub_cancel_of_le`/`sub_add_cancel` collapsing to `mod n n`.
//!
//! ## Status
//!
//! All of the above are declared here and axiom-free.

use super::NatPrelude;
use super::finite::{le_of_lt, pos_implies_succ_pred};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.IsGroupOn`: a plain bounded `Prop` predicate over
/// caller-supplied `op`/`inv`, the same height `relation.rs`'s
/// `ReflexiveOn`/`SymmetricOn`/`TransitiveOn`/`EquivalenceOn` use — nothing
/// else in this file needs to unfold through it at a higher priority.
const GROUP_HEIGHT: u16 = 1;

/// `Nat → Nat → Nat`.
fn binop_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let inner = d.arrow(nat, nat);
    d.arrow(nat, inner)
}

/// `Nat → Nat`.
fn unop_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `closure op n := ∀ a b, a<n → b<n → op a b < n`.
fn closure_prop(d: &mut NatDev<'_>, op: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let ab = d.apply(op, &[a, b]);
    let concl = d.lt(ab, n);
    let hb = d.lt(b, n);
    let step_b = d.arrow(hb, concl);
    let ha = d.lt(a, n);
    let inner = d.arrow(ha, step_b);
    let with_b = d.pi_fv(b_fv, nat, inner);
    d.pi_fv(a_fv, nat, with_b)
}

/// `assoc op n := ∀ a b c, a<n → b<n → c<n → op (op a b) c = op a (op b c)`.
fn assoc_prop(d: &mut NatDev<'_>, op: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let ab = d.apply(op, &[a, b]);
    let ab_c = d.apply(op, &[ab, c]);
    let bc = d.apply(op, &[b, c]);
    let a_bc = d.apply(op, &[a, bc]);
    let concl = d.eq(ab_c, a_bc);
    let hc = d.lt(c, n);
    let step_c = d.arrow(hc, concl);
    let hb = d.lt(b, n);
    let step_b = d.arrow(hb, step_c);
    let ha = d.lt(a, n);
    let inner = d.arrow(ha, step_b);
    let with_c = d.pi_fv(c_fv, nat, inner);
    let with_b = d.pi_fv(b_fv, nat, with_c);
    d.pi_fv(a_fv, nat, with_b)
}

/// `e<n`, the bound half of `identity`.
fn identity_bound_prop(d: &mut NatDev<'_>, e: ExprId, n: ExprId) -> ExprId {
    d.lt(e, n)
}

/// `∀ a, a<n → op a e = a ∧ op e a = a`, the quantified half of `identity`.
fn identity_forall_prop(d: &mut NatDev<'_>, op: ExprId, e: ExprId, n: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let ae = d.apply(op, &[a, e]);
    let ea = d.apply(op, &[e, a]);
    let left_eq = d.eq(ae, a);
    let right_eq = d.eq(ea, a);
    let both = d.const_app(logic.and, &[left_eq, right_eq]);
    let ha = d.lt(a, n);
    let inner = d.arrow(ha, both);
    d.pi_fv(a_fv, nat, inner)
}

/// `∀ a, a<n → op a e' = a` — the single (right-identity) property
/// [`declare_group_identity_unique`]'s candidate `e'` is hypothesized to
/// satisfy, deliberately weaker than [`identity_forall_prop`]'s two-sided
/// bundle (that theorem never needs `e'`'s *left*-identity law).
fn right_identity_forall_prop(d: &mut NatDev<'_>, op: ExprId, e: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let ae = d.apply(op, &[a, e]);
    let eq_ty = d.eq(ae, a);
    let ha = d.lt(a, n);
    let inner = d.arrow(ha, eq_ty);
    d.pi_fv(a_fv, nat, inner)
}

/// `identity op e n := e<n ∧ (∀ a, a<n → op a e = a ∧ op e a = a)`.
fn identity_prop(d: &mut NatDev<'_>, op: ExprId, e: ExprId, n: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let bound = identity_bound_prop(d, e, n);
    let forall_part = identity_forall_prop(d, op, e, n);
    d.const_app(logic.and, &[bound, forall_part])
}

/// `inverse op e inv n := ∀ a, a<n → inv a<n ∧ (op a (inv a)=e ∧ op (inv a) a=e)`.
fn inverse_prop(d: &mut NatDev<'_>, op: ExprId, e: ExprId, inv: ExprId, n: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let ia = d.apply(inv, &[a]);
    let ia_lt_n = d.lt(ia, n);
    let a_ia = d.apply(op, &[a, ia]);
    let ia_a = d.apply(op, &[ia, a]);
    let left_eq = d.eq(a_ia, e);
    let right_eq = d.eq(ia_a, e);
    let eqs = d.const_app(logic.and, &[left_eq, right_eq]);
    let bundle = d.const_app(logic.and, &[ia_lt_n, eqs]);
    let ha = d.lt(a, n);
    let inner = d.arrow(ha, bundle);
    d.pi_fv(a_fv, nat, inner)
}

/// `IsGroupOn op e inv n`'s four components, built directly (never through
/// the constant), so a caller decomposing a hypothesis of the *folded* type
/// `d.const_app(p.is_group_on, &[op, e, inv, n])` can pass these as the
/// `left`/`right` type arguments to [`and_left`]/[`and_right`] — the
/// hypothesis's type is defeq to `And` of these by `IsGroupOn`'s own
/// definition, exactly as `rat_prelude/probability.rs`'s
/// `is_distribution_parts` is used against `Rat.IsDistribution` hypotheses.
fn is_group_on_parts(
    d: &mut NatDev<'_>,
    op: ExprId,
    e: ExprId,
    inv: ExprId,
    n: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let closure = closure_prop(d, op, n);
    let assoc = assoc_prop(d, op, n);
    let identity = identity_prop(d, op, e, n);
    let inverse = inverse_prop(d, op, e, inv, n);
    (closure, assoc, identity, inverse)
}

/// `d.const_app(p.is_group_on, &[op, e, inv, n])`.
fn is_group_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    op: ExprId,
    e: ExprId,
    inv: ExprId,
    n: ExprId,
) -> ExprId {
    d.const_app(p.is_group_on, &[op, e, inv, n])
}

/// Admit `Nat.IsGroupOn`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_is_group_on(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let fn2 = binop_ty(d);
    let fn1 = unop_ty(d);

    let op_fv = d.fresh_fvar();
    let op = d.kernel().fvar(op_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (closure, assoc, identity, inverse) = is_group_on_parts(d, op, e, inv, n);
    let logic = p.logic;
    let id_inv = d.const_app(logic.and, &[identity, inverse]);
    let assoc_rest = d.const_app(logic.and, &[assoc, id_inv]);
    let body = d.const_app(logic.and, &[closure, assoc_rest]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_inv = d.lam_fv(inv_fv, fn1, with_n);
        let with_e = d.lam_fv(e_fv, nat, with_inv);
        d.lam_fv(op_fv, fn2, with_e)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_inv = d.arrow(fn1, over_n);
        let over_e = d.arrow(nat, over_inv);
        d.arrow(fn2, over_e)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_group_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GROUP_HEIGHT),
    })
}

/// The five proof-pieces a `h : IsGroupOn op e inv n` hypothesis decomposes
/// into: closure, associativity, `e<n`, the identity `∀`, and the inverse
/// `∀`. Each helper below applies these at the specific points its proof
/// needs.
struct GroupParts {
    /// No declared consequence in this file needs `closure` on its own (each
    /// gets it back implicitly through `assoc`'s own bounds), but it is part
    /// of what a `h : IsGroupOn` hypothesis decomposes into and a future
    /// consequence may need it directly.
    #[allow(dead_code)]
    closure: ExprId,
    assoc: ExprId,
    e_lt_n: ExprId,
    identity_forall: ExprId,
    inverse_forall: ExprId,
}

/// Decompose `h : IsGroupOn op e inv n` (typed through the folded constant)
/// into [`GroupParts`], via nested [`and_left`]/[`and_right`] against the
/// unfolded component types from [`is_group_on_parts`]/[`identity_bound_prop`]/
/// [`identity_forall_prop`].
fn decompose_is_group_on(
    d: &mut NatDev<'_>,
    op: ExprId,
    e: ExprId,
    inv: ExprId,
    n: ExprId,
    h: ExprId,
) -> GroupParts {
    let logic = d.prelude().logic;
    let closure_ty = closure_prop(d, op, n);
    let assoc_ty = assoc_prop(d, op, n);
    let identity_ty = identity_prop(d, op, e, n);
    let inverse_ty = inverse_prop(d, op, e, inv, n);
    let id_inv_ty = d.const_app(logic.and, &[identity_ty, inverse_ty]);
    let assoc_rest_ty = d.const_app(logic.and, &[assoc_ty, id_inv_ty]);

    let closure = and_left(d, closure_ty, assoc_rest_ty, h);
    let assoc_rest = and_right(d, closure_ty, assoc_rest_ty, h);
    let assoc = and_left(d, assoc_ty, id_inv_ty, assoc_rest);
    let id_inv = and_right(d, assoc_ty, id_inv_ty, assoc_rest);

    let bound_ty = identity_bound_prop(d, e, n);
    let forall_ty = identity_forall_prop(d, op, e, n);
    let identity = and_left(d, identity_ty, inverse_ty, id_inv);
    let inverse_forall = and_right(d, identity_ty, inverse_ty, id_inv);
    let e_lt_n = and_left(d, bound_ty, forall_ty, identity);
    let identity_forall = and_right(d, bound_ty, forall_ty, identity);

    GroupParts {
        closure,
        assoc,
        e_lt_n,
        identity_forall,
        inverse_forall,
    }
}

/// Build `Pi`/`Lam` around `(stmt, proof)` for `binders`, outermost first —
/// a generic replacement for [`NatOps::theorem`] when the quantified
/// variables are not all `Nat` (here: `op : Nat → Nat → Nat`, `inv : Nat →
/// Nat`, plus propositional hypotheses whose proof term the body actually
/// uses, so each needs its own named free variable rather than
/// [`NatOps::arrow`]'s anonymous binder).
fn build_pi_lam(
    d: &mut NatDev<'_>,
    binders: &[(u64, ExprId)],
    stmt: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, vty) in binders.iter().rev() {
        ty = d.pi_fv(fv, vty, ty);
        value = d.lam_fv(fv, vty, value);
    }
    (ty, value)
}

/// Admit `Nat.group_identity_unique`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_group_identity_unique(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn2 = binop_ty(d);
    let fn1 = unop_ty(d);

    let op_fv = d.fresh_fvar();
    let op = d.kernel().fvar(op_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let ep_fv = d.fresh_fvar();
    let ep = d.kernel().fvar(ep_fv);
    let ep_lt_fv = d.fresh_fvar();
    let ep_lt = d.kernel().fvar(ep_lt_fv);
    let hep_fv = d.fresh_fvar();
    let hep = d.kernel().fvar(hep_fv);

    let group_ty = is_group_on(d, &p, op, e, inv, n);
    let ep_lt_ty = d.lt(ep, n);
    let hep_ty = right_identity_forall_prop(d, op, ep, n);
    let concl = d.eq(ep, e);

    let parts = decompose_is_group_on(d, op, e, inv, n, h);

    // fact (i): op e ep = ep, from e's identity_forall at a := ep (right half).
    let hep_at_ep = d.apply(parts.identity_forall, &[ep, ep_lt]);
    let ep_e = d.apply(op, &[ep, e]);
    let e_ep = d.apply(op, &[e, ep]);
    let left_eq_ty = d.eq(ep_e, ep);
    let right_eq_ty = d.eq(e_ep, ep);
    let fact_i = and_right(d, left_eq_ty, right_eq_ty, hep_at_ep); // e_ep = ep

    // fact (ii): op e ep = e, from the hypothesis applied at a := e.
    let fact_ii = d.apply(hep, &[e, parts.e_lt_n]); // e_ep = e

    let ep_eq_e_ep = d.symm(e_ep, ep, fact_i); // ep = e_ep
    let proof_body = d.trans(ep, e_ep, e, ep_eq_e_ep, fact_ii); // ep = e

    let binders = [
        (op_fv, fn2),
        (e_fv, nat),
        (inv_fv, fn1),
        (n_fv, nat),
        (h_fv, group_ty),
        (ep_fv, nat),
        (ep_lt_fv, ep_lt_ty),
        (hep_fv, hep_ty),
    ];
    let (ty, value) = build_pi_lam(d, &binders, concl, proof_body);
    d.declare_theorem(p.group_identity_unique, ty, value)
}

/// Admit `Nat.group_inverse_unique`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_group_inverse_unique(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn2 = binop_ty(d);
    let fn1 = unop_ty(d);

    let op_fv = d.fresh_fvar();
    let op = d.kernel().fvar(op_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hba_fv = d.fresh_fvar();
    let hba = d.kernel().fvar(hba_fv);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);

    let group_ty = is_group_on(d, &p, op, e, inv, n);
    let ha_ty = d.lt(a, n);
    let hb_ty = d.lt(b, n);
    let hc_ty = d.lt(c, n);
    let ba = d.apply(op, &[b, a]);
    let ac = d.apply(op, &[a, c]);
    let hba_ty = d.eq(ba, e);
    let hac_ty = d.eq(ac, e);
    let concl = d.eq(b, c);

    let parts = decompose_is_group_on(d, op, e, inv, n, h);

    // step1 : b = op b e   (identity_forall at b, right half, reversed)
    let hb_at_b = d.apply(parts.identity_forall, &[b, hb]);
    let be = d.apply(op, &[b, e]);
    let eb = d.apply(op, &[e, b]);
    let left_eq_ty = d.eq(be, b);
    let right_eq_ty = d.eq(eb, b);
    let op_b_e_eq_b = and_left(d, left_eq_ty, right_eq_ty, hb_at_b);
    let step1 = d.symm(be, b, op_b_e_eq_b); // b = op b e

    // step2 : op b e = op b (op a c)   (e = op a c, congr under `op b _`)
    let e_eq_ac = d.symm(ac, e, hac);
    let b_ac = d.apply(op, &[b, ac]);
    let step2 = d.congr(e, ac, e_eq_ac, &|d, v| d.apply(op, &[b, v])); // op b e = op b (op a c)

    // step3 : op b (op a c) = op (op b a) c   (assoc at b,a,c, reversed)
    let assoc_bac = d.apply(parts.assoc, &[b, a, c, hb, ha, hc]); // op (op b a) c = op b (op a c)
    let ba_c = d.apply(op, &[ba, c]);
    let step3 = d.symm(ba_c, b_ac, assoc_bac); // op b (op a c) = op (op b a) c

    // step4 : op (op b a) c = op e c   (op b a = e, congr under `op _ c`)
    let ec = d.apply(op, &[e, c]);
    let step4 = d.congr(ba, e, hba, &|d, v| d.apply(op, &[v, c])); // op (op b a) c = op e c

    // step5 : op e c = c   (identity_forall at c, left half)
    let hc_at_c = d.apply(parts.identity_forall, &[c, hc]);
    let ce = d.apply(op, &[c, e]);
    let left_eq_ty2 = d.eq(ce, c);
    let right_eq_ty2 = d.eq(ec, c);
    let step5 = and_right(d, left_eq_ty2, right_eq_ty2, hc_at_c); // op e c = c

    let (_, proof_body) = d.chain(
        b,
        &[
            (be, step1),
            (b_ac, step2),
            (ba_c, step3),
            (ec, step4),
            (c, step5),
        ],
    );

    let binders = [
        (op_fv, fn2),
        (e_fv, nat),
        (inv_fv, fn1),
        (n_fv, nat),
        (h_fv, group_ty),
        (a_fv, nat),
        (b_fv, nat),
        (c_fv, nat),
        (ha_fv, ha_ty),
        (hb_fv, hb_ty),
        (hc_fv, hc_ty),
        (hba_fv, hba_ty),
        (hac_fv, hac_ty),
    ];
    let (ty, value) = build_pi_lam(d, &binders, concl, proof_body);
    d.declare_theorem(p.group_inverse_unique, ty, value)
}

/// Admit `Nat.group_left_cancel`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_group_left_cancel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn2 = binop_ty(d);
    let fn1 = unop_ty(d);

    let op_fv = d.fresh_fvar();
    let op = d.kernel().fvar(op_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let group_ty = is_group_on(d, &p, op, e, inv, n);
    let ha_ty = d.lt(a, n);
    let hb_ty = d.lt(b, n);
    let hc_ty = d.lt(c, n);
    let ab = d.apply(op, &[a, b]);
    let ac = d.apply(op, &[a, c]);
    let hab_ty = d.eq(ab, ac);
    let concl = d.eq(b, c);

    let parts = decompose_is_group_on(d, op, e, inv, n, h);

    // inverse facts for a: ia < n, op a ia = e, op ia a = e.
    let inv_at_a = d.apply(parts.inverse_forall, &[a, ha]);
    let ia = d.apply(inv, &[a]);
    let ia_lt_ty = d.lt(ia, n);
    let a_ia = d.apply(op, &[a, ia]);
    let ia_a = d.apply(op, &[ia, a]);
    let eqs_ty = {
        let logic = d.prelude().logic;
        let l = d.eq(a_ia, e);
        let r = d.eq(ia_a, e);
        d.const_app(logic.and, &[l, r])
    };
    let ia_lt = and_left(d, ia_lt_ty, eqs_ty, inv_at_a); // ia < n
    let eqs = and_right(d, ia_lt_ty, eqs_ty, inv_at_a);
    let l_ty = d.eq(a_ia, e);
    let r_ty = d.eq(ia_a, e);
    let op_ia_a_eq_e = and_right(d, l_ty, r_ty, eqs); // op ia a = e

    // step1 : b = op e b   (identity_forall at b, left half, reversed)
    let hb_at_b = d.apply(parts.identity_forall, &[b, hb]);
    let be = d.apply(op, &[b, e]);
    let eb = d.apply(op, &[e, b]);
    let left_eq_ty = d.eq(be, b);
    let right_eq_ty = d.eq(eb, b);
    let op_e_b_eq_b = and_right(d, left_eq_ty, right_eq_ty, hb_at_b);
    let step1 = d.symm(eb, b, op_e_b_eq_b); // b = op e b

    // step2 : op e b = op (op ia a) b   (e = op ia a, congr under `op _ b`)
    let e_eq_ia_a = d.symm(ia_a, e, op_ia_a_eq_e);
    let ia_a_b = d.apply(op, &[ia_a, b]);
    let step2 = d.congr(e, ia_a, e_eq_ia_a, &|d, v| d.apply(op, &[v, b]));

    // step3 : op (op ia a) b = op ia (op a b)   (assoc at ia,a,b)
    let step3 = d.apply(parts.assoc, &[ia, a, b, ia_lt, ha, hb]);
    let ia_ab = d.apply(op, &[ia, ab]);

    // step4 : op ia (op a b) = op ia (op a c)   (hyp, congr under `op ia _`)
    let ia_ac = d.apply(op, &[ia, ac]);
    let step4 = d.congr(ab, ac, hab, &|d, v| d.apply(op, &[ia, v]));

    // step5 : op ia (op a c) = op (op ia a) c   (assoc at ia,a,c, reversed)
    let assoc_iaac = d.apply(parts.assoc, &[ia, a, c, ia_lt, ha, hc]);
    let ia_a_c = d.apply(op, &[ia_a, c]);
    let step5 = d.symm(ia_a_c, ia_ac, assoc_iaac);

    // step6 : op (op ia a) c = op e c   (op ia a = e, congr under `op _ c`)
    let ec = d.apply(op, &[e, c]);
    let step6 = d.congr(ia_a, e, op_ia_a_eq_e, &|d, v| d.apply(op, &[v, c]));

    // step7 : op e c = c   (identity_forall at c, left half)
    let hc_at_c = d.apply(parts.identity_forall, &[c, hc]);
    let ce = d.apply(op, &[c, e]);
    let left_eq_ty2 = d.eq(ce, c);
    let right_eq_ty2 = d.eq(ec, c);
    let step7 = and_right(d, left_eq_ty2, right_eq_ty2, hc_at_c);

    let (_, proof_body) = d.chain(
        b,
        &[
            (eb, step1),
            (ia_a_b, step2),
            (ia_ab, step3),
            (ia_ac, step4),
            (ia_a_c, step5),
            (ec, step6),
            (c, step7),
        ],
    );

    let binders = [
        (op_fv, fn2),
        (e_fv, nat),
        (inv_fv, fn1),
        (n_fv, nat),
        (h_fv, group_ty),
        (a_fv, nat),
        (b_fv, nat),
        (c_fv, nat),
        (ha_fv, ha_ty),
        (hb_fv, hb_ty),
        (hc_fv, hc_ty),
        (hab_fv, hab_ty),
    ];
    let (ty, value) = build_pi_lam(d, &binders, concl, proof_body);
    d.declare_theorem(p.group_left_cancel, ty, value)
}

/// Reconstruct the relational `divMod n x (div x n) (mod x n)` from the
/// executable `div_mod_exec` (stated at a successor divisor) via `n`'s own
/// `n = succ (pred n)` witness (valid since `pos_n : 0 < n`).
fn div_mod_reconstructed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let succ_pred_witness = pos_implies_succ_pred(d, &p, n);
    let n_eq_succ_pred = d.apply(succ_pred_witness, &[pos_n]); // n = succ (pred n)
    let pred_n = d.pred(n);
    let succ_pred_n = d.succ(pred_n);
    let exec = d.lemma(p.div_mod_exec, &[pred_n, x]); // divMod (succ pred_n) x (div x (succ pred_n)) (mod x (succ pred_n))

    let motive = d.eq_motive(succ_pred_n, &|d, y| {
        let q = d.div(x, y);
        let r = d.modulo(x, y);
        d.div_mod(y, x, q, r)
    });
    let eq_rev = d.symm(n, succ_pred_n, n_eq_succ_pred); // succ_pred_n = n
    d.transport(succ_pred_n, motive, exec, n, eq_rev)
}

/// `Nat.modEq n x (mod x n)`, for any `x` (given `pos_n : 0 < n`) — the
/// balanced witness is `(u, v) := (0, div x n)`, using `x = n*(div x n) +
/// mod x n` from [`div_mod_reconstructed`] reordered by `add_comm`.
pub(super) fn mod_self_congr(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();
    let one = d.level_one();

    let dm = div_mod_reconstructed(d, &p, n, pos_n, x);
    let q = d.div(x, n);
    let r = d.modulo(x, n);
    let mq = d.mul(n, q);
    let sum_nq_r = d.add(mq, r);
    let eq_ty = d.eq(x, sum_nq_r);
    let bound_ty = d.lt(r, n);
    let eq_part = and_left(d, eq_ty, bound_ty, dm); // x = mq + r

    let commuted = d.lemma(p.add_comm, &[mq, r]); // mq+r = r+mq
    let sum_rq = d.add(r, mq);
    let x_eq_sum_rq = d.trans(x, sum_nq_r, sum_rq, eq_part, commuted); // x = r+mq

    let n0 = d.mul(n, zero);
    let sum_x0 = d.add(x, n0); // mod_eq_sum(n,x,0)
    let mul_zero_pf = d.lemma(p.mul_zero, &[n]); // n*0 = 0
    let x_plus_zero = d.add(x, zero);
    let x0_congr = d.congr(n0, zero, mul_zero_pf, &|d, v| d.add(x, v)); // x+n*0 = x+0
    let add_zero_pf = d.lemma(p.add_zero, &[x]); // x+0 = x
    let (_, left_chain) = d.chain(sum_x0, &[(x_plus_zero, x0_congr), (x, add_zero_pf)]); // sum_x0 = x
    let full = d.trans(sum_x0, x, sum_rq, left_chain, x_eq_sum_rq); // mod_eq_sum(n,x,0) = mod_eq_sum(n,r,q)

    let inner_predicate = d.mod_eq_inner_predicate(n, x, r, zero);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    let inner = d.apply(intro, &[nat, inner_predicate, q, full]);
    let outer_predicate = d.mod_eq_outer_predicate(n, x, r);
    d.apply(intro, &[nat, outer_predicate, zero, inner])
}

/// `modEq n u v → mod u n = mod v n`, by feeding two [`div_mod_reconstructed`]
/// witnesses to `div_mod_remainder_eq_of_mod_eq`'s remainder-uniqueness.
pub(super) fn mod_eq_of_mod_eq_rel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    u: ExprId,
    v: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let qu = d.div(u, n);
    let ru = d.modulo(u, n);
    let qv = d.div(v, n);
    let rv = d.modulo(v, n);
    let dm_u = div_mod_reconstructed(d, &p, n, pos_n, u);
    let dm_v = div_mod_reconstructed(d, &p, n, pos_n, v);
    d.lemma(
        p.div_mod_remainder_eq_of_mod_eq,
        &[n, u, v, qu, ru, qv, rv, h, dm_u, dm_v],
    )
}

/// `mod (add x y1) n = mod (add x y2) n`, from `modEq n y1 y2`.
#[allow(clippy::too_many_arguments)]
fn mod_congr_add_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    x: ExprId,
    y1: ExprId,
    y2: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let modeq_sum = d.lemma(p.mod_eq_add_left, &[n, y1, y2, x, h]);
    let sum1 = d.add(x, y1);
    let sum2 = d.add(x, y2);
    mod_eq_of_mod_eq_rel(d, &p, n, pos_n, sum1, sum2, modeq_sum)
}

/// `mod (add x1 y) n = mod (add x2 y) n`, from `modEq n x1 x2`.
#[allow(clippy::too_many_arguments)]
fn mod_congr_add_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    y: ExprId,
    x1: ExprId,
    x2: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let modeq_sum = d.lemma(p.mod_eq_add_right, &[n, x1, x2, y, h]);
    let sum1 = d.add(x1, y);
    let sum2 = d.add(x2, y);
    mod_eq_of_mod_eq_rel(d, &p, n, pos_n, sum1, sum2, modeq_sum)
}

/// `mod n n = 0`, via `div_mod_unique` against the candidate witness
/// `n = n*1 + 0`.
fn mod_self(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, pos_n: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one_val = d.succ(zero);
    let dm_n = div_mod_reconstructed(d, &p, n, pos_n, n);
    let div_n_n = d.div(n, n);
    let mod_n_n = d.modulo(n, n);

    let mul_n_one = d.mul(n, one_val);
    let mul_one_pf = d.lemma(p.mul_one, &[n]); // n*1 = n
    let sum = d.add(mul_n_one, zero);
    let add_zero_pf = d.lemma(p.add_zero, &[mul_n_one]); // n*1+0 = n*1
    let sum_eq_n = d.trans(sum, mul_n_one, n, add_zero_pf, mul_one_pf); // n*1+0 = n
    let n_eq_sum = d.symm(sum, n, sum_eq_n); // n = n*1+0

    let eq_ty = d.eq(n, sum);
    let bound_ty = d.lt(zero, n);
    let cand = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, n_eq_sum, pos_n]);

    let result = d.lemma(
        p.div_mod_unique,
        &[n, n, div_n_n, mod_n_n, one_val, zero, dm_n, cand],
    );
    let q_eq_ty = d.eq(div_n_n, one_val);
    let r_eq_ty = d.eq(mod_n_n, zero);
    and_right(d, q_eq_ty, r_eq_ty, result)
}

/// The associativity law for `op a b := mod (add a b) n`: `op (op a b) c =
/// op a (op b c)`, unconditionally in `a`,`b`,`c` (given `pos_n`) — the
/// bounds are threaded through only so the statement matches
/// [`assoc_prop`]'s shape.
fn mod_add_assoc(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let p = *p;
    let s1 = d.add(a, b);
    let m1 = d.modulo(s1, n);
    let s2 = d.add(b, c);
    let m2 = d.modulo(s2, n);

    let modeq_m1_s1 = {
        let cong = mod_self_congr(d, &p, n, pos_n, s1); // modEq n s1 m1
        d.lemma(p.mod_eq_symm, &[n, s1, m1, cong]) // modEq n m1 s1
    };
    let eq_l = mod_congr_add_right(d, &p, n, pos_n, c, m1, s1, modeq_m1_s1); // mod(m1+c)n = mod(s1+c)n

    let modeq_m2_s2 = {
        let cong = mod_self_congr(d, &p, n, pos_n, s2);
        d.lemma(p.mod_eq_symm, &[n, s2, m2, cong])
    };
    let eq_r = mod_congr_add_left(d, &p, n, pos_n, a, m2, s2, modeq_m2_s2); // mod(a+m2)n = mod(a+s2)n

    let assoc_raw = d.lemma(p.add_assoc, &[a, b, c]); // (a+b)+c = a+(b+c), i.e. s1+c = a+s2
    let lhs_arg = d.add(s1, c);
    let rhs_arg = d.add(a, s2);
    let congr_assoc = d.congr(lhs_arg, rhs_arg, assoc_raw, &|d, v| d.modulo(v, n));

    let m1_c = d.add(m1, c);
    let lhs_expr = d.modulo(m1_c, n);
    let mid1 = d.modulo(lhs_arg, n);
    let mid2 = d.modulo(rhs_arg, n);
    let a_m2 = d.add(a, m2);
    let rhs_expr = d.modulo(a_m2, n);
    let eq_r_rev = d.symm(rhs_expr, mid2, eq_r); // mid2 = rhs_expr

    let (_, chain) = d.chain(
        lhs_expr,
        &[(mid1, eq_l), (mid2, congr_assoc), (rhs_expr, eq_r_rev)],
    );
    chain
}

/// `mod (add a (mod (sub n a) n)) n = 0`, for `a < n`.
fn mod_add_right_inverse(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    a: ExprId,
    a_lt_n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let diff = d.sub(n, a);
    let md = d.modulo(diff, n);

    let modeq_md_diff = {
        let cong = mod_self_congr(d, &p, n, pos_n, diff);
        d.lemma(p.mod_eq_symm, &[n, diff, md, cong])
    };
    let step1 = mod_congr_add_left(d, &p, n, pos_n, a, md, diff, modeq_md_diff); // mod(a+md)n = mod(a+diff)n

    let a_le_n = le_of_lt(d, &p, a, n, a_lt_n);
    let sum_eq_n = d.lemma(p.add_sub_cancel_of_le, &[a, n, a_le_n]); // a+diff = n
    let sum_expr = d.add(a, diff);
    let step2 = d.congr(sum_expr, n, sum_eq_n, &|d, v| d.modulo(v, n)); // mod(a+diff)n = mod n n

    let step3 = mod_self(d, &p, n, pos_n); // mod n n = 0

    let a_md = d.add(a, md);
    let lhs_expr = d.modulo(a_md, n);
    let mid1 = d.modulo(sum_expr, n);
    let mid2 = d.modulo(n, n);
    let (_, chain) = d.chain(lhs_expr, &[(mid1, step1), (mid2, step2), (zero, step3)]);
    chain
}

/// `mod (add (mod (sub n a) n) a) n = 0`, for `a < n`.
fn mod_add_left_inverse(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    a: ExprId,
    a_lt_n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let diff = d.sub(n, a);
    let md = d.modulo(diff, n);

    let modeq_md_diff = {
        let cong = mod_self_congr(d, &p, n, pos_n, diff);
        d.lemma(p.mod_eq_symm, &[n, diff, md, cong])
    };
    let step1 = mod_congr_add_right(d, &p, n, pos_n, a, md, diff, modeq_md_diff); // mod(md+a)n = mod(diff+a)n

    let a_le_n = le_of_lt(d, &p, a, n, a_lt_n);
    let sum_eq_n = d.lemma(p.sub_add_cancel, &[a, n, a_le_n]); // diff+a = n
    let sum_expr = d.add(diff, a);
    let step2 = d.congr(sum_expr, n, sum_eq_n, &|d, v| d.modulo(v, n));

    let step3 = mod_self(d, &p, n, pos_n);

    let md_a = d.add(md, a);
    let lhs_expr = d.modulo(md_a, n);
    let mid1 = d.modulo(sum_expr, n);
    let mid2 = d.modulo(n, n);
    let (_, chain) = d.chain(lhs_expr, &[(mid1, step1), (mid2, step2), (zero, step3)]);
    chain
}

/// Admit `Nat.modAdd_isGroup : ∀ n, 0<n → IsGroupOn (fun a b => mod (add a
/// b) n) 0 (fun a => mod (sub n a) n) n` — the worked instance, ℤ/n under
/// addition.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_mod_add_is_group(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.mod_add_is_group, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();

        let op = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let sum = d.add(a, b);
            let body = d.modulo(sum, n);
            let inner = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, inner)
        };
        let e = zero;
        let inv = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let diff = d.sub(n, a);
            let body = d.modulo(diff, n);
            d.lam_fv(a_fv, nat, body)
        };

        let pos_n_fv = d.fresh_fvar();
        let pos_n = d.kernel().fvar(pos_n_fv);
        let pos_n_ty = d.lt(zero, n);

        let (closure_ty, assoc_ty, identity_ty, inverse_ty) = is_group_on_parts(d, op, e, inv, n);

        // closure : ∀ a b, a<n→b<n→ op a b<n, via mod_lt (unused bounds).
        let closure_proof = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ha_fv = d.fresh_fvar();
            let hb_fv = d.fresh_fvar();
            let sum = d.add(a, b);
            let bound = d.lemma(p.mod_lt, &[sum, n, pos_n]); // mod(a+b) n < n
            let ha_ty = d.lt(a, n);
            let hb_ty = d.lt(b, n);
            let with_hb = d.lam_fv(hb_fv, hb_ty, bound);
            let with_ha = d.lam_fv(ha_fv, ha_ty, with_hb);
            let with_b = d.lam_fv(b_fv, nat, with_ha);
            d.lam_fv(a_fv, nat, with_b)
        };

        // associativity : ∀ a b c, a<n→b<n→c<n→ op(op a b)c = op a(op b c).
        let assoc_proof = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let ha_fv = d.fresh_fvar();
            let hb_fv = d.fresh_fvar();
            let hc_fv = d.fresh_fvar();
            let body = mod_add_assoc(d, &p, n, pos_n, a, b, c);
            let hc_ty = d.lt(c, n);
            let hb_ty = d.lt(b, n);
            let ha_ty = d.lt(a, n);
            let with_hc = d.lam_fv(hc_fv, hc_ty, body);
            let with_hb = d.lam_fv(hb_fv, hb_ty, with_hc);
            let with_ha = d.lam_fv(ha_fv, ha_ty, with_hb);
            let with_c = d.lam_fv(c_fv, nat, with_ha);
            let with_b = d.lam_fv(b_fv, nat, with_c);
            d.lam_fv(a_fv, nat, with_b)
        };

        // identity : 0<n ∧ ∀a,a<n→ op a 0=a ∧ op 0 a=a.
        let identity_proof = {
            let forall_part = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let ha_fv = d.fresh_fvar();
                let ha = d.kernel().fvar(ha_fv);
                let ha_ty = d.lt(a, n);

                // op a 0 = mod(a+0)n = mod a n = a.
                let a_plus_0 = d.add(a, zero);
                let add_zero_pf = d.lemma(p.add_zero, &[a]); // a+0=a
                let left_congr = d.congr(a_plus_0, a, add_zero_pf, &|d, v| d.modulo(v, n));
                let mod_a_n_eq_a = d.lemma(p.mod_eq_self_of_lt, &[a, n, ha]); // mod a n = a
                let left_eq_ty0 = d.modulo(a_plus_0, n);
                let mod_a_n = d.modulo(a, n);
                let left_final = d.trans(left_eq_ty0, mod_a_n, a, left_congr, mod_a_n_eq_a);

                // op 0 a = mod(0+a)n = mod a n = a.
                let zero_plus_a = d.add(zero, a);
                let zero_add_pf = d.lemma(p.zero_add, &[a]); // 0+a=a
                let right_congr = d.congr(zero_plus_a, a, zero_add_pf, &|d, v| d.modulo(v, n));
                let zero_plus_a_mod = d.modulo(zero_plus_a, n);
                let right_final = d.trans(zero_plus_a_mod, mod_a_n, a, right_congr, mod_a_n_eq_a);

                let left_ty = d.eq(left_eq_ty0, a);
                let right_ty = d.eq(zero_plus_a_mod, a);
                let both = d.const_app(
                    p.logic.and_intro,
                    &[left_ty, right_ty, left_final, right_final],
                );
                let with_ha = d.lam_fv(ha_fv, ha_ty, both);
                d.lam_fv(a_fv, nat, with_ha)
            };
            let bound_ty = d.lt(zero, n);
            let forall_ty = identity_forall_prop(d, op, zero, n);
            d.const_app(
                p.logic.and_intro,
                &[bound_ty, forall_ty, pos_n, forall_part],
            )
        };

        // inverse : ∀a,a<n→ inv a<n ∧ (op a(inv a)=0 ∧ op(inv a)a=0).
        let inverse_proof = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let ha_ty = d.lt(a, n);

            let diff = d.sub(n, a);
            let ia_lt = d.lemma(p.mod_lt, &[diff, n, pos_n]); // mod(sub n a)n < n
            let left_final = mod_add_right_inverse(d, &p, n, pos_n, a, ha);
            let right_final = mod_add_left_inverse(d, &p, n, pos_n, a, ha);

            let ia = d.modulo(diff, n);
            let a_ia = d.add(a, ia);
            let a_ia_mod = d.modulo(a_ia, n);
            let l_ty = d.eq(a_ia_mod, zero);
            let ia_a = d.add(ia, a);
            let ia_a_mod = d.modulo(ia_a, n);
            let r_ty = d.eq(ia_a_mod, zero);
            let eqs = d.const_app(p.logic.and_intro, &[l_ty, r_ty, left_final, right_final]);
            let ia_lt_ty = d.lt(ia, n);
            let eqs_ty = d.const_app(p.logic.and, &[l_ty, r_ty]);
            let bundle = d.const_app(p.logic.and_intro, &[ia_lt_ty, eqs_ty, ia_lt, eqs]);
            let with_ha = d.lam_fv(ha_fv, ha_ty, bundle);
            d.lam_fv(a_fv, nat, with_ha)
        };

        let logic = p.logic;
        let id_inv = d.const_app(
            logic.and_intro,
            &[identity_ty, inverse_ty, identity_proof, inverse_proof],
        );
        let assoc_rest_ty = d.const_app(logic.and, &[identity_ty, inverse_ty]);
        let assoc_rest = d.const_app(
            logic.and_intro,
            &[assoc_ty, assoc_rest_ty, assoc_proof, id_inv],
        );
        let rest_ty = d.const_app(logic.and, &[assoc_ty, assoc_rest_ty]);
        let full = d.const_app(
            logic.and_intro,
            &[closure_ty, rest_ty, closure_proof, assoc_rest],
        );

        let stmt_body = is_group_on(d, &p, op, e, inv, n);
        let stmt = d.arrow(pos_n_ty, stmt_body);
        let value = d.lam_fv(pos_n_fv, pos_n_ty, full);
        (stmt, value)
    })?;
    Ok(())
}

/// Admit `Nat.IsGroupOn` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_group_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_is_group_on(d, p)?;
    declare_group_identity_unique(d, p)?;
    declare_group_inverse_unique(d, p)?;
    declare_group_left_cancel(d, p)?;
    declare_mod_add_is_group(d, p)?;
    Ok(())
}
