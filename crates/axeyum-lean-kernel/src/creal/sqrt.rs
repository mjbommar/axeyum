//! **`CReal.natSqrt`**: the integer square root, by structural recursion, with
//! its defining two-sided bound — the missing computational primitive behind
//! `CReal.sqrt`.
//!
//! ## Why this file exists, and why it stops here
//!
//! `CReal.sqrt`'s only genuinely hard part is not real-analysis machinery —
//! `equiv_of_bounded`, `regular_between`, `fuse_at`
//! ([`super::product`]) and `ratSqLe`/`ratSqSandwich`
//! ([`super::mul_self_zero`]) already give the CReal-level estimate template
//! (see that module's docs: the sandwich lemma turns a rational bound on a
//! *square* directly into a `CReal.Within`, with no division and no case split
//! on which of two reals is bigger). What is missing is a **rational square
//! root approximation with a proven error bound**, and nothing in the trusted
//! library computes one: `RatPrelude` has no `sqrt`/`pow`-inverse, and the one
//! natural place to build it — `Nat`'s own integer square root — does not
//! exist in `nat_prelude` either.
//!
//! Building that primitive needs a genuine **decidable, data-level** search
//! (unlike every real-order fact in this module, which is `Prop`-valued and
//! cannot select data — see [`CReal.inv`](super::CRealPrelude::inv)'s own
//! docs on exactly this restriction). The tool that makes it possible without
//! any new axiom is [`NatOps::ble`](crate::nat_prelude::NatOps::ble) (`Bool`,
//! not `Prop`, so `Bool.rec` may select a `Nat` freely) together with
//! [`NatOps::bool_select_nat`](crate::nat_prelude::NatOps::bool_select_nat)
//! (already built, and already used by `Nat.div`/`Nat.mod`'s own executable
//! state — [`nat_prelude::division`](crate::nat_prelude) — which is the
//! template this file follows).
//!
//! **This slice stays at the `Nat` level on purpose.** Lifting `natSqrt` to a
//! rational approximant of a `CReal` sample needs a decidable comparison for
//! `Rat`/`Int` (built from `Nat.ble` by a constructor case split on `Int`,
//! itself unproblematic since `Int.rec` eliminates into any `Sort` — `Int` is
//! a `Type`, not a `Prop`) and then the sampling-index schedule that
//! compensates for `sqrt` **not** being Lipschitz at `0` (its modulus of
//! continuity is itself a square root: `|sqrt a − sqrt b| ≤ sqrt |a−b|`,
//! provable from `ratSqSandwich` applied to `sqrt a − sqrt b` without ever
//! dividing by `sqrt a + sqrt b`, which is what makes `0 ≤ x` — not
//! `PosBound x k` — the honest hypothesis for `CReal.sqrt`, unlike
//! `CReal.inv`: nothing here needs to *decide* how close to zero `x` is,
//! only to *sample deeper* as the target precision tightens). That remaining
//! climb is real-analysis-sized on its own (`CReal.mul`'s `product.rs` is
//! 2400+ lines; `mul_self_zero.rs`, reusing most of that, still took a
//! four-lane chain — its own commit message says so) and is exactly the
//! obstruction named in this slice's report, not solved by it.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

use super::{CRealPrelude, and_intro};

/// `And left right`, as a `Prop`. Generic over what `left`/`right` are —
/// unlike [`super::equiv`]/[`super::within`], this file's statements are
/// plain `Nat` facts, so there is no `CReal`-specific packaging to reuse.
fn and_ty(d: &mut IntDev<'_>, p: CRealPrelude, left: ExprId, right: ExprId) -> ExprId {
    d.const_app(p.rat.int.logic.and, &[left, right])
}

/// From `h : Eq Bool b Bool.false`, derive `Not (Eq Bool b Bool.true)`.
///
/// `b`'s two possible values are mutually exclusive
/// ([`NatOps::false_true_elim`](crate::nat_prelude::NatOps::false_true_elim)
/// is the existing `Bool.false ≠ Bool.true` discriminator); this is the
/// one-line bridge from "`b` computed to `false`" to "`b` did not compute to
/// `true`", needed to reach [`RatPrelude`](crate::RatPrelude)'s Nat-level
/// `not_le_of_not_ble_eq_true` from the *other* branch of a
/// [`NatOps::bool_select_nat`] discriminant.
fn not_bool_eq_true_of_false(d: &mut IntDev<'_>, b: ExprId, h_false: ExprId) -> ExprId {
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let sym = d.bool_symm(b, false_, h_false);
    let h2_ty = d.bool_eq(b, true_);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let contra = d.bool_trans(false_, b, true_, sym, h2);
    let false_name = d.prelude().logic.false_;
    let false_ty = d.kernel().const_(false_name, vec![]);
    let body = d.false_true_elim(false_ty, contra);
    d.lam_fv(h2_fv, h2_ty, body)
}

/// `Nat.le (Nat.succ (Nat.mul a a)) (Nat.mul (Nat.succ a) (Nat.succ a))` —
/// `(a+1)² ≥ a²+1`, the one algebraic fact the successor case of
/// [`declare_nat_sqrt_spec`] needs to grow the upper bound.
///
/// `(a+1)·(a+1) = ((a·a)+a)+(a+1)` (`succ_mul` then `mul_succ`, folded by one
/// `congr`); `succ(a·a) = (a·a)+1 ≤ (a·a)+(a+1)` (`1 ≤ a+1` is
/// `le_succ_succ` at `zero_le a`, scaled by `add_le_add_left`); and
/// `(a·a)+(a+1) ≤ ((a·a)+a)+(a+1)` is `le_add_right` scaled by
/// `add_le_add_right`. `le_trans` composes the two, and the whole thing is
/// rewritten back along the opening identity.
fn sq_step_bound(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let pa = d.mul(a, a);
    let succ_a = d.succ(a);

    // (a+1)*(a+1) = ((a*a)+a)+(a+1).
    let a_succ_a = d.mul(a, succ_a);
    let pa_plus_a = d.add(pa, a);
    let step_succ_mul = d.const_app(nat.succ_mul, &[a, succ_a]);
    let step_mul_succ = d.const_app(nat.mul_succ, &[a, a]);
    let lhs0 = d.mul(succ_a, succ_a);
    let mid0 = d.add(a_succ_a, succ_a);
    let rhs0 = d.add(pa_plus_a, succ_a);
    let congr1 = d.congr(a_succ_a, pa_plus_a, step_mul_succ, &|d, t| d.add(t, succ_a));
    let (_, whole_eq) = d.chain(lhs0, &[(mid0, step_succ_mul), (rhs0, congr1)]);

    // succ(a*a) <= (a*a) + (a+1), via (a*a)+1 = succ(a*a) and 1 <= a+1.
    let zero = d.zero();
    let one = d.succ(zero);
    let zero_le_a = d.const_app(nat.zero_le, &[a]);
    let one_le_succ_a = d.const_app(nat.le_succ_succ, &[zero, a, zero_le_a]);
    let pa_one = d.add(pa, one);
    let pa_succ_a = d.add(pa, succ_a);
    let add_le_1 = d.const_app(nat.add_le_add_left, &[pa, one, succ_a, one_le_succ_a]);
    let add_succ_pa = d.const_app(nat.add_succ, &[pa, zero]);
    let pa_zero = d.add(pa, zero);
    let add_zero_pa = d.const_app(nat.add_zero, &[pa]);
    let congr2 = d.congr(pa_zero, pa, add_zero_pa, &|d, t| d.succ(t));
    let succ_pa_zero = d.succ(pa_zero);
    let succ_pa = d.succ(pa);
    let (_, pa_one_eq_succ_pa) = d.chain(pa_one, &[(succ_pa_zero, add_succ_pa), (succ_pa, congr2)]);
    let add_le_1_at_succ_pa = {
        let motive = d.eq_motive(pa_one, &|d, t| d.le(t, pa_succ_a));
        d.transport(pa_one, motive, add_le_1, succ_pa, pa_one_eq_succ_pa)
    };
    // add_le_1_at_succ_pa : Le (succ pa) pa_succ_a

    // (a*a)+(a+1) <= ((a*a)+a)+(a+1), via (a*a) <= (a*a)+a.
    let le_add_right_pa_a = d.const_app(nat.le_add_right, &[pa, a]);
    let add_le_2 = d.const_app(
        nat.add_le_add_right,
        &[succ_a, pa, pa_plus_a, le_add_right_pa_a],
    );
    // add_le_2 : Le pa_succ_a rhs0

    let combined = d.const_app(
        nat.le_trans,
        &[succ_pa, pa_succ_a, rhs0, add_le_1_at_succ_pa, add_le_2],
    );
    // combined : Le (succ pa) rhs0

    let whole_eq_rev = d.symm(lhs0, rhs0, whole_eq);
    let motive2 = d.eq_motive(rhs0, &|d, t| d.le(succ_pa, t));
    d.transport(rhs0, motive2, combined, lhs0, whole_eq_rev)
}

/// `CReal.natSqrt : Nat -> Nat`, by structural recursion:
///
/// ```text
/// natSqrt 0        = 0
/// natSqrt (succ j) = let c := succ (natSqrt j)
///                     if Nat.ble (c*c) (succ j) then c else natSqrt j
/// ```
///
/// The single running candidate (rather than `Nat.choose`'s two-argument row,
/// or `Nat.div`/`Nat.mod`'s shared quotient/remainder state) is enough here:
/// unlike division, there is nothing to reset, only ever to grow by at most
/// one per step.
fn declare_nat_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.zero();
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let candidate = d.succ(ih);
        let succ_j = d.succ(j);
        let sq = d.mul(candidate, candidate);
        let cond = d.ble(sq, succ_j);
        let selected = d.bool_select_nat(cond, candidate, ih);
        let with_ih = d.lam_fv(ih_fv, nat, selected);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec = d.kernel().const_(p.rat.int.nat.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    // Strictly greater delta height than `Nat.mul`/`Nat.ble` (both height 1).
    d.kernel().add_declaration(Declaration::Definition {
        name: p.nat_sqrt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })
}

/// `CReal.natSqrtSpec : ∀ n,
///   And (Nat.le (natSqrt n * natSqrt n) n)
///       (Nat.lt n (succ (natSqrt n) * succ (natSqrt n)))`.
///
/// By induction on `n`, proving both halves together (the successor case
/// needs the upper-bound IH to grow the lower bound and vice versa). The
/// step case's discriminant is exactly `natSqrt`'s own `Nat.ble` test; the
/// standard `Bool.rec`-applied-to-the-discriminant-itself trick (as in
/// `nat_prelude::division`'s executable spec proof) recovers each branch as
/// a hypothesis without a separate "cases on this Bool" lemma.
fn declare_nat_sqrt_spec(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = p.rat.int.nat;

    let spec = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        and_ty(d, p, left, right)
    };

    d.theorem(p.nat_sqrt_spec, 1, &|d, v| {
        let n = v[0];
        let stmt = spec(d, n);
        let proof = d.induct(
            &spec,
            &|d| {
                let zero = d.zero();
                let sqrt0 = d.const_app(p.nat_sqrt, &[zero]);
                let ss0 = d.mul(sqrt0, sqrt0);
                let left_ty = d.le(ss0, zero);
                let left_proof = d.const_app(nat.le_refl, &[zero]);
                let succ_sqrt0 = d.succ(sqrt0);
                let rhs = d.mul(succ_sqrt0, succ_sqrt0);
                let right_ty = d.lt(zero, rhs);
                let right_proof = d.zero_lt_succ(sqrt0);
                and_intro(d, p, left_ty, right_ty, left_proof, right_proof)
            },
            &|d, j, ih| {
                let s = d.const_app(p.nat_sqrt, &[j]);
                let ss = d.mul(s, s);
                let left_ih_ty = d.le(ss, j);
                let succ_s = d.succ(s);
                let s1s1 = d.mul(succ_s, succ_s);
                let right_ih_ty = d.lt(j, s1s1);
                let ih_left = d.and_left(left_ih_ty, right_ih_ty, ih);
                let ih_right = d.and_right(left_ih_ty, right_ih_ty, ih);

                let succ_j = d.succ(j);
                let condition = d.ble(s1s1, succ_j);
                let bool_ty = d.bool_ty();

                let target_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
                    let next = d.bool_select_nat(selector, succ_s, s);
                    let next_sq = d.mul(next, next);
                    let l = d.le(next_sq, succ_j);
                    let succ_next = d.succ(next);
                    let r_rhs = d.mul(succ_next, succ_next);
                    let r = d.lt(succ_j, r_rhs);
                    and_ty(d, p, l, r)
                };
                let branch_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
                    let eqty = d.bool_eq(condition, selector);
                    let tgt = target_for(d, selector);
                    d.arrow(eqty, tgt)
                };

                let false_ = d.bool_false();
                let false_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = d.bool_eq(condition, false_);
                    let left_proof = d.const_app(nat.le_step, &[ss, j, ih_left]);
                    let not_true = not_bool_eq_true_of_false(d, condition, h);
                    let not_le =
                        d.const_app(nat.not_le_of_not_ble_eq_true, &[s1s1, succ_j, not_true]);
                    let right_proof = d.const_app(nat.lt_of_not_le, &[s1s1, succ_j, not_le]);
                    let left_ty = d.le(ss, succ_j);
                    let right_ty = d.lt(succ_j, s1s1);
                    let body = and_intro(d, p, left_ty, right_ty, left_proof, right_proof);
                    d.lam_fv(h_fv, h_ty, body)
                };

                let true_ = d.bool_true();
                let true_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = d.bool_eq(condition, true_);
                    let left_proof = d.const_app(nat.le_of_ble_eq_true, &[s1s1, succ_j, h]);

                    let succ_succ_j = d.succ(succ_j);
                    let succ_s1s1 = d.succ(s1s1);
                    let step1 = d.const_app(nat.le_succ_succ, &[succ_j, s1s1, ih_right]);
                    let bound2 = sq_step_bound(d, p, succ_s);
                    let succ_s1 = d.succ(succ_s);
                    let target_rhs = d.mul(succ_s1, succ_s1);
                    let right_proof = d.const_app(
                        nat.le_trans,
                        &[succ_succ_j, succ_s1s1, target_rhs, step1, bound2],
                    );

                    let left_ty = d.le(s1s1, succ_j);
                    let right_ty = d.lt(succ_j, target_rhs);
                    let body = and_intro(d, p, left_ty, right_ty, left_proof, right_proof);
                    d.lam_fv(h_fv, h_ty, body)
                };

                let motive = {
                    let selector_fv = d.fresh_fvar();
                    let selector = d.kernel().fvar(selector_fv);
                    let body = branch_for(d, selector);
                    d.lam_fv(selector_fv, bool_ty, body)
                };
                let level_zero = d.kernel().level_zero();
                let bool_rec = d
                    .kernel()
                    .const_(p.rat.int.logic.bool_rec, vec![level_zero]);
                let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, condition]);
                let refl_cond = d.bool_refl(condition);
                d.apply(selected, &[refl_cond])
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `CReal.natSqrtLe : ∀ n, Nat.le (natSqrt n * natSqrt n) n` — the lower
/// projection of [`declare_nat_sqrt_spec`].
fn declare_nat_sqrt_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    d.theorem(p.nat_sqrt_le, 1, &|d, v| {
        let n = v[0];
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        let spec_const = d.kernel().const_(p.nat_sqrt_spec, vec![]);
        let full = d.apply(spec_const, &[n]);
        let proof = d.and_left(left, right, full);
        (left, proof)
    })?;
    Ok(())
}

/// `CReal.natSqrtLt : ∀ n, Nat.lt n (succ (natSqrt n) * succ (natSqrt n))` —
/// the upper projection of [`declare_nat_sqrt_spec`].
fn declare_nat_sqrt_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    d.theorem(p.nat_sqrt_lt, 1, &|d, v| {
        let n = v[0];
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        let spec_const = d.kernel().const_(p.nat_sqrt_spec, vec![]);
        let full = d.apply(spec_const, &[n]);
        let proof = d.and_right(left, right, full);
        (right, proof)
    })?;
    Ok(())
}

/// Admit `CReal.natSqrt`, `CReal.natSqrtSpec`, `CReal.natSqrtLe`,
/// `CReal.natSqrtLt`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_nat_sqrt(d, p)?;
    declare_nat_sqrt_spec(d, p)?;
    declare_nat_sqrt_le(d, p)?;
    declare_nat_sqrt_lt(d, p)
}
