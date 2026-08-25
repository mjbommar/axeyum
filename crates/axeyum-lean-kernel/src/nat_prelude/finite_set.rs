//! Finite sets over a bounded universe of naturals — curriculum node
//! [`sets`](../../../../docs/curriculum/00-foundations/sets.md), Layer 0, the
//! highest in-degree node in the whole DAG (4 dependents) and, before this
//! file, `covered` with zero kernel theorems: the curriculum prose names a
//! `BitVec`-exhaustive-check *exercise family* (`axeyum-scenarios::Family::Sets`),
//! not a kernel declaration — nothing here named a set operation.
//!
//! This kernel has no `List`, `Finset`, or tuple type, so a set is what the
//! curriculum node's own "Testable in axeyum" section already commits to: a
//! **characteristic function** `Nat → Bool`, and membership over a *bounded*
//! range `[0, n)` is exactly what [`totient.rs`](super::totient)'s
//! `Nat.countRange p n := |{k < n : p k = true}|` already counts. That is the
//! cardinality operator for this representation; it was built for the
//! totient and reused here unchanged.
//!
//! **Definitions** (plain predicate combinators, `Bool`-valued so union,
//! intersection, complement, and difference stay computable): [`declare_set_union`]
//! (`Nat.setUnion p q k := if p k then true else q k`), [`declare_set_inter`]
//! (`if p k then q k else false`), [`declare_set_compl`] (`if p k then false
//! else true`), [`declare_set_diff`] (`p k` and not `q k`) — each a bare
//! `Bool.rec` selection, built via the local [`bool_select_bool`] (the `Bool`
//! -codomain sibling of [`NatOps::bool_select_nat`], which this prelude did
//! not yet have). [`declare_subset`] is the `Prop`-valued `Nat.Subset p q n :=
//! ∀ k, k < n → p k = true → q k = true`, the same "definition with a `Prop`
//! body" shape [`super::finite::declare_injective_surjective`] already uses
//! for `Nat.injectiveOn`.
//!
//! **Theorems.** [`declare_count_range_union_add_inter`] is the two-set
//! inclusion–exclusion law, stated ADDITIVELY (`Nat.sub` is truncated, and the
//! familiar subtractive form needs a `≤` side condition this one does not):
//! `countRange (union p q) n + countRange (inter p q) n = countRange p n +
//! countRange q n`. By induction on `n`; the step needs only ONE nontrivial
//! per-element fact ([`union_inter_sum_eq`]) — that
//! `sel(union a b) + sel(inter a b) = sel a + sel b` for arbitrary `a b :
//! Bool` — proved by a SINGLE `Bool.rec` on `a` alone (not a nested case
//! split on `b`): at `a = true` both sides reduce to the identical term
//! `1 + sel b` by pure `ι`/`δ` reduction (`Bool.rec` fires on the *outer*
//! condition and both branches happen to name `b`'s slot the same way), and
//! at `a = false` the two sides differ only by `add`'s argument order
//! (`sel b + 0` vs `0 + sel b`), closed by `zero_add` — no case split on `b`
//! is needed in either branch. The four-term regroup
//! `(A+a)+(B+b) = (A+B)+(a+b)` this step also needs is
//! [`add_regroup_four`], the same private lemma
//! [`fibonacci.rs`](super::fibonacci)'s `fib_add` built (this prelude has no
//! `add_add_add_comm`; the per-file-private-copy convention is deliberate,
//! see that file's own comment).
//!
//! [`declare_count_range_le_of_subset`] is cardinality monotonicity:
//! `Subset p q n → countRange p n ≤ countRange q n`, by induction on `n` with
//! the hypothesis carried through the motive (`super::totient`'s
//! `countRange_eq_pred_of_only_zero_false` is the template: a motive that is
//! itself an arrow, so the induction hypothesis is a function to apply, not a
//! bare fact). The step's own per-element fact is
//! [`le_sel_of_bool_impl`]: `(a = true → b = true) → sel a ≤ sel b`, again a
//! single `Bool.rec` on `a` (the `a = false` branch never needs the
//! hypothesis at all — `zero_le` closes it unconditionally; the `a = true`
//! branch applies the hypothesis to `Eq.refl true` and transports `le_refl 1`
//! along the resulting `b = true`).
//!
//! [`declare_count_range_compl`] (the task's optional 4th step, landed
//! because its per-element fact needs no lemma at all —
//! [`compl_sum_eq`]'s two `Bool.rec` branches are both bare `Eq.refl`, since
//! `compl`'s two outputs are the *literal* constructors `false`/`true`, not
//! a free `q k`): `countRange p n + countRange (compl p) n = n`.
//!
//! Every declaration here computes: `nat_prelude_tests.rs`'s
//! `finite_set_operations_compute_on_a_concrete_pair` builds two singleton
//! predicates over `{0,1,2}` and checks `def_eq` on every operation at every
//! point, WITH negative controls — a set operation that type-checks but
//! computes the wrong membership has an empty axiom footprint and passes
//! every sweep in this repository otherwise.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ============================================================================
// `bool_select_bool` — the `Bool`-codomain sibling of `NatOps::bool_select_nat`.
// ============================================================================

/// `Bool.rec (fun _ => Bool) on_false on_true condition : Bool` — computational
/// `if condition then on_true else on_false` at `Bool` itself. Exactly
/// [`NatOps::bool_select_nat`]'s construction with the motive's codomain
/// changed from `Nat` to `Bool` (both live at the same universe level, so the
/// `Bool.rec` level argument is unchanged: [`NatOps::level_one`]).
fn bool_select_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(bool_rec, &[motive, on_false, on_true, condition])
}

/// `countRange(d, p, f, n)`, i.e. `d.const_app(p.count_range, &[f, n])` — the
/// same one-liner [`super::totient`]'s private `count_range` builds; not
/// exported, so this file carries its own copy (this prelude's per-file
/// convention).
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

// ============================================================================
// The set operations as predicate combinators.
// ============================================================================

/// `Nat.setUnion p q := fun k => if p k then true else q k`.
pub(super) fn declare_set_union(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let true_ = d.bool_true();
        let sel = bool_select_bool(d, &p, fk, true_, gk);
        d.lam_fv(k_fv, nat, sel)
    };
    let value = {
        let with_g = d.lam_fv(g_fv, pred_ty, body);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    let ty = {
        let over_g = d.arrow(pred_ty, pred_ty);
        d.arrow(pred_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.set_union,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(20),
    })?;
    Ok(())
}

/// `Nat.setInter p q := fun k => if p k then q k else false`.
pub(super) fn declare_set_inter(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let false_ = d.bool_false();
        let sel = bool_select_bool(d, &p, fk, gk, false_);
        d.lam_fv(k_fv, nat, sel)
    };
    let value = {
        let with_g = d.lam_fv(g_fv, pred_ty, body);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    let ty = {
        let over_g = d.arrow(pred_ty, pred_ty);
        d.arrow(pred_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.set_inter,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(21),
    })?;
    Ok(())
}

/// `Nat.setCompl p := fun k => if p k then false else true`.
pub(super) fn declare_set_compl(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let false_ = d.bool_false();
        let true_ = d.bool_true();
        let sel = bool_select_bool(d, &p, fk, false_, true_);
        d.lam_fv(k_fv, nat, sel)
    };
    let value = d.lam_fv(f_fv, pred_ty, body);
    let ty = d.arrow(pred_ty, pred_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.set_compl,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(22),
    })?;
    Ok(())
}

/// `Nat.setDiff p q := fun k => if p k then (if q k then false else true) else false`
/// — `p k ∧ ¬ q k`.
pub(super) fn declare_set_diff(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let false_ = d.bool_false();
        let true_ = d.bool_true();
        let not_gk = bool_select_bool(d, &p, gk, false_, true_);
        let false2 = d.bool_false();
        let sel = bool_select_bool(d, &p, fk, not_gk, false2);
        d.lam_fv(k_fv, nat, sel)
    };
    let value = {
        let with_g = d.lam_fv(g_fv, pred_ty, body);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    let ty = {
        let over_g = d.arrow(pred_ty, pred_ty);
        d.arrow(pred_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.set_diff,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(23),
    })?;
    Ok(())
}

/// `Nat.Subset p q n := ∀ k, k < n → p k = true → q k = true` — a `Prop`-valued
/// `Definition`, exactly the shape
/// [`super::finite::declare_injective_surjective`]'s `Nat.injectiveOn` already
/// uses (a Pi type into `Sort 0`).
pub(super) fn declare_subset(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let prop = d.kernel().sort_zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let bound = d.lt(k, n);
    let fk = d.apply(f, &[k]);
    let true_ = d.bool_true();
    let mem_f = d.bool_eq(fk, true_);
    let gk = d.apply(g, &[k]);
    let mem_g = d.bool_eq(gk, true_);
    let inner = d.arrow(mem_f, mem_g);
    let with_bound = d.arrow(bound, inner);
    let body = d.pi_fv(k_fv, nat, with_bound);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_g = d.arrow(pred_ty, over_n);
        d.arrow(pred_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.subset,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(24),
    })?;
    Ok(())
}

// ============================================================================
// `Nat.countRange_union_add_inter`.
// ============================================================================

/// `Eq Nat (add (add a b) (add c e)) (add (add a c) (add b e))` — the private
/// four-term commutative regroup [`super::fibonacci`]'s `fib_add` already
/// built (this prelude has no `add_add_add_comm`; per-file-private copies are
/// this prelude's own convention, see that file's module doc). Reused
/// verbatim: `(a+b)+(c+e) = ((a+b)+c)+e` [`add_assoc`, reversed] `=
/// ((a+c)+b)+e` [`add_right_comm` on the inner pair, under `(-)+e`] `=
/// (a+c)+(b+e)` [`add_assoc`].
fn add_regroup_four(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    let p = *p;
    let ab = d.add(a, b);
    let ce = d.add(c, e);
    let start = d.add(ab, ce);

    let abc = d.add(ab, c);
    let step1 = d.add(abc, e);
    let h1 = {
        let fwd = d.lemma(p.add_assoc, &[ab, c, e]);
        d.symm(step1, start, fwd)
    };

    let ac = d.add(a, c);
    let acb = d.add(ac, b);
    let step2 = d.add(acb, e);
    let h2 = {
        let h_comm = d.lemma(p.add_right_comm, &[a, b, c]);
        d.congr(abc, acb, h_comm, &|d, x| d.add(x, e))
    };

    let be = d.add(b, e);
    let target = d.add(ac, be);
    let h3 = d.lemma(p.add_assoc, &[ac, b, e]);

    let (_end, proof) = d.chain(start, &[(step1, h1), (step2, h2), (target, h3)]);
    proof
}

/// `∀ a b : Bool, Eq Nat (add (sel (union a b)) (sel (inter a b))) (add (sel a) (sel b))`
/// where `sel x := bool_select_nat x 1 0` — the per-element fact
/// `countRange_union_add_inter`'s step needs. A SINGLE `Bool.rec` on `a`
/// (`b` stays free throughout, never split):
///
/// - `a = true`: `union true b ≡ true`, `inter true b ≡ b`, so the LHS is
///   `sel true + sel b` and the RHS (`sel true + sel b`) is the *same term*
///   — `Eq.refl`.
/// - `a = false`: `union false b ≡ b`, `inter false b ≡ false`, so the LHS
///   reduces (by `add`'s own `x + 0 ≡ x` rule) to `sel b`, but the RHS
///   `0 + sel b` does not reduce further without knowing `b` — closed by
///   `zero_add` and `symm`, no case split on `b`.
fn union_inter_sum_eq(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let one = d.num(1);
    let zero = d.zero();
    let sel_b = d.bool_select_nat(b, one, zero);

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let union_xb = bool_select_bool(d, &p_, x, true_, b);
        let inter_xb = bool_select_bool(d, &p_, x, b, false_);
        let one_u = d.num(1);
        let zero_u = d.zero();
        let sel_union = d.bool_select_nat(union_xb, one_u, zero_u);
        let one_i = d.num(1);
        let zero_i = d.zero();
        let sel_inter = d.bool_select_nat(inter_xb, one_i, zero_i);
        let lhs = d.add(sel_union, sel_inter);
        let one_x = d.num(1);
        let zero_x = d.zero();
        let sel_x = d.bool_select_nat(x, one_x, zero_x);
        let rhs = d.add(sel_x, sel_b);
        let stmt = d.eq(lhs, rhs);
        d.lam_fv(x_fv, bool_ty, stmt)
    };

    let case_false = {
        let zero_add_proof = d.lemma(p_.zero_add, &[sel_b]);
        let zero2 = d.zero();
        let add_zero_b = d.add(zero2, sel_b);
        d.symm(add_zero_b, sel_b, zero_add_proof)
    };
    let case_true = {
        let one_t = d.num(1);
        let sum = d.add(one_t, sel_b);
        d.refl(sum)
    };

    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, a])
}

/// `Nat.countRange_union_add_inter : ∀ p q n,
///   Eq Nat (add (countRange (setUnion p q) n) (countRange (setInter p q) n))
///          (add (countRange p n) (countRange q n))` — the two-set
/// inclusion–exclusion law, stated additively.
pub(super) fn declare_count_range_union_add_inter(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let union_fg = d.const_app(p.set_union, &[f, g]);
    let inter_fg = d.const_app(p.set_inter, &[f, g]);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let cu = count_range(d, &p, union_fg, x);
        let ci = count_range(d, &p, inter_fg, x);
        let cf = count_range(d, &p, f, x);
        let cg = count_range(d, &p, g, x);
        let lhs = d.add(cu, ci);
        let rhs = d.add(cf, cg);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, m, ih| {
            let a_ = count_range(d, &p, union_fg, m);
            let b_ = count_range(d, &p, inter_fg, m);
            let c_ = count_range(d, &p, f, m);
            let dd = count_range(d, &p, g, m);

            let fm = d.apply(f, &[m]);
            let gm = d.apply(g, &[m]);
            let one = d.num(1);
            let zero = d.zero();
            let selp = d.bool_select_nat(fm, one, zero);
            let one2 = d.num(1);
            let zero2 = d.zero();
            let selq = d.bool_select_nat(gm, one2, zero2);

            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let union_fm_gm = bool_select_bool(d, &p, fm, true_, gm);
            let inter_fm_gm = bool_select_bool(d, &p, fm, gm, false_);
            let one3 = d.num(1);
            let zero3 = d.zero();
            let selu = d.bool_select_nat(union_fm_gm, one3, zero3);
            let one4 = d.num(1);
            let zero4 = d.zero();
            let seli = d.bool_select_nat(inter_fm_gm, one4, zero4);

            let start = {
                let l = d.add(a_, selu);
                let r = d.add(b_, seli);
                d.add(l, r)
            };
            let ab = d.add(a_, b_);
            let selu_seli = d.add(selu, seli);
            let mid1 = d.add(ab, selu_seli);
            let h_a = add_regroup_four(d, &p, a_, selu, b_, seli);

            let cd = d.add(c_, dd);
            let mid1b = d.add(cd, selu_seli);
            let h_b1 = d.congr(ab, cd, ih, &|d, t| d.add(t, selu_seli));

            let sel_eq = union_inter_sum_eq(d, &p, fm, gm);
            let selp_selq = d.add(selp, selq);
            let mid2 = d.add(cd, selp_selq);
            let h_b2 = d.congr(selu_seli, selp_selq, sel_eq, &|d, t| d.add(cd, t));

            let target = {
                let l = d.add(c_, selp);
                let r = d.add(dd, selq);
                d.add(l, r)
            };
            let h_c = add_regroup_four(d, &p, c_, dd, selp, selq);

            let (_end, proof) = d.chain(
                start,
                &[(mid1, h_a), (mid1b, h_b1), (mid2, h_b2), (target, h_c)],
            );
            proof
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_n);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.count_range_union_add_inter, ty, value)
}

// ============================================================================
// `Nat.countRange_le_of_subset`.
// ============================================================================

/// `a b : Bool ⊢ (Eq Bool a true → Eq Bool b true) → Le (sel a) (sel b)` where
/// `sel x := bool_select_nat x 1 0` — the per-element fact
/// `countRange_le_of_subset`'s step needs. A single `Bool.rec` on `a`: at
/// `a = false` the hypothesis is unused, `zero_le` closes it unconditionally;
/// at `a = true` the hypothesis applied to `Eq.refl true` gives `b = true`,
/// and `le_refl 1 : Le 1 (sel true)` transports along it to `Le 1 (sel b)`.
fn le_sel_of_bool_impl(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    imp: ExprId,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let eqxt = d.bool_eq(x, true_);
        let eqbt = d.bool_eq(b, true_);
        let hyp_ty = d.arrow(eqxt, eqbt);
        let one = d.num(1);
        let zero = d.zero();
        let sel_x = d.bool_select_nat(x, one, zero);
        let one2 = d.num(1);
        let zero2 = d.zero();
        let sel_b = d.bool_select_nat(b, one2, zero2);
        let concl = d.le(sel_x, sel_b);
        let body = d.arrow(hyp_ty, concl);
        d.lam_fv(x_fv, bool_ty, body)
    };

    let case_false = {
        let hyp_fv = d.fresh_fvar();
        let eqft = d.bool_eq(false_, true_);
        let eqbt = d.bool_eq(b, true_);
        let hyp_ty = d.arrow(eqft, eqbt);
        let one = d.num(1);
        let zero = d.zero();
        let sel_b = d.bool_select_nat(b, one, zero);
        let body = d.lemma(p_.zero_le, &[sel_b]);
        d.lam_fv(hyp_fv, hyp_ty, body)
    };

    let case_true = {
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let eqtt = d.bool_eq(true_, true_);
        let eqbt = d.bool_eq(b, true_);
        let hyp_ty = d.arrow(eqtt, eqbt);
        let refl_true = d.bool_refl(true_);
        let hb = d.apply(hyp, &[refl_true]);
        let symm_hb = d.bool_symm(b, true_, hb);
        let motive2 = d.bool_eq_motive(true_, &|d, x| {
            let one_i = d.num(1);
            let zero_i = d.zero();
            let sel_x = d.bool_select_nat(x, one_i, zero_i);
            let one_i2 = d.num(1);
            d.le(one_i2, sel_x)
        });
        let one3 = d.num(1);
        let refl_case = d.lemma(p_.le_refl, &[one3]);
        let result = d.bool_transport(true_, motive2, refl_case, b, symm_hb);
        d.lam_fv(hyp_fv, hyp_ty, result)
    };

    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    let applied = d.apply(bool_rec, &[motive, case_false, case_true, a]);
    d.apply(applied, &[imp])
}

/// `Nat.countRange_le_of_subset : ∀ p q n,
///   Subset p q n → Le (countRange p n) (countRange q n)` — cardinality
/// monotonicity. Induction on `n` with the `Subset` hypothesis carried
/// through the motive, exactly [`super::totient::declare_count_range_eq_pred_of_only_zero_false`]'s
/// shape.
pub(super) fn declare_count_range_le_of_subset(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let subset_ty = d.const_app(p.subset, &[f, g, x]);
        let cf = count_range(d, &p, f, x);
        let cg = count_range(d, &p, g, x);
        let concl = d.le(cf, cg);
        d.arrow(subset_ty, concl)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = d.const_app(p.subset, &[f, g, zero]);
            let hyp_fv = d.fresh_fvar();
            let body = d.lemma(p.le_refl, &[zero]);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let hyp2_ty = d.const_app(p.subset, &[f, g, sm]);
            let hyp2_fv = d.fresh_fvar();
            let hyp2 = d.kernel().fvar(hyp2_fv);

            // Restrict `hyp2` (bound `k < succ m`) to `Subset f g m`, for the IH.
            let restricted = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let bound_ty = d.lt(k, m);
                let bound_fv = d.fresh_fvar();
                let bound_hyp = d.kernel().fvar(bound_fv);
                let true_ = d.bool_true();
                let fk = d.apply(f, &[k]);
                let mem_f_ty = d.bool_eq(fk, true_);
                let mem_fv = d.fresh_fvar();
                let mem_hyp = d.kernel().fvar(mem_fv);
                let succ_k = d.succ(k);
                let lifted_bound = d.lemma(p.le_step, &[succ_k, m, bound_hyp]);
                let applied = d.apply(hyp2, &[k, lifted_bound, mem_hyp]);
                let with_mem = d.lam_fv(mem_fv, mem_f_ty, applied);
                let with_bound = d.lam_fv(bound_fv, bound_ty, with_mem);
                d.lam_fv(k_fv, nat, with_bound)
            };
            let ih_applied = d.apply(ih, &[restricted]);

            let fm = d.apply(f, &[m]);
            let gm = d.apply(g, &[m]);

            let sel_le = {
                let sm_le = d.lemma(p.le_refl, &[sm]);
                let true_ = d.bool_true();
                let mem_f_ty = d.bool_eq(fm, true_);
                let mem_fv = d.fresh_fvar();
                let mem_hyp = d.kernel().fvar(mem_fv);
                let applied = d.apply(hyp2, &[m, sm_le, mem_hyp]);
                let imp = d.lam_fv(mem_fv, mem_f_ty, applied);
                le_sel_of_bool_impl(d, &p, fm, gm, imp)
            };

            let cf_m = count_range(d, &p, f, m);
            let cg_m = count_range(d, &p, g, m);
            let one = d.num(1);
            let zero = d.zero();
            let selp = d.bool_select_nat(fm, one, zero);
            let one2 = d.num(1);
            let zero2 = d.zero();
            let selq = d.bool_select_nat(gm, one2, zero2);

            let step1 = d.lemma(p.add_le_add_right, &[selp, cf_m, cg_m, ih_applied]);
            let step2 = d.lemma(p.add_le_add_left, &[cg_m, selp, selq, sel_le]);
            let cf_sm = d.add(cf_m, selp);
            let cg_m_selp = d.add(cg_m, selp);
            let cg_sm = d.add(cg_m, selq);
            let final_le = d.lemma(p.le_trans, &[cf_sm, cg_m_selp, cg_sm, step1, step2]);

            d.lam_fv(hyp2_fv, hyp2_ty, final_le)
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_n);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.count_range_le_of_subset, ty, value)
}

// ============================================================================
// `Nat.countRange_compl` (the task's optional 4th step).
// ============================================================================

/// `a : Bool ⊢ Eq Nat (add (sel a) (sel (compl a))) 1` where
/// `sel x := bool_select_nat x 1 0` — the per-element fact
/// `countRange_compl`'s step needs. Both `Bool.rec` branches are bare
/// `Eq.refl`: unlike [`union_inter_sum_eq`], `compl`'s two outputs are the
/// literal constructors `false`/`true` (never a free `q k`), so both sides
/// collapse to the numeral `1` by pure `ι`/`δ` reduction with no lemma at
/// all.
fn compl_sum_eq(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let compl_x = bool_select_bool(d, &p_, x, false_, true_);
        let one_x = d.num(1);
        let zero_x = d.zero();
        let sel_x = d.bool_select_nat(x, one_x, zero_x);
        let one_c = d.num(1);
        let zero_c = d.zero();
        let sel_compl = d.bool_select_nat(compl_x, one_c, zero_c);
        let lhs = d.add(sel_x, sel_compl);
        let one_r = d.num(1);
        let stmt = d.eq(lhs, one_r);
        d.lam_fv(x_fv, bool_ty, stmt)
    };
    let case_false = {
        let one_v = d.num(1);
        d.refl(one_v)
    };
    let case_true = {
        let one_v = d.num(1);
        d.refl(one_v)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, a])
}

/// `Nat.countRange_compl : ∀ p n,
///   Eq Nat (add (countRange p n) (countRange (setCompl p) n)) n`.
pub(super) fn declare_count_range_compl(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let compl_f = d.const_app(p.set_compl, &[f]);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let cf = count_range(d, &p, f, x);
        let cc = count_range(d, &p, compl_f, x);
        let lhs = d.add(cf, cc);
        d.eq(lhs, x)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, m, ih| {
            let a_ = count_range(d, &p, f, m);
            let b_ = count_range(d, &p, compl_f, m);
            let fm = d.apply(f, &[m]);
            let one = d.num(1);
            let zero = d.zero();
            let selp = d.bool_select_nat(fm, one, zero);
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let compl_fm = bool_select_bool(d, &p, fm, false_, true_);
            let one2 = d.num(1);
            let zero2 = d.zero();
            let selc = d.bool_select_nat(compl_fm, one2, zero2);

            let start = {
                let l = d.add(a_, selp);
                let r = d.add(b_, selc);
                d.add(l, r)
            };
            let ab = d.add(a_, b_);
            let selp_selc = d.add(selp, selc);
            let mid1 = d.add(ab, selp_selc);
            let h_a = add_regroup_four(d, &p, a_, selp, b_, selc);

            let mid1b = d.add(m, selp_selc);
            let h_b1 = d.congr(ab, m, ih, &|d, t| d.add(t, selp_selc));

            let sel_eq = compl_sum_eq(d, &p, fm);
            let one3 = d.num(1);
            let target = d.add(m, one3);
            let h_b2 = d.congr(selp_selc, one3, sel_eq, &|d, t| d.add(m, t));

            let (_end, proof) = d.chain(start, &[(mid1, h_a), (mid1b, h_b1), (target, h_b2)]);
            proof
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    d.declare_theorem(p.count_range_compl, ty, value)
}

/// Declare `Nat.setUnion`/`setInter`/`setCompl`/`setDiff`/`Subset` and the
/// three `countRange` cardinality laws, in dependency order. Must run AFTER
/// [`super::totient::declare_totient_all`] (`Nat.countRange` itself).
pub(super) fn declare_finite_set_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_set_union(d, p)?;
    declare_set_inter(d, p)?;
    declare_set_compl(d, p)?;
    declare_set_diff(d, p)?;
    declare_subset(d, p)?;
    declare_count_range_union_add_inter(d, p)?;
    declare_count_range_le_of_subset(d, p)?;
    declare_count_range_compl(d, p)?;
    Ok(())
}
