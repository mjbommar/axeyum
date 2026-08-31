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
pub(super) fn compl_sum_eq(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
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

// ============================================================================
// Pointwise Boolean-lattice laws — the curriculum node's own claim ("the same
// Boolean laws as in propositional logic, one level up"), made a kernel
// theorem. Every statement is `∀ …, Eq Bool (… k) (… k)`, NOT an equality of
// functions: this kernel has no `funext`.
//
// `union_at`/`inter_at`/`compl_at` are the same `bool_select_bool` shapes
// [`declare_set_union`]/[`declare_set_inter`]/[`declare_set_compl`] build,
// factored out so every per-element proof below can share them; each
// declared theorem's STATEMENT still goes through the real `Nat.setUnion` /
// `Nat.setInter` / `Nat.setCompl` constants (delta-equal to these, so the
// kernel's own defeq check bridges the two — the same split the file already
// used for `countRange_union_add_inter`'s statement vs. `union_inter_sum_eq`'s
// proof).
//
// Every law here needs only ONE `Bool.rec` case split — on the outermost
// variable — except the two commutativity laws, which genuinely need both
// arguments concrete before either side reduces (`bool_split2`). The reason
// every other law collapses with a single split: `union`/`inter` branch only
// on their FIRST argument, so once that argument is a literal, one side
// short-circuits to a fixed value while the other reduces (by unfolding +
// ι, no lemma) to the identical residual — verified case-by-case in the
// doc comment of each `_at` function below.
// ============================================================================

/// `select(a, true_, b)` — [`declare_set_union`]'s body at a point, factored
/// out for the pointwise laws below.
fn union_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let true_ = d.bool_true();
    bool_select_bool(d, p, a, true_, b)
}

/// `select(a, b, false_)` — [`declare_set_inter`]'s body at a point.
fn inter_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let false_ = d.bool_false();
    bool_select_bool(d, p, a, b, false_)
}

/// `select(a, false_, true_)` — [`declare_set_compl`]'s body at a point.
fn compl_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    bool_select_bool(d, p, a, false_, true_)
}

/// One-variable `Bool.rec` case split on `a`: `case_true`/`case_false` supply
/// the proof of `goal(true)`/`goal(false)` (almost always a bare `Eq.refl`,
/// since every law using this helper reduces both sides of `goal(x)` to the
/// identical residual term once `x` is a literal). `goal` builds
/// `Eq Bool lhs(x) rhs(x)` for a placeholder `x : Bool`.
fn bool_split1(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    goal: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    case_true: &dyn Fn(&mut NatDev<'_>) -> ExprId,
    case_false: &dyn Fn(&mut NatDev<'_>) -> ExprId,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = goal(d, x);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true_term = case_true(d);
    let case_false_term = case_false(d);
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false_term, case_true_term, a])
}

/// The `a`-fixed half of [`bool_split2`]: case-splits on `b` alone, with `a`
/// already substituted by the literal `a_val` (`a_is_true` says which).
/// `leaf(a_is_true, b_is_true)` gives the `Bool` literal both sides reduce to.
fn bool_split2_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a_val: ExprId,
    a_is_true: bool,
    b: ExprId,
    goal: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    leaf: &dyn Fn(bool, bool) -> bool,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let motive = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let body = goal(d, a_val, y);
        d.lam_fv(y_fv, bool_ty, body)
    };
    let case_true_term = {
        let lit = if leaf(a_is_true, true) {
            d.bool_true()
        } else {
            d.bool_false()
        };
        d.bool_refl(lit)
    };
    let case_false_term = {
        let lit = if leaf(a_is_true, false) {
            d.bool_true()
        } else {
            d.bool_false()
        };
        d.bool_refl(lit)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false_term, case_true_term, b])
}

/// Two-variable `Bool.rec` case split (`a` then `b`) — for the two
/// commutativity laws, the only ones here where NEITHER argument's literal
/// value alone lets the other side reduce (unlike every other law, which
/// peels only its outermost condition; see the module doc above).
fn bool_split2(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    goal: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    leaf: &dyn Fn(bool, bool) -> bool,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let case_true_a = bool_split2_case(d, &p_, true_, true, b, goal, leaf);
    let case_false_a = bool_split2_case(d, &p_, false_, false, b, goal, leaf);
    let motive_outer = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = goal(d, x, b);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive_outer, case_false_a, case_true_a, a])
}

// --- the per-element facts --------------------------------------------------

/// `Eq Bool (union a b) (union b a)`. Genuinely needs both arguments split
/// (4 cases): at `a = true` alone, `union b a` is stuck on the free `b`
/// (`select(b, true_, true_)` does not ι-reduce without a literal `b`), even
/// though every branch is `true_` — `Bool.rec` has no case-irrelevance
/// principle for that. `leaf = a || b` in every one of the 4 concrete cases.
fn union_comm_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| -> ExprId {
        let lhs = union_at(d, &p_, x, y);
        let rhs = union_at(d, &p_, y, x);
        d.bool_eq(lhs, rhs)
    };
    let leaf = |x: bool, y: bool| -> bool { x || y };
    bool_split2(d, &p_, a, b, &goal, &leaf)
}

/// `Eq Bool (inter a b) (inter b a)`, the `inter` sibling of
/// [`union_comm_at`]; same reason for needing both arguments split.
fn inter_comm_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| -> ExprId {
        let lhs = inter_at(d, &p_, x, y);
        let rhs = inter_at(d, &p_, y, x);
        d.bool_eq(lhs, rhs)
    };
    let leaf = |x: bool, y: bool| -> bool { x && y };
    bool_split2(d, &p_, a, b, &goal, &leaf)
}

/// `Eq Bool (union (union a b) c) (union a (union b c))`. A SINGLE split on
/// `a`: at `a = true` both sides ι-reduce to `true_` without touching `b`/`c`
/// (union's `true` branch short-circuits); at `a = false` both sides ι-reduce
/// to the identical term `union b c` (union's `false` branch discards its own
/// left argument and defers to the right, on both sides alike).
fn union_assoc_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let xb = union_at(d, &p_, x, b);
        let lhs = union_at(d, &p_, xb, c);
        let bc = union_at(d, &p_, b, c);
        let rhs = union_at(d, &p_, x, bc);
        d.bool_eq(lhs, rhs)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let bc = union_at(d, &p_, b, c);
        d.bool_refl(bc)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (inter (inter a b) c) (inter a (inter b c))`, the `inter`
/// sibling of [`union_assoc_at`]. A single split on `a`: at `a = true` both
/// sides ι-reduce to the identical term `inter b c`; at `a = false` both
/// ι-reduce to `false_` (`inter`'s `false` branch is the fixed constant
/// `false_`, so it never even looks at the other operand).
fn inter_assoc_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let xb = inter_at(d, &p_, x, b);
        let lhs = inter_at(d, &p_, xb, c);
        let bc = inter_at(d, &p_, b, c);
        let rhs = inter_at(d, &p_, x, bc);
        d.bool_eq(lhs, rhs)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let bc = inter_at(d, &p_, b, c);
        d.bool_refl(bc)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (union a a) a` — a single split on `a`, both branches literal.
fn union_idem_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let lhs = union_at(d, &p_, x, x);
        d.bool_eq(lhs, x)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (inter a a) a`, the `inter` sibling of [`union_idem_at`].
fn inter_idem_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let lhs = inter_at(d, &p_, x, x);
        d.bool_eq(lhs, x)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (inter a (union b c)) (union (inter a b) (inter a c))` —
/// `setInter_union_distrib`'s per-element fact. A single split on `a`: at
/// `a = true`, both sides ι-reduce to the identical term `union b c`; at
/// `a = false`, both ι-reduce to `false_` (`inter`'s `false` branch is the
/// fixed constant on the left, and on the right `inter a b`/`inter a c` both
/// collapse to `false_` the same way before `union false_ false_` does too).
fn inter_union_distrib_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let qr = union_at(d, &p_, b, c);
        let lhs = inter_at(d, &p_, x, qr);
        let pq = inter_at(d, &p_, x, b);
        let pr = inter_at(d, &p_, x, c);
        let rhs = union_at(d, &p_, pq, pr);
        d.bool_eq(lhs, rhs)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let bc = union_at(d, &p_, b, c);
        d.bool_refl(bc)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (union a (inter b c)) (inter (union a b) (union a c))` —
/// `setUnion_inter_distrib`'s per-element fact, the dual of
/// [`inter_union_distrib_at`]. A single split on `a`: at `a = true`, both
/// sides ι-reduce to `true_`; at `a = false`, both ι-reduce to the identical
/// term `inter b c`.
fn union_inter_distrib_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let qr = inter_at(d, &p_, b, c);
        let lhs = union_at(d, &p_, x, qr);
        let pq = union_at(d, &p_, x, b);
        let pr = union_at(d, &p_, x, c);
        let rhs = inter_at(d, &p_, pq, pr);
        d.bool_eq(lhs, rhs)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let bc = inter_at(d, &p_, b, c);
        d.bool_refl(bc)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (union a (inter a b)) a` — `setUnion_absorb`'s per-element fact.
/// A single split on `a`: at `a = true`, `union`'s own `true` branch
/// short-circuits to `true_` without even looking at `inter true b`; at
/// `a = false`, `union`'s `false` branch defers to `inter false b`, which
/// itself ι-reduces to the fixed constant `false_` regardless of `b`. Both
/// branches land on the literal equal to `a`'s own value — no lemma at all.
fn union_absorb_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let xb = inter_at(d, &p_, x, b);
        let lhs = union_at(d, &p_, x, xb);
        d.bool_eq(lhs, x)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (inter a (union a b)) a` — `setInter_absorb`'s per-element fact,
/// the dual of [`union_absorb_at`]. A single split on `a`: at `a = true`,
/// `inter`'s `true` branch defers to `union true b`, which itself ι-reduces
/// to `true_` regardless of `b`; at `a = false`, `inter`'s own `false` branch
/// is the fixed constant `false_`, never looking at `union false b` at all.
fn inter_absorb_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let xb = union_at(d, &p_, x, b);
        let lhs = inter_at(d, &p_, x, xb);
        d.bool_eq(lhs, x)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (compl (union a b)) (inter (compl a) (compl b))` — De Morgan,
/// `setCompl_union`'s per-element fact. A single split on `a`: at `a = true`,
/// both sides ι-reduce to `false_`; at `a = false`, both ι-reduce to the
/// identical term `compl b`.
fn compl_union_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let xy = union_at(d, &p_, x, b);
        let lhs = compl_at(d, &p_, xy);
        let cx = compl_at(d, &p_, x);
        let cb = compl_at(d, &p_, b);
        let rhs = inter_at(d, &p_, cx, cb);
        d.bool_eq(lhs, rhs)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let cb = compl_at(d, &p_, b);
        d.bool_refl(cb)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (compl (inter a b)) (union (compl a) (compl b))` — De Morgan,
/// `setCompl_inter`'s per-element fact, the dual of [`compl_union_at`]. A
/// single split on `a`: at `a = true`, both sides ι-reduce to the identical
/// term `compl b`; at `a = false`, both ι-reduce to `true_`.
fn compl_inter_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let xy = inter_at(d, &p_, x, b);
        let lhs = compl_at(d, &p_, xy);
        let cx = compl_at(d, &p_, x);
        let cb = compl_at(d, &p_, b);
        let rhs = union_at(d, &p_, cx, cb);
        d.bool_eq(lhs, rhs)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let cb = compl_at(d, &p_, b);
        d.bool_refl(cb)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

/// `Eq Bool (compl (compl a)) a` — `setCompl_involutive`'s per-element fact.
/// A single split on `a`, both branches literal.
fn compl_involutive_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p_ = *p;
    let goal = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let cx = compl_at(d, &p_, x);
        let ccx = compl_at(d, &p_, cx);
        d.bool_eq(ccx, x)
    };
    let case_true = |d: &mut NatDev<'_>| -> ExprId {
        let true_ = d.bool_true();
        d.bool_refl(true_)
    };
    let case_false = |d: &mut NatDev<'_>| -> ExprId {
        let false_ = d.bool_false();
        d.bool_refl(false_)
    };
    bool_split1(d, &p_, a, &goal, &case_true, &case_false)
}

// --- the theorems ------------------------------------------------------

/// `Nat.setUnion_comm : ∀ p q k, Eq Bool (setUnion p q k) (setUnion q p k)`.
pub(super) fn declare_set_union_comm(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let union_fg = d.const_app(p.set_union, &[f, g]);
    let union_gf = d.const_app(p.set_union, &[g, f]);
    let lhs = d.apply(union_fg, &[k]);
    let rhs = d.apply(union_gf, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let proof = union_comm_at(d, &p, fk, gk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_union_comm, ty, value)
}

/// `Nat.setInter_comm : ∀ p q k, Eq Bool (setInter p q k) (setInter q p k)`.
pub(super) fn declare_set_inter_comm(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inter_fg = d.const_app(p.set_inter, &[f, g]);
    let inter_gf = d.const_app(p.set_inter, &[g, f]);
    let lhs = d.apply(inter_fg, &[k]);
    let rhs = d.apply(inter_gf, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let proof = inter_comm_at(d, &p, fk, gk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_inter_comm, ty, value)
}

/// `Nat.setUnion_assoc : ∀ p q r k,
///   Eq Bool (setUnion (setUnion p q) r k) (setUnion p (setUnion q r) k)`.
pub(super) fn declare_set_union_assoc(
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
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let union_fg = d.const_app(p.set_union, &[f, g]);
    let lhs_fn = d.const_app(p.set_union, &[union_fg, h]);
    let union_gh = d.const_app(p.set_union, &[g, h]);
    let rhs_fn = d.const_app(p.set_union, &[f, union_gh]);
    let lhs = d.apply(lhs_fn, &[k]);
    let rhs = d.apply(rhs_fn, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let hk = d.apply(h, &[k]);
    let proof = union_assoc_at(d, &p, fk, gk, hk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_h = d.pi_fv(h_fv, pred_ty, with_k);
        let with_g = d.pi_fv(g_fv, pred_ty, with_h);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_h = d.lam_fv(h_fv, pred_ty, with_k);
        let with_g = d.lam_fv(g_fv, pred_ty, with_h);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_union_assoc, ty, value)
}

/// `Nat.setInter_assoc : ∀ p q r k,
///   Eq Bool (setInter (setInter p q) r k) (setInter p (setInter q r) k)`.
pub(super) fn declare_set_inter_assoc(
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
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inter_fg = d.const_app(p.set_inter, &[f, g]);
    let lhs_fn = d.const_app(p.set_inter, &[inter_fg, h]);
    let inter_gh = d.const_app(p.set_inter, &[g, h]);
    let rhs_fn = d.const_app(p.set_inter, &[f, inter_gh]);
    let lhs = d.apply(lhs_fn, &[k]);
    let rhs = d.apply(rhs_fn, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let hk = d.apply(h, &[k]);
    let proof = inter_assoc_at(d, &p, fk, gk, hk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_h = d.pi_fv(h_fv, pred_ty, with_k);
        let with_g = d.pi_fv(g_fv, pred_ty, with_h);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_h = d.lam_fv(h_fv, pred_ty, with_k);
        let with_g = d.lam_fv(g_fv, pred_ty, with_h);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_inter_assoc, ty, value)
}

/// `Nat.setUnion_idem : ∀ p k, Eq Bool (setUnion p p k) (p k)`.
pub(super) fn declare_set_union_idem(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let union_ff = d.const_app(p.set_union, &[f, f]);
    let lhs = d.apply(union_ff, &[k]);
    let fk = d.apply(f, &[k]);
    let stmt = d.bool_eq(lhs, fk);

    let proof = union_idem_at(d, &p, fk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_k)
    };
    d.declare_theorem(p.set_union_idem, ty, value)
}

/// `Nat.setInter_idem : ∀ p k, Eq Bool (setInter p p k) (p k)`.
pub(super) fn declare_set_inter_idem(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inter_ff = d.const_app(p.set_inter, &[f, f]);
    let lhs = d.apply(inter_ff, &[k]);
    let fk = d.apply(f, &[k]);
    let stmt = d.bool_eq(lhs, fk);

    let proof = inter_idem_at(d, &p, fk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_k)
    };
    d.declare_theorem(p.set_inter_idem, ty, value)
}

/// `Nat.setInter_union_distrib : ∀ p q r k,
///   Eq Bool (setInter p (setUnion q r) k)
///           (setUnion (setInter p q) (setInter p r) k)`.
pub(super) fn declare_set_inter_union_distrib(
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
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let union_gh = d.const_app(p.set_union, &[g, h]);
    let lhs_fn = d.const_app(p.set_inter, &[f, union_gh]);
    let inter_fg = d.const_app(p.set_inter, &[f, g]);
    let inter_fh = d.const_app(p.set_inter, &[f, h]);
    let rhs_fn = d.const_app(p.set_union, &[inter_fg, inter_fh]);
    let lhs = d.apply(lhs_fn, &[k]);
    let rhs = d.apply(rhs_fn, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let hk = d.apply(h, &[k]);
    let proof = inter_union_distrib_at(d, &p, fk, gk, hk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_h = d.pi_fv(h_fv, pred_ty, with_k);
        let with_g = d.pi_fv(g_fv, pred_ty, with_h);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_h = d.lam_fv(h_fv, pred_ty, with_k);
        let with_g = d.lam_fv(g_fv, pred_ty, with_h);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_inter_union_distrib, ty, value)
}

/// `Nat.setUnion_inter_distrib : ∀ p q r k,
///   Eq Bool (setUnion p (setInter q r) k)
///           (setInter (setUnion p q) (setUnion p r) k)`.
pub(super) fn declare_set_union_inter_distrib(
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
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inter_gh = d.const_app(p.set_inter, &[g, h]);
    let lhs_fn = d.const_app(p.set_union, &[f, inter_gh]);
    let union_fg = d.const_app(p.set_union, &[f, g]);
    let union_fh = d.const_app(p.set_union, &[f, h]);
    let rhs_fn = d.const_app(p.set_inter, &[union_fg, union_fh]);
    let lhs = d.apply(lhs_fn, &[k]);
    let rhs = d.apply(rhs_fn, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let hk = d.apply(h, &[k]);
    let proof = union_inter_distrib_at(d, &p, fk, gk, hk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_h = d.pi_fv(h_fv, pred_ty, with_k);
        let with_g = d.pi_fv(g_fv, pred_ty, with_h);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_h = d.lam_fv(h_fv, pred_ty, with_k);
        let with_g = d.lam_fv(g_fv, pred_ty, with_h);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_union_inter_distrib, ty, value)
}

/// `Nat.setUnion_absorb : ∀ p q k, Eq Bool (setUnion p (setInter p q) k) (p k)`.
pub(super) fn declare_set_union_absorb(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inter_fg = d.const_app(p.set_inter, &[f, g]);
    let lhs_fn = d.const_app(p.set_union, &[f, inter_fg]);
    let lhs = d.apply(lhs_fn, &[k]);
    let fk = d.apply(f, &[k]);
    let stmt = d.bool_eq(lhs, fk);

    let gk = d.apply(g, &[k]);
    let proof = union_absorb_at(d, &p, fk, gk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_union_absorb, ty, value)
}

/// `Nat.setInter_absorb : ∀ p q k, Eq Bool (setInter p (setUnion p q) k) (p k)`.
pub(super) fn declare_set_inter_absorb(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let union_fg = d.const_app(p.set_union, &[f, g]);
    let lhs_fn = d.const_app(p.set_inter, &[f, union_fg]);
    let lhs = d.apply(lhs_fn, &[k]);
    let fk = d.apply(f, &[k]);
    let stmt = d.bool_eq(lhs, fk);

    let gk = d.apply(g, &[k]);
    let proof = inter_absorb_at(d, &p, fk, gk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_inter_absorb, ty, value)
}

/// `Nat.setCompl_union : ∀ p q k,
///   Eq Bool (setCompl (setUnion p q) k) (setInter (setCompl p) (setCompl q) k)`.
pub(super) fn declare_set_compl_union(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let union_fg = d.const_app(p.set_union, &[f, g]);
    let lhs_fn = d.const_app(p.set_compl, &[union_fg]);
    let compl_f = d.const_app(p.set_compl, &[f]);
    let compl_g = d.const_app(p.set_compl, &[g]);
    let rhs_fn = d.const_app(p.set_inter, &[compl_f, compl_g]);
    let lhs = d.apply(lhs_fn, &[k]);
    let rhs = d.apply(rhs_fn, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let proof = compl_union_at(d, &p, fk, gk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_compl_union, ty, value)
}

/// `Nat.setCompl_inter : ∀ p q k,
///   Eq Bool (setCompl (setInter p q) k) (setUnion (setCompl p) (setCompl q) k)`.
pub(super) fn declare_set_compl_inter(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let inter_fg = d.const_app(p.set_inter, &[f, g]);
    let lhs_fn = d.const_app(p.set_compl, &[inter_fg]);
    let compl_f = d.const_app(p.set_compl, &[f]);
    let compl_g = d.const_app(p.set_compl, &[g]);
    let rhs_fn = d.const_app(p.set_union, &[compl_f, compl_g]);
    let lhs = d.apply(lhs_fn, &[k]);
    let rhs = d.apply(rhs_fn, &[k]);
    let stmt = d.bool_eq(lhs, rhs);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let proof = compl_inter_at(d, &p, fk, gk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_compl_inter, ty, value)
}

/// `Nat.setCompl_involutive : ∀ p k, Eq Bool (setCompl (setCompl p) k) (p k)`.
pub(super) fn declare_set_compl_involutive(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let compl_f = d.const_app(p.set_compl, &[f]);
    let lhs_fn = d.const_app(p.set_compl, &[compl_f]);
    let lhs = d.apply(lhs_fn, &[k]);
    let fk = d.apply(f, &[k]);
    let stmt = d.bool_eq(lhs, fk);

    let proof = compl_involutive_at(d, &p, fk);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_k)
    };
    d.declare_theorem(p.set_compl_involutive, ty, value)
}

/// `a b : Bool ⊢ (Eq Bool a true → Eq Bool b true) → (Eq Bool b true →
/// Eq Bool a true) → Eq Bool a b` — the per-element fact `subset_antisymm`
/// needs: two `Bool` values that imply each other's truth are equal. A
/// single `Bool.rec` on `a`, delayed-hypothesis style (the same shape
/// [`le_sel_of_bool_impl`] uses): at `a = true`, the forward implication
/// applied to `Eq.refl true` gives `Eq Bool b true`, symmetrized
/// ([`NatOps::bool_symm`]); at `a = false`, a SECOND, nested `Bool.rec` on
/// `b` closes it — its own `true` branch applies the backward implication
/// (delayed the same way the outer split delays the forward one) to
/// `Eq.refl true`, landing on exactly `Eq Bool false true`; its `false`
/// branch is `Eq.refl false`, the backward implication unused.
fn bool_eq_of_mutual_impl(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    imp1: ExprId,
    imp2: ExprId,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    // The `a = false` branch, built ahead of time: given
    // `Eq Bool b true → Eq Bool false true`, produce `Eq Bool false b`, by a
    // nested split on `b` (delayed hypothesis again: `b`'s own `true` branch
    // needs `Eq Bool b true` to invoke the implication, which only the
    // delayed-hypothesis shape supplies).
    let false_branch = {
        let nested_motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let eq_y_true = d.bool_eq(y, true_);
            let eq_false_true = d.bool_eq(false_, true_);
            let hyp_ty = d.arrow(eq_y_true, eq_false_true);
            let eq_false_y = d.bool_eq(false_, y);
            let body = d.arrow(hyp_ty, eq_false_y);
            d.lam_fv(y_fv, bool_ty, body)
        };
        let nested_case_true = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq_true_true = d.bool_eq(true_, true_);
            let eq_false_true = d.bool_eq(false_, true_);
            let hyp_ty = d.arrow(eq_true_true, eq_false_true);
            let refl_true = d.bool_refl(true_);
            let body = d.apply(h, &[refl_true]);
            d.lam_fv(h_fv, hyp_ty, body)
        };
        let nested_case_false = {
            let h_fv = d.fresh_fvar();
            let eq_false_true = d.bool_eq(false_, true_);
            let hyp_ty = d.arrow(eq_false_true, eq_false_true);
            let body = d.bool_refl(false_);
            d.lam_fv(h_fv, hyp_ty, body)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
        d.apply(
            bool_rec,
            &[nested_motive, nested_case_false, nested_case_true, b],
        )
    };

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let imp1_ty = {
            let eq_x_true = d.bool_eq(x, true_);
            let eq_b_true = d.bool_eq(b, true_);
            d.arrow(eq_x_true, eq_b_true)
        };
        let imp2_ty = {
            let eq_b_true = d.bool_eq(b, true_);
            let eq_x_true = d.bool_eq(x, true_);
            d.arrow(eq_b_true, eq_x_true)
        };
        let concl = d.bool_eq(x, b);
        let inner = d.arrow(imp2_ty, concl);
        let body = d.arrow(imp1_ty, inner);
        d.lam_fv(x_fv, bool_ty, body)
    };

    let case_true = {
        let imp1_fv = d.fresh_fvar();
        let imp1_hyp = d.kernel().fvar(imp1_fv);
        let imp2_fv = d.fresh_fvar();

        let eq_true_true = d.bool_eq(true_, true_);
        let eq_b_true = d.bool_eq(b, true_);
        let imp1_ty = d.arrow(eq_true_true, eq_b_true);
        let imp2_ty = d.arrow(eq_b_true, eq_true_true);

        let refl_true = d.bool_refl(true_);
        let hb = d.apply(imp1_hyp, &[refl_true]); // Eq Bool b true
        let body = d.bool_symm(b, true_, hb); // Eq Bool true b

        let with_imp2 = d.lam_fv(imp2_fv, imp2_ty, body);
        d.lam_fv(imp1_fv, imp1_ty, with_imp2)
    };

    let case_false = {
        let imp1_fv = d.fresh_fvar();
        let imp2_fv = d.fresh_fvar();
        let imp2_hyp = d.kernel().fvar(imp2_fv);

        let eq_false_true = d.bool_eq(false_, true_);
        let eq_b_true = d.bool_eq(b, true_);
        let imp1_ty = d.arrow(eq_false_true, eq_b_true);
        let imp2_ty = d.arrow(eq_b_true, eq_false_true);

        let body = d.apply(false_branch, &[imp2_hyp]); // Eq Bool false b

        let with_imp2 = d.lam_fv(imp2_fv, imp2_ty, body);
        d.lam_fv(imp1_fv, imp1_ty, with_imp2)
    };

    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    let applied = d.apply(bool_rec, &[motive, case_false, case_true, a]);
    let applied1 = d.apply(applied, &[imp1]);
    d.apply(applied1, &[imp2])
}
/// `Nat.subset_refl : ∀ f n, Subset f f n` — reflexivity. No case split:
/// unfolding `Subset f f n` at a point `k` is `k < n → f k = true →
/// f k = true`, and the identity function on the membership hypothesis
/// closes it directly.
pub(super) fn declare_subset_refl(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let stmt = d.const_app(p.subset, &[f, f, n]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();

    let fk = d.apply(f, &[k]);
    let true_ = d.bool_true();
    let hm_ty = d.bool_eq(fk, true_);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let with_hm = d.lam_fv(hm_fv, hm_ty, hm);
    let with_hk = d.lam_fv(hk_fv, hk_ty, with_hm);
    let proof_k = d.lam_fv(k_fv, nat, with_hk);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof_k);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    d.declare_theorem(p.subset_refl, ty, value)
}
/// `Nat.subset_trans : ∀ f g h n, Subset f g n → Subset g h n →
/// Subset f h n` — transitivity: chain the two membership implications at
/// each point.
pub(super) fn declare_subset_trans(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sub_fg_ty = d.const_app(p.subset, &[f, g, n]);
    let sub_fg_fv = d.fresh_fvar();
    let sub_fg = d.kernel().fvar(sub_fg_fv);
    let sub_gh_ty = d.const_app(p.subset, &[g, h, n]);
    let sub_gh_fv = d.fresh_fvar();
    let sub_gh = d.kernel().fvar(sub_gh_fv);

    let stmt = d.const_app(p.subset, &[f, h, n]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);
    let fk = d.apply(f, &[k]);
    let true_ = d.bool_true();
    let hm_ty = d.bool_eq(fk, true_);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let gk_true = d.apply(sub_fg, &[k, hk, hm]); // Eq Bool (g k) true
    let hk_true = d.apply(sub_gh, &[k, hk, gk_true]); // Eq Bool (h k) true

    let with_hm = d.lam_fv(hm_fv, hm_ty, hk_true);
    let with_hk = d.lam_fv(hk_fv, hk_ty, with_hm);
    let proof_k = d.lam_fv(k_fv, nat, with_hk);
    let with_gh = d.lam_fv(sub_gh_fv, sub_gh_ty, proof_k);
    let with_fg = d.lam_fv(sub_fg_fv, sub_fg_ty, with_gh);

    let ty_inner = {
        let inner = d.arrow(sub_gh_ty, stmt);
        d.arrow(sub_fg_ty, inner)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, ty_inner);
        let with_h = d.pi_fv(h_fv, pred_ty, with_n);
        let with_g = d.pi_fv(g_fv, pred_ty, with_h);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, with_fg);
        let with_h = d.lam_fv(h_fv, pred_ty, with_n);
        let with_g = d.lam_fv(g_fv, pred_ty, with_h);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.subset_trans, ty, value)
}
/// `Nat.subset_antisymm : ∀ f g n, Subset f g n → Subset g f n →
/// ∀ k, k < n → Eq Bool (f k) (g k)` — antisymmetry, POINTWISE (this kernel
/// has no `funext`, so function equality is not even statable). Specializes
/// both `Subset` hypotheses to the two directions of implication at `k`, then
/// [`bool_eq_of_mutual_impl`] closes it.
pub(super) fn declare_subset_antisymm(
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

    let sub_fg_ty = d.const_app(p.subset, &[f, g, n]);
    let sub_fg_fv = d.fresh_fvar();
    let sub_fg = d.kernel().fvar(sub_fg_fv);
    let sub_gf_ty = d.const_app(p.subset, &[g, f, n]);
    let sub_gf_fv = d.fresh_fvar();
    let sub_gf = d.kernel().fvar(sub_gf_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let true_ = d.bool_true();

    let imp1 = {
        let mem_fv = d.fresh_fvar();
        let mem = d.kernel().fvar(mem_fv);
        let mem_ty = d.bool_eq(fk, true_);
        let applied = d.apply(sub_fg, &[k, hk, mem]);
        d.lam_fv(mem_fv, mem_ty, applied)
    };
    let imp2 = {
        let mem_fv = d.fresh_fvar();
        let mem = d.kernel().fvar(mem_fv);
        let mem_ty = d.bool_eq(gk, true_);
        let applied = d.apply(sub_gf, &[k, hk, mem]);
        d.lam_fv(mem_fv, mem_ty, applied)
    };

    let eq_proof = bool_eq_of_mutual_impl(d, &p, fk, gk, imp1, imp2);
    let concl = d.bool_eq(fk, gk);

    let with_hk = d.lam_fv(hk_fv, hk_ty, eq_proof);
    let proof_k = d.lam_fv(k_fv, nat, with_hk);
    let with_gf = d.lam_fv(sub_gf_fv, sub_gf_ty, proof_k);
    let with_fg = d.lam_fv(sub_fg_fv, sub_fg_ty, with_gf);

    let stmt_k = {
        let inner = d.arrow(hk_ty, concl);
        d.pi_fv(k_fv, nat, inner)
    };
    let ty_inner = {
        let inner = d.arrow(sub_gf_ty, stmt_k);
        d.arrow(sub_fg_ty, inner)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, ty_inner);
        let with_g = d.pi_fv(g_fv, pred_ty, with_n);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, with_fg);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.subset_antisymm, ty, value)
}
/// `Nat.setDiff_eq_inter_compl : ∀ f g k,
///   Eq Bool (setDiff f g k) (setInter f (setCompl g) k)` — `setDiff` is
/// LITERALLY `setInter` applied to `setCompl`, not merely equal to it: both
/// sides unfold (delta on `Nat.setDiff`/`Nat.setInter`/`Nat.setCompl`, beta,
/// iota) to the identical `bool_select_bool` nesting, so `Eq.refl` on the
/// LHS already has the RHS as its type up to defeq — no case split needed.
pub(super) fn declare_set_diff_eq_inter_compl(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let diff_fg = d.const_app(p.set_diff, &[f, g]);
    let lhs = d.apply(diff_fg, &[k]);

    let compl_g = d.const_app(p.set_compl, &[g]);
    let inter_f_complg = d.const_app(p.set_inter, &[f, compl_g]);
    let rhs = d.apply(inter_f_complg, &[k]);

    let stmt = d.bool_eq(lhs, rhs);
    let proof = d.bool_refl(lhs);

    let ty = {
        let with_k = d.pi_fv(k_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_k);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, pred_ty, with_k);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.set_diff_eq_inter_compl, ty, value)
}
/// `a b : Bool, (Eq Bool a true → Eq Bool b true) ⊢
///   Eq Bool (union_at a b) b` — the per-element fact
/// `union_eq_right_of_subset` needs: if `a` implies `b`, unioning with it
/// changes nothing. A single `Bool.rec` on `a`, delayed-hypothesis style
/// ([`le_sel_of_bool_impl`]'s own pattern): at `a = true`, `union_at`
/// short-circuits to `true_` and the hypothesis (applied to `Eq.refl true`)
/// gives `Eq Bool b true`, symmetrized; at `a = false`, `union_at` reduces to
/// `b` itself and the goal `Eq Bool b b` is `Eq.refl`, the hypothesis unused.
fn union_eq_right_of_impl(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    imp: ExprId,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let eq_x_true = d.bool_eq(x, true_);
        let eq_b_true = d.bool_eq(b, true_);
        let hyp_ty = d.arrow(eq_x_true, eq_b_true);
        let union_x_b = bool_select_bool(d, &p_, x, true_, b);
        let concl = d.bool_eq(union_x_b, b);
        let body = d.arrow(hyp_ty, concl);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let eq_true_true = d.bool_eq(true_, true_);
        let eq_b_true = d.bool_eq(b, true_);
        let hyp_ty = d.arrow(eq_true_true, eq_b_true);
        let refl_true = d.bool_refl(true_);
        let hb = d.apply(hyp, &[refl_true]);
        let body = d.bool_symm(b, true_, hb);
        d.lam_fv(hyp_fv, hyp_ty, body)
    };
    let case_false = {
        let hyp_fv = d.fresh_fvar();
        let false_ = d.bool_false();
        let eq_false_true = d.bool_eq(false_, true_);
        let eq_b_true = d.bool_eq(b, true_);
        let hyp_ty = d.arrow(eq_false_true, eq_b_true);
        let body = d.bool_refl(b);
        d.lam_fv(hyp_fv, hyp_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    let applied = d.apply(bool_rec, &[motive, case_false, case_true, a]);
    d.apply(applied, &[imp])
}
/// `Nat.union_eq_right_of_subset : ∀ f g n, Subset f g n →
///   ∀ k, k < n → Eq Bool (setUnion f g k) (g k)` — the lattice–order
/// bridge: union with a superset is the superset. (The companion direction,
/// `(∀k, setUnion f g k = g k) → Subset f g n`, is not required by the task
/// and is not built here.)
pub(super) fn declare_union_eq_right_of_subset(
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

    let sub_fg_ty = d.const_app(p.subset, &[f, g, n]);
    let sub_fg_fv = d.fresh_fvar();
    let sub_fg = d.kernel().fvar(sub_fg_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let true_ = d.bool_true();

    let imp = {
        let mem_fv = d.fresh_fvar();
        let mem = d.kernel().fvar(mem_fv);
        let mem_ty = d.bool_eq(fk, true_);
        let applied = d.apply(sub_fg, &[k, hk, mem]);
        d.lam_fv(mem_fv, mem_ty, applied)
    };

    let eq_proof = union_eq_right_of_impl(d, &p, fk, gk, imp);

    let union_fg = d.const_app(p.set_union, &[f, g]);
    let lhs = d.apply(union_fg, &[k]);
    let concl = d.bool_eq(lhs, gk);

    let with_hk = d.lam_fv(hk_fv, hk_ty, eq_proof);
    let proof_k = d.lam_fv(k_fv, nat, with_hk);
    let with_fg = d.lam_fv(sub_fg_fv, sub_fg_ty, proof_k);

    let stmt_k = {
        let inner = d.arrow(hk_ty, concl);
        d.pi_fv(k_fv, nat, inner)
    };
    let ty_inner = d.arrow(sub_fg_ty, stmt_k);
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, ty_inner);
        let with_g = d.pi_fv(g_fv, pred_ty, with_n);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, with_fg);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.union_eq_right_of_subset, ty, value)
}
/// `a b : Bool, Eq Bool a true ⊢ Eq Bool (union_at a b) true` — the
/// per-element fact `subset_union_left` needs: membership in `p` implies
/// membership in `setUnion p q`. A single `Bool.rec` on `a`, delayed
/// hypothesis: at `a = true`, `union_at` short-circuits to `true_`,
/// `Eq.refl`; at `a = false`, `union_at` reduces to `b`, and the (impossible)
/// hypothesis `Eq Bool false true` eliminates into the goal via
/// [`NatOps::false_true_elim`].
fn union_left_mem_of_mem(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let eq_x_true = d.bool_eq(x, true_);
        let union_x_b = bool_select_bool(d, &p_, x, true_, b);
        let concl = d.bool_eq(union_x_b, true_);
        let body = d.arrow(eq_x_true, concl);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let hyp_fv = d.fresh_fvar();
        let eq_true_true = d.bool_eq(true_, true_);
        let body = d.bool_refl(true_);
        d.lam_fv(hyp_fv, eq_true_true, body)
    };
    let case_false = {
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let false_ = d.bool_false();
        let eq_false_true = d.bool_eq(false_, true_);
        let target = d.bool_eq(b, true_);
        let body = d.false_true_elim(target, hyp);
        d.lam_fv(hyp_fv, eq_false_true, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    let applied = d.apply(bool_rec, &[motive, case_false, case_true, a]);
    d.apply(applied, &[h])
}
/// `Nat.subset_union_left : ∀ f g n, Subset f (setUnion f g) n`.
pub(super) fn declare_subset_union_left(
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
    let stmt = d.const_app(p.subset, &[f, union_fg, n]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let true_ = d.bool_true();
    let hm_ty = d.bool_eq(fk, true_);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let eq_proof = union_left_mem_of_mem(d, &p, fk, gk, hm);

    let with_hm = d.lam_fv(hm_fv, hm_ty, eq_proof);
    let with_hk = d.lam_fv(hk_fv, hk_ty, with_hm);
    let proof_k = d.lam_fv(k_fv, nat, with_hk);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_n);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof_k);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.subset_union_left, ty, value)
}
/// `a b : Bool, Eq Bool (inter_at a b) true ⊢ Eq Bool a true` — the
/// per-element fact `subset_inter_left` needs: membership in
/// `setInter p q` implies membership in `p`. A single `Bool.rec` on `a`,
/// delayed hypothesis: at `a = true`, the goal `Eq Bool true true` is
/// `Eq.refl`, independent of the hypothesis; at `a = false`, `inter_at`
/// reduces to `false_`, so the delayed hypothesis is ALREADY of the exact
/// needed type `Eq Bool false true → Eq Bool false true` — the identity
/// function.
fn mem_left_of_inter_mem(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inter_x_b = bool_select_bool(d, &p_, x, b, false_);
        let hyp_ty = d.bool_eq(inter_x_b, true_);
        let concl = d.bool_eq(x, true_);
        let body = d.arrow(hyp_ty, concl);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let hyp_fv = d.fresh_fvar();
        let eq_b_true = d.bool_eq(b, true_);
        let body = d.bool_refl(true_);
        d.lam_fv(hyp_fv, eq_b_true, body)
    };
    let case_false = {
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let eq_false_true = d.bool_eq(false_, true_);
        d.lam_fv(hyp_fv, eq_false_true, hyp)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    let applied = d.apply(bool_rec, &[motive, case_false, case_true, a]);
    d.apply(applied, &[h])
}
/// `Nat.subset_inter_left : ∀ f g n, Subset (setInter f g) f n`.
pub(super) fn declare_subset_inter_left(
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

    let inter_fg = d.const_app(p.set_inter, &[f, g]);
    let stmt = d.const_app(p.subset, &[inter_fg, f, n]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();

    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let true_ = d.bool_true();
    let inter_fg_k = d.apply(inter_fg, &[k]);
    let hm_ty = d.bool_eq(inter_fg_k, true_);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let eq_proof = mem_left_of_inter_mem(d, &p, fk, gk, hm);

    let with_hm = d.lam_fv(hm_fv, hm_ty, eq_proof);
    let with_hk = d.lam_fv(hk_fv, hk_ty, with_hm);
    let proof_k = d.lam_fv(k_fv, nat, with_hk);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, pred_ty, with_n);
        d.pi_fv(f_fv, pred_ty, with_g)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof_k);
        let with_g = d.lam_fv(g_fv, pred_ty, with_n);
        d.lam_fv(f_fv, pred_ty, with_g)
    };
    d.declare_theorem(p.subset_inter_left, ty, value)
}

/// Declare `Nat.setUnion`/`setInter`/`setCompl`/`setDiff`/`Subset`, the three
/// `countRange` cardinality laws, and the pointwise Boolean-lattice laws
/// (curriculum node `sets`'s own claim), in dependency order. Must run AFTER
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
    declare_set_union_comm(d, p)?;
    declare_set_inter_comm(d, p)?;
    declare_set_union_assoc(d, p)?;
    declare_set_inter_assoc(d, p)?;
    declare_set_union_idem(d, p)?;
    declare_set_inter_idem(d, p)?;
    declare_set_inter_union_distrib(d, p)?;
    declare_set_union_inter_distrib(d, p)?;
    declare_set_union_absorb(d, p)?;
    declare_set_inter_absorb(d, p)?;
    declare_set_compl_union(d, p)?;
    declare_set_compl_inter(d, p)?;
    declare_set_compl_involutive(d, p)?;
    declare_subset_refl(d, p)?;
    declare_subset_trans(d, p)?;
    declare_subset_antisymm(d, p)?;
    declare_set_diff_eq_inter_compl(d, p)?;
    declare_union_eq_right_of_subset(d, p)?;
    declare_subset_union_left(d, p)?;
    declare_subset_inter_left(d, p)?;
    Ok(())
}
