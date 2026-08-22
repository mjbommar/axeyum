//! `Nat.noConfusionType` / `Nat.noConfusion`: constructor disjointness and
//! injectivity for `Nat`, generated once as reusable declarations (mirroring
//! what Lean's elaborator synthesizes for every inductive) rather than
//! re-derived ad hoc at each call site. `Nat.not_lt_zero` is then proved
//! *from* `Nat.noConfusion`, not from a bespoke discriminator.
//!
//! ## `noConfusionType`
//!
//! `Nat.noConfusionType : Π {u} (P : Sort u) (n1 n2 : Nat), Sort u`, by a
//! case split on `n1` then `n2` (both via `Nat.rec`, ignoring every induction
//! hypothesis — this is `Nat.casesOn` twice, not real recursion):
//!
//! | n1     | n2     | result             |
//! |--------|--------|--------------------|
//! | zero   | zero   | `P → P`            |
//! | zero   | succ _ | `P`                |
//! | succ _ | zero   | `P`                |
//! | succ a | succ b | `(a = b → P) → P`  |
//!
//! Same-constructor cells carry the argument-equality hypothesis curried into
//! `P`; different-constructor cells are just `P` itself, so a hypothetical
//! equation between different constructors, run through `noConfusion` below,
//! produces an arbitrary `P` directly — no separate `False`-elimination step
//! is needed.
//!
//! Each `Nat.rec` here computes a **type** (an element of `Sort u`) rather
//! than a proof, so — mirroring the existing `not_succ_le_zero` discriminator
//! in `order.rs`, which does the same thing at the fixed `P := False`/`True`
//! instance — its motive maps into `Sort (u+1)` (the type *of* `Sort u`), not
//! `Sort u` itself.
//!
//! ## `noConfusion`
//!
//! `Nat.noConfusion : Π {u} (P : Sort u) {n1 n2}, n1 = n2 → noConfusionType P n1 n2`.
//! Built by transporting (`Eq.rec`) the *uniform* inhabitant of
//! `noConfusionType P n1 n1` (`fun p => p` at `zero`, `fun k => k rfl` at
//! `succ _`, itself a `Nat.rec` case split, this time computing a genuine
//! value rather than a type, so its motive maps into `Sort u` directly)
//! along the hypothesis `n1 = n2`.
//!
//! ## Payoff: `Nat.not_lt_zero`
//!
//! `Nat.lt n zero` unfolds to `Nat.le (succ n) zero`; `le_dest` turns that
//! into `∃ k, succ n + k = zero`. Casing on `k` reduces the sum to `succ n`
//! (`k = zero`) or `succ (succ n + j)` (`k = succ j`) — either way a
//! `succ _ = zero` equation, which `noConfusion` (instantiated at
//! `P := False`) discharges directly. No case analysis on the constructors
//! of `Le` itself is needed at all — the whole argument routes through
//! plain `Nat` disjointness.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;

/// `Nat.noConfusionType.{u} P n1 n2 : Sort u`, applied to concrete arguments.
fn no_confusion_type_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    u_level: LevelId,
    pp: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let c = d.kernel().const_(p.no_confusion_type, vec![u_level]);
    d.apply(c, &[pp, a, b])
}

/// `Nat.noConfusionType`, `Nat.noConfusion`, `Nat.succ_ne_zero`, and
/// `Nat.not_lt_zero` — the last built *from* `noConfusion`, not from a
/// bespoke discriminator.
///
/// # Errors
///
/// Returns the trusted kernel gate's rejection — a self-check failure here
/// means the generated `noConfusionType`/`noConfusion` terms do not actually
/// type-check, which would be a bug in this construction, not in the kernel.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_no_confusion(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();

    // A fresh universe parameter, private to this pair of declarations: each
    // declaration owns its own `uparams` list, so a plain `u` cannot collide
    // with any other declaration's parameters.
    let u_name = {
        let base = d.kernel().anon();
        d.kernel().name_str(base, "u")
    };
    let u_level = d.kernel().level_param(u_name);
    let succ_u = d.kernel().level_succ(u_level);
    let sort_u = d.kernel().sort(u_level);

    // ======================================================================
    // Nat.noConfusionType : Sort u -> Nat -> Nat -> Sort u
    // ======================================================================

    let no_confusion_type_ty = {
        let inner = d.arrow(nat, sort_u); // Nat -> Sort u
        let inner = d.arrow(nat, inner); //  Nat -> Nat -> Sort u
        d.arrow(sort_u, inner) //  Sort u -> Nat -> Nat -> Sort u
    };

    let p_fv = d.fresh_fvar();
    let p_var = d.kernel().fvar(p_fv);
    let n1_fv = d.fresh_fvar();
    let n1_var = d.kernel().fvar(n1_fv);
    let n2_fv = d.fresh_fvar();
    let n2_var = d.kernel().fvar(n2_fv);

    // n1 = zero: `fun n2 => Nat.rec{u+1} (motive:=fun _=>Sort u) (P -> P) (fun _ _ => P) n2`.
    let zero_branch = {
        let n2a_fv = d.fresh_fvar();
        let n2a = d.kernel().fvar(n2a_fv);
        let inner_motive = d.kernel().lam(anon, nat, sort_u, BinderInfo::Default);
        let inner_rec = d.kernel().const_(p.rec, vec![succ_u]);
        let same_ctor = d.arrow(p_var, p_var);
        let diff_ctor = {
            let step_ih = d.kernel().lam(anon, sort_u, p_var, BinderInfo::Default);
            d.kernel().lam(anon, nat, step_ih, BinderInfo::Default)
        };
        let applied = d.apply(inner_rec, &[inner_motive, same_ctor, diff_ctor, n2a]);
        d.lam_fv(n2a_fv, nat, applied)
    };

    // n1 = succ n1': `fun n2 => Nat.rec{u+1} (motive:=fun _=>Sort u) P (fun m2 _ => (n1'=m2 -> P) -> P) n2`.
    let outer_succ_minor = {
        let n1p_fv = d.fresh_fvar();
        let n1p = d.kernel().fvar(n1p_fv);

        let n2b_fv = d.fresh_fvar();
        let n2b = d.kernel().fvar(n2b_fv);
        let inner_motive = d.kernel().lam(anon, nat, sort_u, BinderInfo::Default);
        let inner_rec = d.kernel().const_(p.rec, vec![succ_u]);
        let same_ctor = {
            let m2_fv = d.fresh_fvar();
            let m2 = d.kernel().fvar(m2_fv);
            let eqn = d.eq(n1p, m2);
            let curried = d.arrow(eqn, p_var);
            let whole = d.arrow(curried, p_var);
            let step_ih = d.kernel().lam(anon, sort_u, whole, BinderInfo::Default);
            d.lam_fv(m2_fv, nat, step_ih)
        };
        let diff_ctor = p_var;
        let branch = d.apply(inner_rec, &[inner_motive, diff_ctor, same_ctor, n2b]);
        let branch = d.lam_fv(n2b_fv, nat, branch);

        let ih_ty = d.arrow(nat, sort_u);
        let with_ih = d.kernel().lam(anon, ih_ty, branch, BinderInfo::Default);
        d.lam_fv(n1p_fv, nat, with_ih)
    };

    let outer_motive = {
        let codomain = d.arrow(nat, sort_u);
        d.kernel().lam(anon, nat, codomain, BinderInfo::Default)
    };
    let outer_rec = d.kernel().const_(p.rec, vec![succ_u]);
    let discriminator = d.apply(
        outer_rec,
        &[outer_motive, zero_branch, outer_succ_minor, n1_var],
    );
    let no_confusion_type_body = d.apply(discriminator, &[n2_var]);

    let no_confusion_type_value = {
        let inner = d.lam_fv(n2_fv, nat, no_confusion_type_body);
        let inner = d.lam_fv(n1_fv, nat, inner);
        d.lam_fv(p_fv, sort_u, inner)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.no_confusion_type,
        uparams: vec![u_name],
        ty: no_confusion_type_ty,
        value: no_confusion_type_value,
        hint: ReducibilityHint::Regular(1),
    })?;

    // ======================================================================
    // Nat.noConfusion : Π (P:Sort u) (n1 n2:Nat), n1 = n2 -> noConfusionType P n1 n2
    // ======================================================================

    let p2_fv = d.fresh_fvar();
    let p2_var = d.kernel().fvar(p2_fv);
    let n1b_fv = d.fresh_fvar();
    let n1b_var = d.kernel().fvar(n1b_fv);
    let n2c_fv = d.fresh_fvar();
    let n2c_var = d.kernel().fvar(n2c_fv);
    let h_fv = d.fresh_fvar();
    let h_var = d.kernel().fvar(h_fv);

    let eqn = d.eq(n1b_var, n2c_var);

    let no_confusion_ty = {
        let concl = no_confusion_type_at(d, &p, u_level, p2_var, n1b_var, n2c_var);
        let arrow_h = d.arrow(eqn, concl);
        let inner = d.pi_fv(n2c_fv, nat, arrow_h);
        let inner = d.pi_fv(n1b_fv, nat, inner);
        d.pi_fv(p2_fv, sort_u, inner)
    };

    // The uniform inhabitant of `noConfusionType P n1 n1`, by cases on n1
    // (this rec computes a VALUE, so its motive maps into `Sort u` directly,
    // not `Sort (u+1)` as in `noConfusionType`'s own internal case splits).
    let uniform = {
        let uniform_motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = no_confusion_type_at(d, &p, u_level, p2_var, y, y);
            d.lam_fv(y_fv, nat, body)
        };
        let uniform_zero = {
            // : P -> P
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            d.lam_fv(x_fv, p2_var, x)
        };
        let uniform_succ = {
            // Π (k:Nat) (_ih : noConfusionType P k k), (k=k -> P) -> P
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let ih_ty = no_confusion_type_at(d, &p, u_level, p2_var, k, k);
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let refl_k = d.refl(k);
            let f_applied = d.apply(f, &[refl_k]);
            let f_ty = {
                let eqn_kk = d.eq(k, k);
                d.arrow(eqn_kk, p2_var)
            };
            let with_f = d.lam_fv(f_fv, f_ty, f_applied);
            let with_ih = d.kernel().lam(anon, ih_ty, with_f, BinderInfo::Default);
            d.lam_fv(k_fv, nat, with_ih)
        };
        let rec = d.kernel().const_(p.rec, vec![u_level]);
        d.apply(rec, &[uniform_motive, uniform_zero, uniform_succ, n1b_var])
    };

    let eq_rec_motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = no_confusion_type_at(d, &p, u_level, p2_var, n1b_var, x);
        let hyp = d.eq(n1b_var, x);
        let inner = d.kernel().lam(anon, hyp, body, BinderInfo::Default);
        d.lam_fv(x_fv, nat, inner)
    };
    let one = d.level_one();
    let eq_rec = d.kernel().const_(p.logic.eq_rec, vec![u_level, one]);
    let no_confusion_body = d.apply(
        eq_rec,
        &[nat, n1b_var, eq_rec_motive, uniform, n2c_var, h_var],
    );

    let no_confusion_value = {
        let inner = d.lam_fv(h_fv, eqn, no_confusion_body);
        let inner = d.lam_fv(n2c_fv, nat, inner);
        let inner = d.lam_fv(n1b_fv, nat, inner);
        d.lam_fv(p2_fv, sort_u, inner)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.no_confusion,
        uparams: vec![u_name],
        ty: no_confusion_ty,
        value: no_confusion_value,
        hint: ReducibilityHint::Regular(2),
    })?;

    // ======================================================================
    // Nat.succ_ne_zero : forall n, Not (Eq Nat (succ n) zero)
    // ======================================================================

    d.theorem(p.succ_ne_zero, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let zero = d.zero();
        let eqn = d.eq(sn, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let level_zero = d.kernel().level_zero();
        let nc = d.kernel().const_(p.no_confusion, vec![level_zero]);
        let applied = d.apply(nc, &[false_ty, sn, zero, h]);
        let stmt = d.arrow(eqn, false_ty);
        let proof = d.lam_fv(h_fv, eqn, applied);
        (stmt, proof)
    })?;

    // ======================================================================
    // Nat.not_lt_zero : forall n, Not (Lt n zero)
    //
    // Unlike `not_succ_le_zero` (order.rs), which discriminates directly on
    // the constructors of `Le`, this routes through `le_dest` to an ordinary
    // Nat equation and discharges it with `noConfusion`.
    // ======================================================================

    d.theorem(p.not_lt_zero, 1, &|d, v| {
        let n = v[0];
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let zero = d.zero();
        let sn = d.succ(n);
        let lt_ty = d.lt(n, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let one = d.level_one();

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `motive_k`/`base`/`step` build, for each shape of `k`, a proof of
        // `(succ n + k = zero) -> False` via `Nat.noConfusion`.
        let motive_k = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let lhs = d.add(sn, k);
            let zero = d.zero();
            let eqn = d.eq(lhs, zero);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            d.arrow(eqn, false_ty)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let lhs = d.add(sn, zero);
            let hk_ty = d.eq(lhs, zero);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level_zero = d.kernel().level_zero();
            let nc = d.kernel().const_(p.no_confusion, vec![level_zero]);
            // `sn` is already `succ _`-shaped; `hk`'s declared type
            // `add sn zero = zero` is definitionally `sn = zero`.
            let applied = d.apply(nc, &[false_ty, sn, zero, hk]);
            d.lam_fv(hk_fv, hk_ty, applied)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
            let zero = d.zero();
            let sj = d.succ(j);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let lhs = d.add(sn, sj);
            let hk_ty = d.eq(lhs, zero);
            let inner = d.add(sn, j);
            let inner_succ = d.succ(inner);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level_zero = d.kernel().level_zero();
            let nc = d.kernel().const_(p.no_confusion, vec![level_zero]);
            // `hk`'s declared type `add sn (succ j) = zero` is
            // definitionally `succ (add sn j) = zero`.
            let applied = d.apply(nc, &[false_ty, inner_succ, zero, hk]);
            d.lam_fv(hk_fv, hk_ty, applied)
        };

        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let case_split = d.induct(&motive_k, &base, &step, k);
        let minor = d.lam_fv(k_fv, nat, case_split);

        let predicate = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let lhs = d.add(sn, k2);
            let body = d.eq(lhs, zero);
            d.lam_fv(k2_fv, nat, body)
        };
        let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
        let exists_ty = d.apply(exists_c, &[nat, predicate]);
        let motive = d
            .kernel()
            .lam(anon, exists_ty, false_ty, BinderInfo::Default);

        let source_proof = d.lemma(p.le_dest, &[sn, zero, h]);

        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let result = d.apply(rec, &[nat, predicate, motive, minor, source_proof]);

        let stmt = d.arrow(lt_ty, false_ty);
        let proof = d.lam_fv(h_fv, lt_ty, result);
        (stmt, proof)
    })?;

    Ok(())
}
