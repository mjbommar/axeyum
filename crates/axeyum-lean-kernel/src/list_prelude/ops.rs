//! Term-building helpers shared by `list_prelude`'s operations and theorems:
//! the raw `Pi`/`Lam`/`fvar` plumbing (mirroring `prelude.rs`'s own
//! `apply_all`/`lam_fvar`/`pi_fvar`), and a carrier-generic `Eq` layer
//! (mirroring `examples/g4_pilot_generic_congr_probe.rs`'s
//! `eq_of`/`refl_of`/`transport_generic`/`generic_congr_arg`, ADR-1495's G4
//! pilot 2) so a proof step can be written once and reused at `Nat`,
//! `List α`, or any other `Type 0` carrier without a per-carrier `NatOps`/
//! `IntDev`-style hardcoded dev layer — exactly the reuse this crate's own
//! `kernel-proof-engineering.md` warns a hardcoded carrier defeats.

use super::ListNames;
use crate::LogicPrelude;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError};

// --- raw term plumbing -------------------------------------------------

pub(crate) fn apply_all(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

pub(crate) fn lam_fvar(
    kernel: &mut Kernel,
    fvar: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.lam(anon, ty, body, info)
}

pub(crate) fn pi_fvar(
    kernel: &mut Kernel,
    fvar: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.pi(anon, ty, body, info)
}

pub(crate) fn arrow(kernel: &mut Kernel, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, dom, cod, BinderInfo::Default)
}

/// `List.{0} alpha`, i.e. `List α` at the fixed instantiation `u := 0` this
/// whole module works at.
pub(crate) fn list_of(
    kernel: &mut Kernel,
    list: NameId,
    zero_lvl: LevelId,
    alpha: ExprId,
) -> ExprId {
    let c = kernel.const_(list, vec![zero_lvl]);
    kernel.app(c, alpha)
}

// --- carrier-generic `Eq` layer (ADR-1495 G4 pilot 2, generalized) -----

pub(crate) fn eq_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> ExprId {
    let e = kernel.const_(logic.eq, vec![level]);
    apply_all(kernel, e, &[ty, lhs, rhs])
}

pub(crate) fn refl_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
) -> ExprId {
    let e = kernel.const_(logic.eq_refl, vec![level]);
    apply_all(kernel, e, &[ty, a])
}

/// `fun (x : ty) (_ : Eq ty a x) => body(x)`.
fn eq_motive_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
    x_fv: u64,
    body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let x = kernel.fvar(x_fv);
    let concl = body(kernel, x);
    let hyp = eq_of(kernel, logic, level, ty, a, x);
    let anon = kernel.anon();
    let inner = kernel.lam(anon, hyp, concl, BinderInfo::Default);
    lam_fvar(kernel, x_fv, ty, inner, BinderInfo::Default)
}

/// `Eq.rec.{0,level} ty p motive refl_case q h : motive q h`.
#[allow(clippy::too_many_arguments)]
fn transport_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = kernel.level_zero();
    let rec = kernel.const_(logic.eq_rec, vec![zero, level]);
    apply_all(kernel, rec, &[ty, p, motive, refl_case, q, h])
}

/// `h : Eq ty a b  ⊢  Eq ty b a`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn symm_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    x_fv: u64,
) -> ExprId {
    let motive = eq_motive_of(kernel, logic, level, ty, a, x_fv, &|k, x| {
        eq_of(k, logic, level, ty, x, a)
    });
    let refl_case = refl_of(kernel, logic, level, ty, a);
    transport_of(kernel, logic, level, ty, a, motive, refl_case, b, h)
}

/// `h1 : Eq ty a b`, `h2 : Eq ty b c  ⊢  Eq ty a c`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn trans_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
    x_fv: u64,
) -> ExprId {
    let motive = eq_motive_of(kernel, logic, level, ty, b, x_fv, &|k, x| {
        eq_of(k, logic, level, ty, a, x)
    });
    transport_of(kernel, logic, level, ty, b, motive, h1, c, h2)
}

/// Congruence in an arbitrary one-hole context: `h : Eq ty_a a b` gives
/// `Eq ty_b (f a) (f b)`. `ty_a`/`level_a` type the arguments; `ty_b`/
/// `level_b` type the result (the two coincide for most calls here, but
/// `length : List α → Nat` needs them to differ).
#[allow(clippy::too_many_arguments)]
pub(crate) fn congr_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    level_a: LevelId,
    ty_a: ExprId,
    level_b: LevelId,
    ty_b: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    x_fv: u64,
    f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(kernel, a);
    let motive = eq_motive_of(kernel, logic, level_a, ty_a, a, x_fv, &|k, x| {
        let fx = f(k, x);
        eq_of(k, logic, level_b, ty_b, fa, fx)
    });
    let refl_case = refl_of(kernel, logic, level_b, ty_b, fa);
    transport_of(kernel, logic, level_a, ty_a, a, motive, refl_case, b, h)
}

// --- a `Bool` case split (needed by `bridge::declare_count_to_multiset`) --

/// `Or (Eq Bool b true) (Eq Bool b false)` for an arbitrary `b : Bool`, by a
/// direct `Bool.rec` split — fully constructive, no excluded middle. Mirrors
/// `nat_prelude::ops::bool_true_or_false`, rebuilt here because that helper
/// is `pub(super)` to `nat_prelude` and not reachable from `list_prelude`.
pub(crate) fn bool_true_or_false_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    one_lvl: LevelId,
    b: ExprId,
    x_fv: u64,
) -> ExprId {
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let true_ = kernel.const_(logic.bool_true, vec![]);
    let false_ = kernel.const_(logic.bool_false, vec![]);

    let motive = {
        let x = kernel.fvar(x_fv);
        let is_true = eq_of(kernel, logic, one_lvl, bool_ty, x, true_);
        let is_false = eq_of(kernel, logic, one_lvl, bool_ty, x, false_);
        let or_c = kernel.const_(logic.or, vec![]);
        let body = apply_all(kernel, or_c, &[is_true, is_false]);
        lam_fvar(kernel, x_fv, bool_ty, body, BinderInfo::Default)
    };
    // `false`-constructor case: motive false = Or (Eq false true) (Eq false false)
    // — the SECOND disjunct holds by `Eq.refl`, so this is `Or.inr`.
    let case_false = {
        let is_true = eq_of(kernel, logic, one_lvl, bool_ty, false_, true_);
        let is_false = eq_of(kernel, logic, one_lvl, bool_ty, false_, false_);
        let refl_false = refl_of(kernel, logic, one_lvl, bool_ty, false_);
        let or_inr = kernel.const_(logic.or_inr, vec![]);
        apply_all(kernel, or_inr, &[is_true, is_false, refl_false])
    };
    // `true`-constructor case: motive true = Or (Eq true true) (Eq true false)
    // — the FIRST disjunct holds by `Eq.refl`, so this is `Or.inl`.
    let case_true = {
        let is_true = eq_of(kernel, logic, one_lvl, bool_ty, true_, true_);
        let is_false = eq_of(kernel, logic, one_lvl, bool_ty, true_, false_);
        let refl_true = refl_of(kernel, logic, one_lvl, bool_ty, true_);
        let or_inl = kernel.const_(logic.or_inl, vec![]);
        apply_all(kernel, or_inl, &[is_true, is_false, refl_true])
    };
    let zero = kernel.level_zero();
    let bool_rec = kernel.const_(logic.bool_rec, vec![zero]);
    apply_all(kernel, bool_rec, &[motive, case_false, case_true, b])
}

/// `Or.rec` into a NON-DEPENDENT `goal`: from `proof : Or left_ty right_ty`
/// and two case functions already built as `left_ty → goal` /
/// `right_ty → goal` lambdas (via [`lam_fvar`]), a proof of `goal`. Mirrors
/// `nat_prelude::steps::or_cases`, rebuilt here for the same visibility
/// reason as [`bool_true_or_false_of`].
#[allow(clippy::too_many_arguments)]
pub(crate) fn or_cases_of(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    let or_ty = {
        let or_c = kernel.const_(logic.or, vec![]);
        apply_all(kernel, or_c, &[left_ty, right_ty])
    };
    let motive = kernel.lam(anon, or_ty, goal, BinderInfo::Default);
    let rec = kernel.const_(logic.or_rec, vec![]);
    apply_all(
        kernel,
        rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, proof],
    )
}

// --- the operations ------------------------------------------------------

/// `List.length : {α : Type 0} → List α → Nat`, by `List.rec` with the
/// constant motive `Nat` — `nil ↦ 0`, `cons head tail ↦ succ ih`.
pub(super) fn declare_length(
    kernel: &mut Kernel,
    list: NameId,
    rec: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
    logic: &LogicPrelude,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(list, "length");
    let alpha_fv = 90_000;
    let l_fv = 90_001;
    let head_fv = 90_002;
    let tail_fv = 90_003;
    let ih_fv = 90_004;

    let alpha = kernel.fvar(alpha_fv);
    let list_alpha = list_of(kernel, list, zero_lvl, alpha);
    let nat_const = kernel.const_(logic.nat, vec![]);

    let anon = kernel.anon();
    let motive = kernel.lam(anon, list_alpha, nat_const, BinderInfo::Default);
    let nil_case = kernel.const_(logic.nat_zero, vec![]);
    let cons_case = {
        let ih = kernel.fvar(ih_fv);
        let succ_const = kernel.const_(logic.nat_succ, vec![]);
        let succ_ih = kernel.app(succ_const, ih);
        let with_ih = lam_fvar(kernel, ih_fv, nat_const, succ_ih, BinderInfo::Default);
        let with_tail = lam_fvar(kernel, tail_fv, list_alpha, with_ih, BinderInfo::Default);
        lam_fvar(kernel, head_fv, alpha, with_tail, BinderInfo::Default)
    };

    let l = kernel.fvar(l_fv);
    let rec_const = kernel.const_(rec, vec![one_lvl, zero_lvl]);
    let body = apply_all(kernel, rec_const, &[alpha, motive, nil_case, cons_case, l]);
    let value = {
        let with_l = lam_fvar(kernel, l_fv, list_alpha, body, BinderInfo::Default);
        lam_fvar(kernel, alpha_fv, type0, with_l, BinderInfo::Implicit)
    };
    let ty = {
        let with_l = pi_fvar(kernel, l_fv, list_alpha, nat_const, BinderInfo::Default);
        pi_fvar(kernel, alpha_fv, type0, with_l, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `List.append : {α : Type 0} → List α → List α → List α`, recursing on the
/// FIRST list argument — `append nil l2 ≡ l2`,
/// `append (cons h t) l2 ≡ cons h (append t l2)`.
#[allow(clippy::too_many_arguments)]
pub(super) fn declare_append(
    kernel: &mut Kernel,
    list: NameId,
    nil: NameId,
    cons: NameId,
    rec: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(list, "append");
    let alpha_fv = 90_100;
    let l1_fv = 90_101;
    let l2_fv = 90_102;
    let head_fv = 90_103;
    let tail_fv = 90_104;
    let ih_fv = 90_105;

    let alpha = kernel.fvar(alpha_fv);
    let list_alpha = list_of(kernel, list, zero_lvl, alpha);

    let anon = kernel.anon();
    let motive = kernel.lam(anon, list_alpha, list_alpha, BinderInfo::Default);
    let nil_case = kernel.fvar(l2_fv);
    let cons_case = {
        let cons_const = kernel.const_(cons, vec![zero_lvl]);
        let ih = kernel.fvar(ih_fv);
        let head = kernel.fvar(head_fv);
        let cons_head_ih = apply_all(kernel, cons_const, &[alpha, head, ih]);
        let with_ih = lam_fvar(kernel, ih_fv, list_alpha, cons_head_ih, BinderInfo::Default);
        let with_tail = lam_fvar(kernel, tail_fv, list_alpha, with_ih, BinderInfo::Default);
        lam_fvar(kernel, head_fv, alpha, with_tail, BinderInfo::Default)
    };

    let l1 = kernel.fvar(l1_fv);
    let rec_const = kernel.const_(rec, vec![one_lvl, zero_lvl]);
    let body = apply_all(kernel, rec_const, &[alpha, motive, nil_case, cons_case, l1]);
    let value = {
        let with_l2 = lam_fvar(kernel, l2_fv, list_alpha, body, BinderInfo::Default);
        let with_l1 = lam_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
        lam_fvar(kernel, alpha_fv, type0, with_l1, BinderInfo::Implicit)
    };
    let ty = {
        let with_l2 = pi_fvar(kernel, l2_fv, list_alpha, list_alpha, BinderInfo::Default);
        let with_l1 = pi_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
        pi_fvar(kernel, alpha_fv, type0, with_l1, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    let _ = nil;
    Ok(name)
}

/// `List.map : {α β : Type 0} → (α → β) → List α → List β`.
#[allow(clippy::too_many_arguments)]
pub(super) fn declare_map(
    kernel: &mut Kernel,
    list: NameId,
    nil: NameId,
    cons: NameId,
    rec: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(list, "map");
    let alpha_fv = 90_200;
    let beta_fv = 90_201;
    let f_fv = 90_202;
    let l_fv = 90_203;
    let head_fv = 90_204;
    let tail_fv = 90_205;
    let ih_fv = 90_206;

    let alpha = kernel.fvar(alpha_fv);
    let beta = kernel.fvar(beta_fv);
    let list_alpha = list_of(kernel, list, zero_lvl, alpha);
    let list_beta = list_of(kernel, list, zero_lvl, beta);
    let f_ty = arrow(kernel, alpha, beta);

    let anon = kernel.anon();
    let motive = kernel.lam(anon, list_alpha, list_beta, BinderInfo::Default);
    let nil_case = {
        let nil_const = kernel.const_(nil, vec![zero_lvl]);
        kernel.app(nil_const, beta)
    };
    let cons_case = {
        let cons_const = kernel.const_(cons, vec![zero_lvl]);
        let f = kernel.fvar(f_fv);
        let head = kernel.fvar(head_fv);
        let f_head = kernel.app(f, head);
        let ih = kernel.fvar(ih_fv);
        let cons_fhead_ih = apply_all(kernel, cons_const, &[beta, f_head, ih]);
        let with_ih = lam_fvar(kernel, ih_fv, list_beta, cons_fhead_ih, BinderInfo::Default);
        let with_tail = lam_fvar(kernel, tail_fv, list_alpha, with_ih, BinderInfo::Default);
        lam_fvar(kernel, head_fv, alpha, with_tail, BinderInfo::Default)
    };

    let l = kernel.fvar(l_fv);
    let rec_const = kernel.const_(rec, vec![one_lvl, zero_lvl]);
    let body = apply_all(kernel, rec_const, &[alpha, motive, nil_case, cons_case, l]);
    let value = {
        let with_l = lam_fvar(kernel, l_fv, list_alpha, body, BinderInfo::Default);
        let with_f = lam_fvar(kernel, f_fv, f_ty, with_l, BinderInfo::Default);
        let with_beta = lam_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
        lam_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
    };
    let ty = {
        let with_l = pi_fvar(kernel, l_fv, list_alpha, list_beta, BinderInfo::Default);
        let with_f = pi_fvar(kernel, f_fv, f_ty, with_l, BinderInfo::Default);
        let with_beta = pi_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
        pi_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `List.foldr : {α β : Type 0} → (α → β → β) → β → List α → β`.
pub(super) fn declare_foldr(
    kernel: &mut Kernel,
    list: NameId,
    rec: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(list, "foldr");
    let alpha_fv = 90_300;
    let beta_fv = 90_301;
    let f_fv = 90_302;
    let z_fv = 90_303;
    let l_fv = 90_304;
    let head_fv = 90_305;
    let tail_fv = 90_306;
    let ih_fv = 90_307;

    let alpha = kernel.fvar(alpha_fv);
    let beta = kernel.fvar(beta_fv);
    let list_alpha = list_of(kernel, list, zero_lvl, alpha);
    let f_ty = {
        let inner = arrow(kernel, beta, beta);
        arrow(kernel, alpha, inner)
    };

    let anon = kernel.anon();
    let motive = kernel.lam(anon, list_alpha, beta, BinderInfo::Default);
    let nil_case = kernel.fvar(z_fv);
    let cons_case = {
        let f = kernel.fvar(f_fv);
        let head = kernel.fvar(head_fv);
        let ih = kernel.fvar(ih_fv);
        let f_head = kernel.app(f, head);
        let f_head_ih = kernel.app(f_head, ih);
        let with_ih = lam_fvar(kernel, ih_fv, beta, f_head_ih, BinderInfo::Default);
        let with_tail = lam_fvar(kernel, tail_fv, list_alpha, with_ih, BinderInfo::Default);
        lam_fvar(kernel, head_fv, alpha, with_tail, BinderInfo::Default)
    };

    let l = kernel.fvar(l_fv);
    let rec_const = kernel.const_(rec, vec![one_lvl, zero_lvl]);
    let body = apply_all(kernel, rec_const, &[alpha, motive, nil_case, cons_case, l]);
    let value = {
        let with_l = lam_fvar(kernel, l_fv, list_alpha, body, BinderInfo::Default);
        let with_z = lam_fvar(kernel, z_fv, beta, with_l, BinderInfo::Default);
        let with_f = lam_fvar(kernel, f_fv, f_ty, with_z, BinderInfo::Default);
        let with_beta = lam_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
        lam_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
    };
    let ty = {
        let with_l = pi_fvar(kernel, l_fv, list_alpha, beta, BinderInfo::Default);
        let with_z = pi_fvar(kernel, z_fv, beta, with_l, BinderInfo::Default);
        let with_f = pi_fvar(kernel, f_fv, f_ty, with_z, BinderInfo::Default);
        let with_beta = pi_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
        pi_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `List.reverse : {α : Type 0} → List α → List α`, via `append` —
/// `reverse nil ≡ nil`, `reverse (cons h t) ≡ append (reverse t) (cons h nil)`.
#[allow(clippy::too_many_arguments)]
pub(super) fn declare_reverse(
    kernel: &mut Kernel,
    list: NameId,
    nil: NameId,
    cons: NameId,
    rec: NameId,
    append: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(list, "reverse");
    let alpha_fv = 90_400;
    let l_fv = 90_401;
    let head_fv = 90_402;
    let tail_fv = 90_403;
    let ih_fv = 90_404;

    let alpha = kernel.fvar(alpha_fv);
    let list_alpha = list_of(kernel, list, zero_lvl, alpha);

    let anon = kernel.anon();
    let motive = kernel.lam(anon, list_alpha, list_alpha, BinderInfo::Default);
    let nil_case = {
        let nil_const = kernel.const_(nil, vec![zero_lvl]);
        kernel.app(nil_const, alpha)
    };
    let cons_case = {
        let append_const = kernel.const_(append, vec![]);
        let cons_const = kernel.const_(cons, vec![zero_lvl]);
        let nil_const = kernel.const_(nil, vec![zero_lvl]);
        let head = kernel.fvar(head_fv);
        let ih = kernel.fvar(ih_fv);
        let singleton_nil = kernel.app(nil_const, alpha);
        let singleton = apply_all(kernel, cons_const, &[alpha, head, singleton_nil]);
        let appended = apply_all(kernel, append_const, &[alpha, ih, singleton]);
        let with_ih = lam_fvar(kernel, ih_fv, list_alpha, appended, BinderInfo::Default);
        let with_tail = lam_fvar(kernel, tail_fv, list_alpha, with_ih, BinderInfo::Default);
        lam_fvar(kernel, head_fv, alpha, with_tail, BinderInfo::Default)
    };

    let l = kernel.fvar(l_fv);
    let rec_const = kernel.const_(rec, vec![one_lvl, zero_lvl]);
    let body = apply_all(kernel, rec_const, &[alpha, motive, nil_case, cons_case, l]);
    let value = {
        let with_l = lam_fvar(kernel, l_fv, list_alpha, body, BinderInfo::Default);
        lam_fvar(kernel, alpha_fv, type0, with_l, BinderInfo::Implicit)
    };
    let ty = {
        let with_l = pi_fvar(kernel, l_fv, list_alpha, list_alpha, BinderInfo::Default);
        pi_fvar(kernel, alpha_fv, type0, with_l, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;
    Ok(name)
}

// --- induction (Prop-valued motive) ---------------------------------------

/// `List.rec.{0,0} alpha (fun x => p x) base (fun head tail ih => step head tail ih) target`:
/// induction on `target : List alpha` for a `Prop`-valued motive `p`. Shared
/// by `theorems::declare_list_theorems` and `bridge::build_list_nat_bridge`.
#[allow(clippy::too_many_arguments)]
pub(super) fn list_induct_prop(
    kernel: &mut Kernel,
    names: &ListNames,
    alpha: ExprId,
    zero_lvl: LevelId,
    p: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    base: &dyn Fn(&mut Kernel) -> ExprId,
    step: &dyn Fn(&mut Kernel, ExprId, ExprId, ExprId) -> ExprId,
    target: ExprId,
    x_fv: u64,
    head_fv: u64,
    tail_fv: u64,
    ih_fv: u64,
) -> ExprId {
    let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
    let motive = {
        let x = kernel.fvar(x_fv);
        let body = p(kernel, x);
        lam_fvar(kernel, x_fv, list_alpha, body, BinderInfo::Default)
    };
    let base_term = base(kernel);
    let step_term = {
        let head = kernel.fvar(head_fv);
        let tail = kernel.fvar(tail_fv);
        let ih_ty = p(kernel, tail);
        let ih = kernel.fvar(ih_fv);
        let body = step(kernel, head, tail, ih);
        let with_ih = lam_fvar(kernel, ih_fv, ih_ty, body, BinderInfo::Default);
        let with_tail = lam_fvar(kernel, tail_fv, list_alpha, with_ih, BinderInfo::Default);
        lam_fvar(kernel, head_fv, alpha, with_tail, BinderInfo::Default)
    };
    let zero = kernel.level_zero();
    let rec_const = kernel.const_(names.rec, vec![zero, zero_lvl]);
    apply_all(
        kernel,
        rec_const,
        &[alpha, motive, base_term, step_term, target],
    )
}
