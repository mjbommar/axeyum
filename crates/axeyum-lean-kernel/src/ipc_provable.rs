//! **Slice 2 of the decomposition recorded in `ipc_heyting.rs`'s module
//! docs** (and in `docs/plan/status/273-logic-excluded-middle.md`): an
//! inductive `Provable : FormulaList -> Formula -> Prop` relation encoding
//! intuitionistic propositional natural deduction, over `ipc_heyting.rs`'s
//! `Formula` AST.
//!
//! ## Why a context type first
//!
//! Natural deduction's `assumption`, `→I` (implication introduction, which
//! *discharges* an assumption) and `∨E` (which opens a fresh assumption in
//! each branch) all need a **context** of currently-available hypotheses —
//! there is no way to state them with `Provable : Formula -> Prop` alone.
//! The kernel has no `List` type (the complete inductive list remains
//! `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable` + `Nat.le` +
//! `Nat.Fin` + `Char` + `Nat.Pair`, per the prior lane's grep), so
//! [`FormulaList`] is built here the same way `Str` and `Formula` itself
//! were: [`crate::Kernel::add_recursive_datatype_family`], with `Formula`
//! itself as the (non-recursive) carrier sort for `cons`'s `head` field:
//!
//! ```text
//! FormulaList.nil  : FormulaList
//! FormulaList.cons : Formula -> FormulaList -> FormulaList
//! ```
//!
//! ## `Provable`: an indexed `Prop`-valued inductive, not a datatype family
//!
//! `Provable : FormulaList -> Formula -> Prop` is genuinely **indexed**
//! (both arguments vary per constructor, e.g. `weaken` changes the context
//! and `and_elim1` changes the goal), so it is built directly through the
//! general [`crate::Kernel::add_inductive`] — the same trusted gate that
//! admits `Nat.le` (`nat_prelude/order.rs`, `Nat -> Nat -> Prop` with a
//! recursive-hypothesis constructor `le_step`) and `Acc`
//! (`prelude.rs`, a fully indexed accessibility relation with a
//! higher-order recursive field). `Nat.le`'s shape is the closest working
//! precedent in this kernel for "a field that is directly a recursive
//! application of the family being defined, at a *different* index than the
//! conclusion" — exactly what every hypothesis of `Provable`'s eleven
//! constructors is.
//!
//! `num_params` is `0`: unlike `Nat.le`'s `n` or `Acc`'s `(α, r)`, no
//! argument of `Provable` is held literally fixed across every constructor
//! (`weaken`, `or_elim` and `imp_intro` all change the context between a
//! hypothesis and the conclusion), so both `FormulaList` and `Formula`
//! arguments are indices.
//!
//! The eleven constructors are the standard intuitionistic natural
//! deduction rules. `assumption` is split into two structural pieces
//! (`ax_head` + `weaken`) rather than a single "membership" side condition,
//! because the kernel has no separate `Mem : FormulaList -> Formula -> Prop`
//! relation either, and `ax_head` + `weaken` together generate exactly the
//! same derivability as "the goal occurs somewhere in the context":
//!
//! - `ax_head  : ∀ ctx phi, Provable (cons phi ctx) phi`
//! - `weaken   : ∀ ctx phi psi, Provable ctx phi -> Provable (cons psi ctx) phi`
//! - `and_intro, and_elim1, and_elim2`
//! - `or_intro1, or_intro2, or_elim`
//! - `imp_intro, imp_elim`
//! - `bot_elim`
//!
//! ## What this slice proves, and what it does not
//!
//! Two closed derivations are landed as kernel `Theorem`s, each a genuine
//! natural-deduction proof term built from the eleven constructors and
//! admitted through the trusted gate:
//!
//! - [`declare_imp_self`]: `Provable nil (imp p p)` — `imp_intro (ax_head)`.
//! - [`declare_and_elim1_example`]: `Provable nil (imp (and_ p q) p)` —
//!   `imp_intro (and_elim1 (ax_head))`.
//!
//! This is genuine evidence the relation is inhabited the way natural
//! deduction predicts, but it is **not** the fact this file exists for.
//! `F:excluded-middle-not-intuitionistic` needs `Not (Provable nil
//! pem_instance)`, which needs:
//!
//! 3. a generic `eval : Formula -> (Nat -> Nat) -> Nat` via `Formula.rec`
//!    (not built here — this file's example proofs never evaluate a
//!    formula, only derive one),
//! 4. soundness (`Provable ctx phi -> (every valuation making ctx true makes
//!    phi true)`) by induction on the derivation (not built here — the real
//!    missing mathematical content), combined with `ipc_heyting.rs`'s
//!    countermodel to conclude `Not (Provable nil pem_instance)`.
//!
//! Neither is attempted here. This file's module tests instead run a
//! **non-kernel, Rust-level** finite decision procedure mirroring the same
//! eleven rules (`tests::finite_search_discriminates_between_derivable_and_pem`)
//! as a non-vacuity check on the *rule set itself* — the "a
//! `Definition`/relation can type-check and still be wrong" gotcha applies to
//! an inductive relation exactly as it does to a computed function, and this
//! is the cheapest evaluation test available before soundness exists to do
//! the job properly.
#![allow(clippy::similar_names)]

use crate::{BinderInfo, Declaration, ExprId, KernelError, NameId, RecField};
use crate::{IpcHeytingPrelude, build_ipc_heyting_prelude};

/// Names produced by [`build_ipc_provable_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IpcProvablePrelude {
    /// `Formula` and the 3-element Heyting-chain semantics this package is
    /// built over.
    pub heyting: IpcHeytingPrelude,
    /// `FormulaList : Type`.
    pub formula_list: NameId,
    /// `FormulaList.nil : FormulaList`.
    pub nil: NameId,
    /// `FormulaList.cons : Formula -> FormulaList -> FormulaList`.
    pub cons: NameId,
    /// `FormulaList.rec`.
    pub formula_list_rec: NameId,
    /// `Provable : FormulaList -> Formula -> Prop`.
    pub provable: NameId,
    /// `Provable.ax_head : (ctx : FormulaList) -> (phi : Formula) -> Provable (cons phi ctx) phi`.
    pub ax_head: NameId,
    /// `Provable.weaken : (ctx) -> (phi psi : Formula) -> Provable ctx phi -> Provable (cons psi ctx) phi`.
    pub weaken: NameId,
    /// `Provable.and_intro`.
    pub and_intro: NameId,
    /// `Provable.and_elim1`.
    pub and_elim1: NameId,
    /// `Provable.and_elim2`.
    pub and_elim2: NameId,
    /// `Provable.or_intro1`.
    pub or_intro1: NameId,
    /// `Provable.or_intro2`.
    pub or_intro2: NameId,
    /// `Provable.or_elim`.
    pub or_elim: NameId,
    /// `Provable.imp_intro`.
    pub imp_intro: NameId,
    /// `Provable.imp_elim`.
    pub imp_elim: NameId,
    /// `Provable.bot_elim`.
    pub bot_elim: NameId,
    /// `ipc_provable_imp_self : Provable nil (imp p p)`.
    pub imp_self: NameId,
    /// `ipc_provable_and_elim1_example : Provable nil (imp (and_ p q) p)`.
    pub and_elim1_example: NameId,
}

/// Build `FormulaList`, the `Provable` natural-deduction relation, and the
/// two example derivations, registering every declaration through the
/// trusted [`crate::Kernel::add_inductive`] / [`crate::Kernel::add_declaration`]
/// gates.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_ipc_provable_prelude(
    kernel: &mut crate::Kernel,
) -> Result<IpcProvablePrelude, KernelError> {
    let heyting = build_ipc_heyting_prelude(kernel)?;
    let anon = kernel.anon();
    let zero_lvl = kernel.level_zero();
    let one = kernel.level_succ(zero_lvl);
    let formula_ty = kernel.const_(heyting.formula, vec![]);

    // --- FormulaList : Type, nil | cons (head : Formula) (tail : FormulaList) ---
    let formula_list = kernel.name_str(anon, "FormulaList");
    let nil = kernel.name_str(formula_list, "nil");
    let cons = kernel.name_str(formula_list, "cons");
    let family = kernel.add_recursive_datatype_family(
        formula_list,
        formula_ty,
        one,
        &[
            (nil, vec![]),
            (cons, vec![RecField::Carrier, RecField::Recursive]),
        ],
    )?;
    let formula_list_rec = family.rec;
    let flist_ty = kernel.const_(formula_list, vec![]);

    // --- Provable : FormulaList -> Formula -> Prop, eleven ND rules ---------
    let provable = kernel.name_str(anon, "Provable");
    let ax_head = kernel.name_str(provable, "ax_head");
    let weaken = kernel.name_str(provable, "weaken");
    let and_intro = kernel.name_str(provable, "and_intro");
    let and_elim1 = kernel.name_str(provable, "and_elim1");
    let and_elim2 = kernel.name_str(provable, "and_elim2");
    let or_intro1 = kernel.name_str(provable, "or_intro1");
    let or_intro2 = kernel.name_str(provable, "or_intro2");
    let or_elim = kernel.name_str(provable, "or_elim");
    let imp_intro = kernel.name_str(provable, "imp_intro");
    let imp_elim = kernel.name_str(provable, "imp_elim");
    let bot_elim = kernel.name_str(provable, "bot_elim");

    let names = Names {
        and_: heyting.and_,
        or_: heyting.or_,
        imp: heyting.imp,
        bot: heyting.bot,
        formula_ty,
        flist_ty,
        provable,
        cons,
        nil,
    };

    let provable_ty = {
        let prop = kernel.sort_zero();
        let inner = kernel.pi(anon, formula_ty, prop, BinderInfo::Default);
        kernel.pi(anon, flist_ty, inner, BinderInfo::Default)
    };

    let ctor_decls = vec![
        (ax_head, ax_head_ty(kernel, &names)),
        (weaken, weaken_ty(kernel, &names)),
        (and_intro, and_intro_ty(kernel, &names)),
        (and_elim1, and_elim_ty(kernel, &names, true)),
        (and_elim2, and_elim_ty(kernel, &names, false)),
        (or_intro1, or_intro_ty(kernel, &names, true)),
        (or_intro2, or_intro_ty(kernel, &names, false)),
        (or_elim, or_elim_ty(kernel, &names)),
        (imp_intro, imp_intro_ty(kernel, &names)),
        (imp_elim, imp_elim_ty(kernel, &names)),
        (bot_elim, bot_elim_ty(kernel, &names)),
    ];
    kernel.add_inductive(provable, &[], 0, provable_ty, &ctor_decls)?;

    let imp_self = declare_imp_self(kernel, &heyting, &names, imp_intro, ax_head)?;
    let and_elim1_example =
        declare_and_elim1_example(kernel, &heyting, &names, imp_intro, ax_head, and_elim1)?;

    Ok(IpcProvablePrelude {
        heyting,
        formula_list,
        nil,
        cons,
        formula_list_rec,
        provable,
        ax_head,
        weaken,
        and_intro,
        and_elim1,
        and_elim2,
        or_intro1,
        or_intro2,
        or_elim,
        imp_intro,
        imp_elim,
        bot_elim,
        imp_self,
        and_elim1_example,
    })
}

/// The names [`ax_head_ty`] and friends need, gathered so each constructor
/// builder takes one argument instead of eight.
struct Names {
    and_: NameId,
    or_: NameId,
    imp: NameId,
    bot: NameId,
    formula_ty: ExprId,
    flist_ty: ExprId,
    provable: NameId,
    cons: NameId,
    nil: NameId,
}

fn apply_all(kernel: &mut crate::Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// Build `Pi (v : ty), body`, abstracting the single fvar `id` out of `body`.
fn pi_fv(kernel: &mut crate::Kernel, id: u64, ty: ExprId, body: ExprId) -> ExprId {
    let anon = kernel.anon();
    let abstracted = kernel.abstract_fvars(body, &[id]);
    kernel.pi(anon, ty, abstracted, BinderInfo::Default)
}

/// A non-dependent function type `hyp -> concl` (`concl` built before this
/// call, so it carries no loose reference to the about-to-be-introduced
/// binder).
fn arrow(kernel: &mut crate::Kernel, hyp: ExprId, concl: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, hyp, concl, BinderInfo::Default)
}

fn cons_app(kernel: &mut crate::Kernel, n: &Names, head: ExprId, tail: ExprId) -> ExprId {
    let cons_const = kernel.const_(n.cons, vec![]);
    apply_all(kernel, cons_const, &[head, tail])
}

fn provable_app(kernel: &mut crate::Kernel, n: &Names, ctx: ExprId, phi: ExprId) -> ExprId {
    let provable_const = kernel.const_(n.provable, vec![]);
    apply_all(kernel, provable_const, &[ctx, phi])
}

fn and_app(kernel: &mut crate::Kernel, n: &Names, a: ExprId, b: ExprId) -> ExprId {
    let c = kernel.const_(n.and_, vec![]);
    apply_all(kernel, c, &[a, b])
}

fn or_app(kernel: &mut crate::Kernel, n: &Names, a: ExprId, b: ExprId) -> ExprId {
    let c = kernel.const_(n.or_, vec![]);
    apply_all(kernel, c, &[a, b])
}

fn imp_app(kernel: &mut crate::Kernel, n: &Names, a: ExprId, b: ExprId) -> ExprId {
    let c = kernel.const_(n.imp, vec![]);
    apply_all(kernel, c, &[a, b])
}

/// `ax_head : (ctx : FormulaList) -> (phi : Formula) -> Provable (cons phi ctx) phi`.
fn ax_head_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 941_001_u64;
    let phi_id = 941_002_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let extended = cons_app(kernel, n, phi, ctx);
    let body = provable_app(kernel, n, extended, phi);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, body);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `weaken : (ctx) -> (phi psi : Formula) -> Provable ctx phi -> Provable (cons psi ctx) phi`.
fn weaken_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 942_001_u64;
    let phi_id = 942_002_u64;
    let psi_id = 942_003_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let hyp = provable_app(kernel, n, ctx, phi);
    let extended = cons_app(kernel, n, psi, ctx);
    let concl = provable_app(kernel, n, extended, phi);
    let body = arrow(kernel, hyp, concl);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, body);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `and_intro : (ctx) -> (phi psi : Formula) -> Provable ctx phi -> Provable ctx psi -> Provable ctx (and_ phi psi)`.
fn and_intro_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 943_001_u64;
    let phi_id = 943_002_u64;
    let psi_id = 943_003_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let hyp1 = provable_app(kernel, n, ctx, phi);
    let hyp2 = provable_app(kernel, n, ctx, psi);
    let conj = and_app(kernel, n, phi, psi);
    let concl = provable_app(kernel, n, ctx, conj);
    let inner = arrow(kernel, hyp2, concl);
    let body = arrow(kernel, hyp1, inner);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, body);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `and_elim1 : (ctx) -> (phi psi) -> Provable ctx (and_ phi psi) -> Provable ctx phi`
/// (or, with `first = false`, `and_elim2`'s `-> Provable ctx psi`).
fn and_elim_ty(kernel: &mut crate::Kernel, n: &Names, first: bool) -> ExprId {
    let ctx_id = 944_001_u64;
    let phi_id = 944_002_u64;
    let psi_id = 944_003_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let conj = and_app(kernel, n, phi, psi);
    let hyp = provable_app(kernel, n, ctx, conj);
    let target = if first { phi } else { psi };
    let concl = provable_app(kernel, n, ctx, target);
    let body = arrow(kernel, hyp, concl);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, body);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `or_intro1 : (ctx) -> (phi psi) -> Provable ctx phi -> Provable ctx (or_ phi psi)`
/// (or, with `first = false`, `or_intro2`'s `Provable ctx psi -> ...`).
fn or_intro_ty(kernel: &mut crate::Kernel, n: &Names, first: bool) -> ExprId {
    let ctx_id = 945_001_u64;
    let phi_id = 945_002_u64;
    let psi_id = 945_003_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let source = if first { phi } else { psi };
    let hyp = provable_app(kernel, n, ctx, source);
    let disj = or_app(kernel, n, phi, psi);
    let concl = provable_app(kernel, n, ctx, disj);
    let body = arrow(kernel, hyp, concl);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, body);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `or_elim : (ctx) -> (phi psi chi) -> Provable ctx (or_ phi psi) ->
/// Provable (cons phi ctx) chi -> Provable (cons psi ctx) chi -> Provable ctx chi`.
fn or_elim_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 946_001_u64;
    let phi_id = 946_002_u64;
    let psi_id = 946_003_u64;
    let chi_id = 946_004_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let chi = kernel.fvar(chi_id);
    let disj = or_app(kernel, n, phi, psi);
    let hyp1 = provable_app(kernel, n, ctx, disj);
    let ctx_phi = cons_app(kernel, n, phi, ctx);
    let hyp2 = provable_app(kernel, n, ctx_phi, chi);
    let ctx_psi = cons_app(kernel, n, psi, ctx);
    let hyp3 = provable_app(kernel, n, ctx_psi, chi);
    let concl = provable_app(kernel, n, ctx, chi);
    let inner = arrow(kernel, hyp3, concl);
    let inner = arrow(kernel, hyp2, inner);
    let body = arrow(kernel, hyp1, inner);
    let with_chi = pi_fv(kernel, chi_id, n.formula_ty, body);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, with_chi);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `imp_intro : (ctx) -> (phi psi) -> Provable (cons phi ctx) psi -> Provable ctx (imp phi psi)`.
fn imp_intro_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 947_001_u64;
    let phi_id = 947_002_u64;
    let psi_id = 947_003_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let ctx_phi = cons_app(kernel, n, phi, ctx);
    let hyp = provable_app(kernel, n, ctx_phi, psi);
    let implication = imp_app(kernel, n, phi, psi);
    let concl = provable_app(kernel, n, ctx, implication);
    let body = arrow(kernel, hyp, concl);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, body);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `imp_elim : (ctx) -> (phi psi) -> Provable ctx (imp phi psi) -> Provable ctx phi -> Provable ctx psi`.
fn imp_elim_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 948_001_u64;
    let phi_id = 948_002_u64;
    let psi_id = 948_003_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let psi = kernel.fvar(psi_id);
    let implication = imp_app(kernel, n, phi, psi);
    let hyp1 = provable_app(kernel, n, ctx, implication);
    let hyp2 = provable_app(kernel, n, ctx, phi);
    let concl = provable_app(kernel, n, ctx, psi);
    let inner = arrow(kernel, hyp2, concl);
    let body = arrow(kernel, hyp1, inner);
    let with_psi = pi_fv(kernel, psi_id, n.formula_ty, body);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, with_psi);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `bot_elim : (ctx) -> (phi) -> Provable ctx bot -> Provable ctx phi`.
fn bot_elim_ty(kernel: &mut crate::Kernel, n: &Names) -> ExprId {
    let ctx_id = 949_001_u64;
    let phi_id = 949_002_u64;
    let ctx = kernel.fvar(ctx_id);
    let phi = kernel.fvar(phi_id);
    let bot = kernel.const_(n.bot, vec![]);
    let hyp = provable_app(kernel, n, ctx, bot);
    let concl = provable_app(kernel, n, ctx, phi);
    let body = arrow(kernel, hyp, concl);
    let with_phi = pi_fv(kernel, phi_id, n.formula_ty, body);
    pi_fv(kernel, ctx_id, n.flist_ty, with_phi)
}

/// `Formula.var k`, for building example closed formulas.
fn var_app(kernel: &mut crate::Kernel, heyting: &IpcHeytingPrelude, k: u32) -> ExprId {
    let mut idx = kernel.const_(heyting.nat.zero, vec![]);
    let succ = kernel.const_(heyting.nat.succ, vec![]);
    for _ in 0..k {
        idx = kernel.app(succ, idx);
    }
    let var_const = kernel.const_(heyting.var, vec![]);
    kernel.app(var_const, idx)
}

/// Declare `ipc_provable_imp_self : Provable FormulaList.nil (Formula.imp p p)`
/// where `p := Formula.var 0`, proved by `imp_intro nil p p (ax_head nil p)` —
/// a genuine natural-deduction proof term (assume `p`, conclude `p -> p`),
/// admitted through the trusted gate.
fn declare_imp_self(
    kernel: &mut crate::Kernel,
    heyting: &IpcHeytingPrelude,
    n: &Names,
    imp_intro: NameId,
    ax_head: NameId,
) -> Result<NameId, KernelError> {
    let anon = kernel.anon();
    let nil_expr = kernel.const_(n.nil, vec![]);
    let p = var_app(kernel, heyting, 0);

    // ax_head nil p : Provable (cons p nil) p.
    let ax_head_const = kernel.const_(ax_head, vec![]);
    let ax_head_term = apply_all(kernel, ax_head_const, &[nil_expr, p]);

    // imp_intro nil p p (ax_head nil p) : Provable nil (imp p p).
    let imp_intro_const = kernel.const_(imp_intro, vec![]);
    let value = apply_all(kernel, imp_intro_const, &[nil_expr, p, p, ax_head_term]);

    let self_imp = imp_app(kernel, n, p, p);
    let stated_ty = provable_app(kernel, n, nil_expr, self_imp);

    let name = kernel.name_str(anon, "ipc_provable_imp_self");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stated_ty,
        value,
    })?;
    Ok(name)
}

/// Declare `ipc_provable_and_elim1_example : Provable FormulaList.nil
/// (Formula.imp (Formula.and_ p q) p)` where `p := Formula.var 0`,
/// `q := Formula.var 1`, proved by `imp_intro nil (and_ p q) p (and_elim1
/// (cons (and_ p q) nil) p q (ax_head nil (and_ p q)))`.
fn declare_and_elim1_example(
    kernel: &mut crate::Kernel,
    heyting: &IpcHeytingPrelude,
    n: &Names,
    imp_intro: NameId,
    ax_head: NameId,
    and_elim1: NameId,
) -> Result<NameId, KernelError> {
    let anon = kernel.anon();
    let nil_expr = kernel.const_(n.nil, vec![]);
    let p = var_app(kernel, heyting, 0);
    let q = var_app(kernel, heyting, 1);
    let and_pq = and_app(kernel, n, p, q);
    let ctx_and_pq = cons_app(kernel, n, and_pq, nil_expr);

    // ax_head nil (and_ p q) : Provable (cons (and_ p q) nil) (and_ p q).
    let ax_head_const = kernel.const_(ax_head, vec![]);
    let ax_head_term = apply_all(kernel, ax_head_const, &[nil_expr, and_pq]);

    // and_elim1 (cons (and_ p q) nil) p q (...) : Provable (cons (and_ p q) nil) p.
    let and_elim1_const = kernel.const_(and_elim1, vec![]);
    let and_elim1_term = apply_all(kernel, and_elim1_const, &[ctx_and_pq, p, q, ax_head_term]);

    // imp_intro nil (and_ p q) p (...) : Provable nil (imp (and_ p q) p).
    let imp_intro_const = kernel.const_(imp_intro, vec![]);
    let value = apply_all(
        kernel,
        imp_intro_const,
        &[nil_expr, and_pq, p, and_elim1_term],
    );

    let conclusion_imp = imp_app(kernel, n, and_pq, p);
    let stated_ty = provable_app(kernel, n, nil_expr, conclusion_imp);

    let name = kernel.name_str(anon, "ipc_provable_and_elim1_example");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stated_ty,
        value,
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Kernel;

    /// The prelude builds at all: `FormulaList`, its recursor, `Provable`,
    /// and all eleven constructors are genuine environment declarations.
    #[test]
    fn ipc_provable_prelude_builds() {
        let mut kernel = Kernel::new();
        let p = build_ipc_provable_prelude(&mut kernel).expect("prelude must build");
        assert!(kernel.environment().get(p.formula_list).is_some());
        assert!(kernel.environment().get(p.formula_list_rec).is_some());
        assert!(kernel.environment().get(p.nil).is_some());
        assert!(kernel.environment().get(p.cons).is_some());
        assert!(kernel.environment().get(p.provable).is_some());
        for ctor in [
            p.ax_head,
            p.weaken,
            p.and_intro,
            p.and_elim1,
            p.and_elim2,
            p.or_intro1,
            p.or_intro2,
            p.or_elim,
            p.imp_intro,
            p.imp_elim,
            p.bot_elim,
        ] {
            assert!(
                kernel.environment().get(ctor).is_some(),
                "constructor {ctor:?} must be a genuine declaration"
            );
        }
    }

    /// The two example derivations (`p -> p`, `(p and q) -> p`) admit through
    /// the trusted gate and are axiom-free -- genuine natural-deduction proof
    /// terms built from `Provable`'s constructors, not assertions.
    #[test]
    fn example_derivations_admit_and_are_axiom_free() {
        let mut kernel = Kernel::new();
        let p = build_ipc_provable_prelude(&mut kernel).expect("prelude must build");
        assert!(kernel.environment().get(p.imp_self).is_some());
        assert!(kernel.environment().get(p.and_elim1_example).is_some());
        assert!(
            kernel.axiom_footprint(p.imp_self).is_empty(),
            "imp_self must be axiom-free"
        );
        assert!(
            kernel.axiom_footprint(p.and_elim1_example).is_empty(),
            "and_elim1_example must be axiom-free"
        );
    }

    /// Scoping control mirroring `ipc_heyting.rs`'s
    /// `no_prior_derivation_relation_exists_before_this_file`: as of THIS
    /// file, `Provable` IS present by exact name match, checked the same way
    /// that prior test checked its absence (never a substring test, which
    /// could pass vacuously against an unrelated declaration).
    #[test]
    fn provable_relation_is_present_and_findable_by_exact_name() {
        let mut kernel = Kernel::new();
        let p = build_ipc_provable_prelude(&mut kernel).expect("prelude must build");
        let names: Vec<String> = kernel
            .environment()
            .iter()
            .map(|(name, _)| kernel.display_name(*name).to_string())
            .collect();
        let provable_str = kernel.display_name(p.provable).to_string();
        assert!(
            names.iter().any(|n| n == &provable_str),
            "Provable must be found by exact name match"
        );
        // Positive control of the identical lookup kind: FormulaList, this
        // file's own other new declaration.
        let flist_str = kernel.display_name(p.formula_list).to_string();
        assert!(names.iter().any(|n| n == &flist_str));
    }

    // -----------------------------------------------------------------
    // Non-kernel, Rust-level bounded/finite proof search: a non-vacuity
    // sanity check on the RULE SET, not a formalized theorem. See the
    // module doc's "What this slice proves, and what it does not" section.
    // -----------------------------------------------------------------

    /// A minimal propositional-formula shape used ONLY by this Rust-level
    /// search, deliberately kept separate from the kernel's `Formula` (which
    /// has no `PartialEq`/`Hash` and lives inside the kernel arena). The
    /// eleven closure rules in [`saturate`] are written to mirror
    /// `Provable`'s eleven constructors one for one -- see the inline
    /// comments pairing each rule with its kernel counterpart by name.
    #[derive(Clone, PartialEq, Eq, Debug)]
    enum MetaFormula {
        P,
        Q,
        Bot,
        And(Box<MetaFormula>, Box<MetaFormula>),
        Or(Box<MetaFormula>, Box<MetaFormula>),
        Imp(Box<MetaFormula>, Box<MetaFormula>),
    }

    impl MetaFormula {
        fn imp(a: MetaFormula, b: MetaFormula) -> MetaFormula {
            MetaFormula::Imp(Box::new(a), Box::new(b))
        }
        fn and(a: MetaFormula, b: MetaFormula) -> MetaFormula {
            MetaFormula::And(Box::new(a), Box::new(b))
        }
        fn or(a: MetaFormula, b: MetaFormula) -> MetaFormula {
            MetaFormula::Or(Box::new(a), Box::new(b))
        }
    }

    /// The finite universe `S`: exactly the subformulas needed for the three
    /// queries below (`p -> p`, `(p and q) -> p`, `p or not p`). Because
    /// normal (cut-free, no maximal formula) intuitionistic natural
    /// deduction derivations enjoy the subformula property, a query whose
    /// full subformula closure lies inside `S` is decided CORRECTLY by
    /// [`saturate`]'s closure over `S` -- this is not an ad hoc truncation,
    /// it is exactly the closure the normal-form theorem says is sufficient
    /// for these three goals from the empty context.
    fn finite_search_universe() -> Vec<MetaFormula> {
        let p = MetaFormula::P;
        let q = MetaFormula::Q;
        let bot = MetaFormula::Bot;
        let notp = MetaFormula::imp(p.clone(), bot.clone());
        let pandq = MetaFormula::and(p.clone(), q.clone());
        let por_notp = MetaFormula::or(p.clone(), notp.clone());
        let imp_pp = MetaFormula::imp(p.clone(), p.clone());
        let imp_andq_p = MetaFormula::imp(pandq.clone(), p.clone());
        vec![p, q, bot, notp, pandq, por_notp, imp_pp, imp_andq_p]
    }

    /// Forward-chaining fixpoint over `(context, goal)` pairs where `context`
    /// is a bitmask subset of `universe` and `goal` is an index into
    /// `universe`. Representing the context as a SET (not `Provable`'s
    /// `FormulaList`, an ordered structure) gives `Provable.weaken` for
    /// free: the base "membership" rule below is re-evaluated independently
    /// at every bitmask value, so any fact resting only on membership in a
    /// subset context re-derives identically at every bitmask superset.
    ///
    /// Each closure step below is commented with the `Provable` constructor
    /// it mirrors.
    #[allow(clippy::too_many_lines)]
    fn saturate(universe: &[MetaFormula]) -> std::collections::HashSet<(u32, usize)> {
        let index_of = |f: &MetaFormula| universe.iter().position(|g| g == f);
        let n = universe.len();
        let mut derivable: std::collections::HashSet<(u32, usize)> =
            std::collections::HashSet::new();

        // `ax_head` (+ `weaken`, folded in via the bitmask-superset argument
        // above): every element of `ctx` is derivable from `ctx`, at every
        // `ctx` independently.
        for ctx in 0u32..(1 << n) {
            for i in 0..n {
                if ctx & (1 << i) != 0 {
                    derivable.insert((ctx, i));
                }
            }
        }

        loop {
            let mut changed = false;
            for ctx in 0u32..(1 << n) {
                // Introduction rules: `and_intro`, `or_intro1`/`or_intro2`,
                // `imp_intro`.
                for (goal_index, goal) in universe.iter().enumerate() {
                    if derivable.contains(&(ctx, goal_index)) {
                        continue;
                    }
                    let found = match goal {
                        MetaFormula::And(a, b) => match (index_of(a), index_of(b)) {
                            (Some(ai), Some(bi)) => {
                                derivable.contains(&(ctx, ai)) && derivable.contains(&(ctx, bi))
                            }
                            _ => false,
                        },
                        MetaFormula::Or(a, b) => {
                            let via_a =
                                index_of(a).is_some_and(|ai| derivable.contains(&(ctx, ai)));
                            let via_b =
                                index_of(b).is_some_and(|bi| derivable.contains(&(ctx, bi)));
                            via_a || via_b
                        }
                        MetaFormula::Imp(a, b) => match (index_of(a), index_of(b)) {
                            (Some(ai), Some(bi)) => {
                                let extended = ctx | (1 << ai);
                                derivable.contains(&(extended, bi))
                            }
                            _ => false,
                        },
                        MetaFormula::P | MetaFormula::Q | MetaFormula::Bot => false,
                    };
                    if found {
                        derivable.insert((ctx, goal_index));
                        changed = true;
                    }
                }
                // Elimination rules, reading a premise already derivable
                // from `ctx`: `and_elim1`/`and_elim2`, `or_elim`, `imp_elim`,
                // `bot_elim`.
                for (premise_index, premise) in universe.iter().enumerate() {
                    if !derivable.contains(&(ctx, premise_index)) {
                        continue;
                    }
                    match premise {
                        MetaFormula::And(a, b) => {
                            if let Some(ai) = index_of(a)
                                && derivable.insert((ctx, ai))
                            {
                                changed = true;
                            }
                            if let Some(bi) = index_of(b)
                                && derivable.insert((ctx, bi))
                            {
                                changed = true;
                            }
                        }
                        MetaFormula::Or(a, b) => {
                            if let (Some(ai), Some(bi)) = (index_of(a), index_of(b)) {
                                let ctx_a = ctx | (1 << ai);
                                let ctx_b = ctx | (1 << bi);
                                for goal_index in 0..n {
                                    if derivable.contains(&(ctx_a, goal_index))
                                        && derivable.contains(&(ctx_b, goal_index))
                                        && derivable.insert((ctx, goal_index))
                                    {
                                        changed = true;
                                    }
                                }
                            }
                        }
                        MetaFormula::Imp(a, b) => {
                            if let (Some(ai), Some(bi)) = (index_of(a), index_of(b))
                                && derivable.contains(&(ctx, ai))
                                && derivable.insert((ctx, bi))
                            {
                                changed = true;
                            }
                        }
                        MetaFormula::Bot => {
                            for goal_index in 0..n {
                                if derivable.insert((ctx, goal_index)) {
                                    changed = true;
                                }
                            }
                        }
                        MetaFormula::P | MetaFormula::Q => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }
        derivable
    }

    /// The non-vacuity check itself: the same rule set that derives the two
    /// kernel-checked positive theorems ([`declare_imp_self`],
    /// [`declare_and_elim1_example`]) does NOT derive `p or not p` from the
    /// empty context. This is the cheapest available discriminating check
    /// on `Provable`'s ENCODING before soundness (slice 4) exists to make
    /// the kernel itself answer this question -- see the module doc.
    #[test]
    fn finite_search_discriminates_between_derivable_and_pem() {
        let universe = finite_search_universe();
        let derivable = saturate(&universe);
        let index_of = |f: &MetaFormula| universe.iter().position(|g| g == f).unwrap();

        let imp_pp = MetaFormula::imp(MetaFormula::P, MetaFormula::P);
        let pandq = MetaFormula::and(MetaFormula::P, MetaFormula::Q);
        let imp_andq_p = MetaFormula::imp(pandq, MetaFormula::P);
        let notp = MetaFormula::imp(MetaFormula::P, MetaFormula::Bot);
        let por_notp = MetaFormula::or(MetaFormula::P, notp);

        assert!(
            derivable.contains(&(0, index_of(&imp_pp))),
            "p -> p must be derivable from the empty context (matches the kernel-checked \
             ipc_provable_imp_self)"
        );
        assert!(
            derivable.contains(&(0, index_of(&imp_andq_p))),
            "(p and q) -> p must be derivable from the empty context (matches the \
             kernel-checked ipc_provable_and_elim1_example)"
        );
        assert!(
            !derivable.contains(&(0, index_of(&por_notp))),
            "p or not p must NOT be derivable from the empty context -- if this fires, the \
             rule set is too permissive (an encoding bug), since ipc_heyting.rs's Heyting-chain \
             countermodel already shows p or not p is not universally valid"
        );
    }
}
