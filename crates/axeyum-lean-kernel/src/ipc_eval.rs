//! **Slice 3 of the decomposition recorded in `ipc_heyting.rs`'s module docs**
//! (and in `docs/plan/status/273-logic-excluded-middle.md`): a generic
//! evaluator `eval : Formula -> (Nat -> Nat) -> Nat`, built as a genuine
//! [`crate::Kernel::add_recursive_datatype_family`]-generated `Formula.rec`
//! application (motive `fun _ => (Nat -> Nat) -> Nat`) rather than the
//! one-off direct-`Nat` computation `ipc_heyting.rs` uses for its single
//! closed `pem_instance` countermodel check.
//!
//! Depends only on `ipc_heyting.rs` (slice 1) — `Formula.rec` already exists
//! as `IpcHeytingPrelude::formula_rec`, and `meet3`/`join3`/`himp3` already
//! exist as the connective cases. Nothing from `ipc_provable.rs` (slice 2,
//! the `Provable` relation) is needed or used here.
//!
//! ## The recursor application
//!
//! For each of `Formula`'s five constructors, in the SAME order they were
//! declared in `ipc_heyting.rs` (`var, bot, and_, or_, imp`), `Formula.rec`
//! requires one minor premise, each of shape `Pi (fields…) (ih per recursive
//! field, in field order), motive (constructor fields…)` — see
//! `inductive.rs`'s module docs for the general schema. Our motive is
//! **non-dependent** (constant in the `Formula` argument, `fun _ => (Nat ->
//! Nat) -> Nat`), so every minor's return type is simply `(Nat -> Nat) ->
//! Nat` regardless of which constructor it belongs to:
//!
//! - `m_var : Nat -> (Nat -> Nat) -> Nat := fun i v => v i` (one `Carrier`
//!   field, no induction hypothesis — `var` is not recursive).
//! - `m_bot : (Nat -> Nat) -> Nat := fun v => 0` (no fields at all).
//! - `m_and_ : Formula -> Formula -> ((Nat->Nat)->Nat) -> ((Nat->Nat)->Nat)
//!   -> (Nat->Nat)->Nat := fun a b ih_a ih_b v => meet3 (ih_a v) (ih_b v)`
//!   (two `Recursive` fields, so two induction hypotheses `ih_a`/`ih_b`
//!   appended after the field binders, in field order).
//! - `m_or_` / `m_imp`: the same shape as `m_and_`, with `join3` / `himp3`
//!   in place of `meet3`.
//!
//! `eval := fun (f : Formula) => Formula.rec.{1} motive m_var m_bot m_and_
//! m_or_ m_imp f`, which has type `Formula -> (Nat -> Nat) -> Nat` because
//! `motive f` beta-reduces to the constant `(Nat -> Nat) -> Nat` for every
//! `f`. The elimination universe is `1` (`Type`, not `Prop`): the motive's
//! codomain `(Nat -> Nat) -> Nat` is itself a `Sort 1` type, the same
//! universe `ipc_heyting.rs`'s `recursive_datatype_size` example uses for a
//! `Nat`-valued motive.
//!
//! ## Non-negotiable: this is a `Definition`, and admission proves NOTHING
//! about what it computes
//!
//! `Kernel::add_declaration` only type-checks. `eval` returning garbage at
//! every input would still have the stated type `Formula -> (Nat -> Nat) ->
//! Nat`, and the kernel would admit it exactly as readily as a correct one —
//! this is the workspace's standing "the trusted gate cannot tell you a
//! `Definition` is wrong, only evaluation can" gotcha, applying here to a
//! recursor application exactly as it does to any other computed function.
//!
//! So the module tests below are not incidental: they are what pins `eval`'s
//! meaning. Every case is hand-computed in a doc comment on the test itself
//! **before** the assertion, against `ipc_heyting.rs`'s own definitions of
//! `meet3 = min`, `join3 = max`, `himp3 a b = if a <= b then 2 else b`. The
//! discriminating table `meet3(0,1)=0, join3(0,1)=1, himp3(0,1)=2` (all
//! three different at the same input pair) is exercised directly through
//! `eval` rather than assumed, so a copy-paste error between the three
//! connective cases fails loudly rather than passing silently. One test
//! also cross-checks `eval` against `ipc_heyting.rs`'s already-proven
//! countermodel theorem `ipc_heyting_join_not_ne_top`
//! (`join3 1 (not3 1) = 1`) by evaluating `pem_instance` itself, tying the
//! new generic recursor path back to the existing direct-`Nat` computation.
//!
//! ## What slice 4 still needs
//!
//! Soundness: `Provable ctx phi -> (every valuation satisfying ctx satisfies
//! phi)`, i.e. `forall rho, sat ctx rho -> eval phi rho = 2`, by induction
//! on `Provable`'s own generated recursor. This file supplies the `eval`
//! half of that statement; it does not attempt soundness itself. See
//! `ipc_provable.rs`'s module docs for the full remaining shape.

use crate::{BinderInfo, Declaration, ExprId, IpcHeytingPrelude, KernelError, NameId};
use crate::{ReducibilityHint, build_ipc_heyting_prelude};

/// Names produced by [`build_ipc_eval_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IpcEvalPrelude {
    /// `Formula` and the 3-element Heyting-chain semantics this package
    /// evaluates a formula into.
    pub heyting: IpcHeytingPrelude,
    /// `eval : Formula -> (Nat -> Nat) -> Nat`.
    pub eval: NameId,
}

/// Build [`IpcHeytingPrelude`] (slice 1) and the generic `eval` recursor
/// application on top of it, registering `eval` through the trusted
/// [`crate::Kernel::add_declaration`] gate.
///
/// # Errors
///
/// Returns the [`KernelError`] from the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_ipc_eval_prelude(kernel: &mut crate::Kernel) -> Result<IpcEvalPrelude, KernelError> {
    let heyting = build_ipc_heyting_prelude(kernel)?;
    let eval = declare_eval(kernel, &heyting)?;
    Ok(IpcEvalPrelude { heyting, eval })
}

fn apply_all(kernel: &mut crate::Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// Build `fun (x : ty) => body`, abstracting the single fvar `id` out of
/// `body`.
fn lam_fv(kernel: &mut crate::Kernel, id: u64, ty: ExprId, body: ExprId) -> ExprId {
    let anon = kernel.anon();
    let abstracted = kernel.abstract_fvars(body, &[id]);
    kernel.lam(anon, ty, abstracted, BinderInfo::Default)
}

/// Build the shared minor-premise shape for `and_`/`or_`/`imp`: each takes
/// two recursive fields `(a, b) : Formula` (field order), then their two
/// induction hypotheses `(ih_a, ih_b) : (Nat -> Nat) -> Nat` (appended after
/// the field binders, in field order, per `inductive.rs`'s recursor schema),
/// and returns `fun v => op (ih_a v) (ih_b v)`.
///
/// `base_id` and the next four `u64`s after it must not collide with any
/// other fvar id live at the same time; each call site uses a distinct
/// hundred-block.
fn binop_minor(
    kernel: &mut crate::Kernel,
    val_ty: ExprId,
    formula_ty: ExprId,
    op: NameId,
    base_id: u64,
) -> ExprId {
    let a_id = base_id;
    let b_id = base_id + 1;
    let iha_id = base_id + 2;
    let ihb_id = base_id + 3;
    let v_id = base_id + 4;

    let iha_fv = kernel.fvar(iha_id);
    let ihb_fv = kernel.fvar(ihb_id);
    let v_fv = kernel.fvar(v_id);
    let iha_v = kernel.app(iha_fv, v_fv);
    let ihb_v = kernel.app(ihb_fv, v_fv);
    let op_const = kernel.const_(op, vec![]);
    let combined = apply_all(kernel, op_const, &[iha_v, ihb_v]);

    let body = lam_fv(kernel, v_id, val_ty, combined);
    let body = lam_fv(kernel, ihb_id, val_ty, body);
    let body = lam_fv(kernel, iha_id, val_ty, body);
    let body = lam_fv(kernel, b_id, formula_ty, body);
    lam_fv(kernel, a_id, formula_ty, body)
}

/// Declare `eval : Formula -> (Nat -> Nat) -> Nat` as a `Formula.rec`
/// application. See the module docs for the full minor-premise table.
fn declare_eval(kernel: &mut crate::Kernel, p: &IpcHeytingPrelude) -> Result<NameId, KernelError> {
    let anon = kernel.anon();
    let nat_ty = kernel.const_(p.nat.nat, vec![]);
    let formula_ty = kernel.const_(p.formula, vec![]);
    // val_ty := Nat -> Nat (the valuation's type).
    let val_ty = kernel.pi(anon, nat_ty, nat_ty, BinderInfo::Default);
    // motive_codomain := (Nat -> Nat) -> Nat -- what `eval` returns once
    // applied to a formula; the motive itself is constant in the `Formula`
    // argument, so this expression is reused directly (no bvar to abstract)
    // both as the motive's lambda body and as `eval`'s stated codomain.
    let motive_codomain = kernel.pi(anon, val_ty, nat_ty, BinderInfo::Default);
    let motive = kernel.lam(anon, formula_ty, motive_codomain, BinderInfo::Default);

    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);

    // m_var : Nat -> (Nat -> Nat) -> Nat := fun i v => v i.
    let i_id = 961_101_u64;
    let v_var_id = 961_102_u64;
    let i_fv = kernel.fvar(i_id);
    let v_var_fv = kernel.fvar(v_var_id);
    let var_body = kernel.app(v_var_fv, i_fv);
    let m_var = lam_fv(kernel, v_var_id, val_ty, var_body);
    let m_var = lam_fv(kernel, i_id, nat_ty, m_var);

    // m_bot : (Nat -> Nat) -> Nat := fun v => 0.
    let v_bot_id = 961_201_u64;
    let zero_const = kernel.const_(p.nat.zero, vec![]);
    let m_bot = lam_fv(kernel, v_bot_id, val_ty, zero_const);

    let m_and = binop_minor(kernel, val_ty, formula_ty, p.meet3, 961_301_u64);
    let m_or = binop_minor(kernel, val_ty, formula_ty, p.join3, 961_401_u64);
    let m_imp = binop_minor(kernel, val_ty, formula_ty, p.himp3, 961_501_u64);

    let rec_const = kernel.const_(p.formula_rec, vec![one_lvl]);
    let applied = apply_all(
        kernel,
        rec_const,
        &[motive, m_var, m_bot, m_and, m_or, m_imp],
    );

    let f_id = 961_601_u64;
    let f_fv = kernel.fvar(f_id);
    let body = kernel.app(applied, f_fv);
    let value = lam_fv(kernel, f_id, formula_ty, body);

    let ty = kernel.pi(anon, formula_ty, motive_codomain, BinderInfo::Default);

    let name = kernel.name_str(anon, "ipc_eval");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Kernel;

    /// The unary numeral `succ^n zero`. Kept to tiny `n` (this file only
    /// ever needs `0`, `1`, `2`) — see the workspace-wide gotcha about unary
    /// `Nat` magnitudes blowing up kernel reduction budgets at large `n`.
    fn num(kernel: &mut Kernel, p: &IpcHeytingPrelude, n: u32) -> ExprId {
        let mut e = kernel.const_(p.nat.zero, vec![]);
        let succ = kernel.const_(p.nat.succ, vec![]);
        for _ in 0..n {
            e = kernel.app(succ, e);
        }
        e
    }

    /// `Formula.var k`.
    fn var(kernel: &mut Kernel, p: &IpcHeytingPrelude, k: u32) -> ExprId {
        let idx = num(kernel, p, k);
        let var_const = kernel.const_(p.var, vec![]);
        kernel.app(var_const, idx)
    }

    fn bot(kernel: &mut Kernel, p: &IpcHeytingPrelude) -> ExprId {
        kernel.const_(p.bot, vec![])
    }

    fn and_(kernel: &mut Kernel, p: &IpcHeytingPrelude, a: ExprId, b: ExprId) -> ExprId {
        let c = kernel.const_(p.and_, vec![]);
        apply_all(kernel, c, &[a, b])
    }

    fn or_(kernel: &mut Kernel, p: &IpcHeytingPrelude, a: ExprId, b: ExprId) -> ExprId {
        let c = kernel.const_(p.or_, vec![]);
        apply_all(kernel, c, &[a, b])
    }

    fn imp(kernel: &mut Kernel, p: &IpcHeytingPrelude, a: ExprId, b: ExprId) -> ExprId {
        let c = kernel.const_(p.imp, vec![]);
        apply_all(kernel, c, &[a, b])
    }

    /// `fun n => n` (the identity valuation): `v(0) = 0`, `v(1) = 1`.
    fn valuation_identity(kernel: &mut Kernel, p: &IpcHeytingPrelude) -> ExprId {
        let n_id = 962_001_u64;
        let n_fv = kernel.fvar(n_id);
        let nat_ty = kernel.const_(p.nat.nat, vec![]);
        lam_fv(kernel, n_id, nat_ty, n_fv)
    }

    /// `fun _ => k` (a constant valuation, ignoring its argument).
    fn valuation_const(kernel: &mut Kernel, p: &IpcHeytingPrelude, k: u32) -> ExprId {
        let junk_id = 962_101_u64 + u64::from(k);
        let k_expr = num(kernel, p, k);
        let nat_ty = kernel.const_(p.nat.nat, vec![]);
        lam_fv(kernel, junk_id, nat_ty, k_expr)
    }

    /// `eval f v`.
    fn eval_app(kernel: &mut Kernel, eval: NameId, f: ExprId, v: ExprId) -> ExprId {
        let eval_const = kernel.const_(eval, vec![]);
        apply_all(kernel, eval_const, &[f, v])
    }

    /// The prelude builds, `eval` is a real declaration, and `Formula.rec`
    /// is what it was built from (not some other route).
    #[test]
    fn ipc_eval_prelude_builds() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        assert!(kernel.environment().get(p.eval).is_some());
    }

    /// `eval`'s inferred type matches its stated `Formula -> (Nat -> Nat) ->
    /// Nat` shape, checked structurally rather than assumed.
    #[test]
    fn eval_has_the_stated_type() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let eval_const = kernel.const_(p.eval, vec![]);
        let inferred = kernel.infer(eval_const).expect("must infer");

        let nat_ty = kernel.const_(p.heyting.nat.nat, vec![]);
        let formula_ty = kernel.const_(p.heyting.formula, vec![]);
        let anon = kernel.anon();
        let val_ty = kernel.pi(anon, nat_ty, nat_ty, BinderInfo::Default);
        let codomain = kernel.pi(anon, val_ty, nat_ty, BinderInfo::Default);
        let expected = kernel.pi(anon, formula_ty, codomain, BinderInfo::Default);

        assert!(
            kernel.def_eq(inferred, expected),
            "eval must have type Formula -> (Nat -> Nat) -> Nat"
        );
    }

    /// `eval Formula.bot v = 0` for an arbitrary valuation (here the
    /// identity `fun n => n`), independent of what `v` is — hand-computed:
    /// `bot` has no fields, so `m_bot`'s body `0` is returned unconditionally.
    #[test]
    fn eval_bot_is_always_zero() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let v = valuation_identity(&mut kernel, &p.heyting);
        let bot_f = bot(&mut kernel, &p.heyting);
        let applied = eval_app(&mut kernel, p.eval, bot_f, v);
        let expected = num(&mut kernel, &p.heyting, 0);
        assert!(kernel.def_eq(applied, expected), "eval(bot, v) must be 0");
    }

    /// `eval (Formula.var i) v = v i`, checked at TWO DIFFERENT valuations
    /// applied to the SAME formula `var 0` — this is what proves `eval`
    /// actually consumes its valuation argument rather than, say, always
    /// returning a fixed constant regardless of `v`:
    /// - `v := fun _ => 0`  =>  `eval (var 0) v = 0`.
    /// - `v := fun _ => 1`  =>  `eval (var 0) v = 1`.
    #[test]
    fn eval_var_applies_the_valuation() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let heyting = p.heyting;

        let var0 = var(&mut kernel, &heyting, 0);
        let v0 = valuation_const(&mut kernel, &heyting, 0);
        let applied0 = eval_app(&mut kernel, p.eval, var0, v0);
        let expected0 = num(&mut kernel, &heyting, 0);
        assert!(
            kernel.def_eq(applied0, expected0),
            "eval(var 0, const 0) must be 0"
        );

        let var0b = var(&mut kernel, &heyting, 0);
        let v1 = valuation_const(&mut kernel, &heyting, 1);
        let applied1 = eval_app(&mut kernel, p.eval, var0b, v1);
        let expected1 = num(&mut kernel, &heyting, 1);
        assert!(
            kernel.def_eq(applied1, expected1),
            "eval(var 0, const 1) must be 1"
        );
    }

    /// **Discriminating check.** At the valuation pair `(v(0), v(1)) =
    /// (0, 1)` (the identity valuation), `meet3(0,1) = 0`, `join3(0,1) = 1`,
    /// `himp3(0,1) = 2` (since `0 <= 1`) are ALL THREE DIFFERENT — so `eval`
    /// applied to `and_`, `or_`, `imp` of the same two subformulas must give
    /// three different answers, which fails loudly on a copy-paste error
    /// between the three connective minors rather than passing silently.
    /// Hand-computed against `ipc_heyting.rs`'s own definitions:
    /// - `eval (and_ (var 0) (var 1)) id = meet3 0 1 = 0`.
    /// - `eval (or_  (var 0) (var 1)) id = join3 0 1 = 1`.
    /// - `eval (imp  (var 0) (var 1)) id = himp3 0 1 = 2`.
    #[test]
    fn eval_and_or_imp_discriminate_at_the_same_arguments() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let heyting = p.heyting;

        let mk = |kernel: &mut Kernel| {
            let v0 = var(kernel, &heyting, 0);
            let v1 = var(kernel, &heyting, 1);
            (v0, v1)
        };

        let (a, b) = mk(&mut kernel);
        let v = valuation_identity(&mut kernel, &heyting);
        let and_f = and_(&mut kernel, &heyting, a, b);
        let and_val = eval_app(&mut kernel, p.eval, and_f, v);
        let expected_and = num(&mut kernel, &heyting, 0);
        assert!(
            kernel.def_eq(and_val, expected_and),
            "eval(and_(var0,var1), id) must be 0"
        );

        let (a, b) = mk(&mut kernel);
        let v = valuation_identity(&mut kernel, &heyting);
        let or_f = or_(&mut kernel, &heyting, a, b);
        let or_val = eval_app(&mut kernel, p.eval, or_f, v);
        let expected_or = num(&mut kernel, &heyting, 1);
        assert!(
            kernel.def_eq(or_val, expected_or),
            "eval(or_(var0,var1), id) must be 1"
        );

        let (a, b) = mk(&mut kernel);
        let v = valuation_identity(&mut kernel, &heyting);
        let imp_f = imp(&mut kernel, &heyting, a, b);
        let imp_val = eval_app(&mut kernel, p.eval, imp_f, v);
        let expected_imp = num(&mut kernel, &heyting, 2);
        assert!(
            kernel.def_eq(imp_val, expected_imp),
            "eval(imp(var0,var1), id) must be 2"
        );
    }

    /// **Nested formula.** `imp (var 0) (or_ (var 0) bot)` — "`p -> (p or
    /// bot)`", exercised at valuation `v := fun _ => 1` (so `p := var 0`
    /// evaluates to `1`, past the trivializing `0` the identity valuation
    /// would give at index `0`). Hand-computed:
    /// - `eval (or_ (var 0) bot) v = join3 1 0 = 1`.
    /// - `eval (imp (var 0) (or_ (var 0) bot)) v = himp3 1 1 = 2` (since
    ///   `1 <= 1`), i.e. this instance is IPC-valid (evaluates to top) —
    ///   which it should be, since `p -> (p or q)` is a theorem of
    ///   intuitionistic logic. This exercises the recursor past depth 1: the
    ///   right-hand `or_` subformula must itself be evaluated (recursively)
    ///   before `himp3` combines the two results.
    #[test]
    fn eval_handles_a_nested_formula() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let heyting = p.heyting;

        let v = valuation_const(&mut kernel, &heyting, 1);
        let p0 = var(&mut kernel, &heyting, 0);
        let bot_f = bot(&mut kernel, &heyting);
        let or_f = or_(&mut kernel, &heyting, p0, bot_f);
        let p0b = var(&mut kernel, &heyting, 0);
        let imp_f = imp(&mut kernel, &heyting, p0b, or_f);

        let applied = eval_app(&mut kernel, p.eval, imp_f, v);
        let expected = num(&mut kernel, &heyting, 2);
        assert!(
            kernel.def_eq(applied, expected),
            "eval(imp(var0, or_(var0,bot)), const 1) must be 2 (top)"
        );
    }

    /// **Cross-check against `ipc_heyting.rs`'s own proven countermodel.**
    /// `ipc_heyting_join_not_ne_top` is a kernel `Theorem` establishing
    /// `join3 1 (not3 1) != 2`, where `not3 1 = himp3 1 0 = 0`, so
    /// `join3 1 (not3 1) = join3 1 0 = 1`. `pem_instance` (from
    /// `ipc_heyting.rs`) is exactly `or_ (var 0) (imp (var 0) bot)`, i.e.
    /// `p or not p` with `not p` spelled `p -> bot`. At `v := fun _ => 1`
    /// this must evaluate through the GENERIC recursor to the SAME value
    /// `1` that the hand-built direct-`Nat` computation already established,
    /// tying the new `eval` path back to the existing result rather than
    /// introducing an independent, unchecked claim about the same formula.
    #[test]
    fn eval_of_pem_instance_matches_the_existing_countermodel_value() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let heyting = p.heyting;

        let pem = crate::pem_instance(&mut kernel, &heyting);
        let v = valuation_const(&mut kernel, &heyting, 1);
        let applied = eval_app(&mut kernel, p.eval, pem, v);
        let expected = num(&mut kernel, &heyting, 1);
        assert!(
            kernel.def_eq(applied, expected),
            "eval(pem_instance, const 1) must be 1, matching join3 1 (not3 1)"
        );
    }

    /// `Kernel::axiom_footprint` for `eval` is empty: it is a plain
    /// recursor application over `meet3`/`join3`/`himp3` and the `Nat`/
    /// `Formula` inductive gates, none of which is an `Axiom`, `Opaque`, or
    /// `Quotient` declaration.
    #[test]
    fn eval_is_axiom_free() {
        let mut kernel = Kernel::new();
        let p = build_ipc_eval_prelude(&mut kernel).expect("prelude must build");
        let footprint = kernel.axiom_footprint(p.eval);
        assert!(
            footprint.is_empty(),
            "expected an axiom-free footprint, found {footprint:?}"
        );
    }
}
