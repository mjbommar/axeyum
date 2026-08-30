//! **Scoping slice for `F:excluded-middle-not-intuitionistic`** — a
//! propositional-formula AST plus a 3-element Gödel/Łukasiewicz Heyting-chain
//! semantics, landed as the FIRST bounded slice toward that fact rather than
//! an attempt at the whole thing.
//!
//! ## What the fact actually asks for
//!
//! `F:excluded-middle-not-intuitionistic` states: *there is no derivation of
//! `p ∨ ¬p`, for a propositional variable `p`, in intuitionistic propositional
//! natural deduction.* That is a statement about the ABSENCE of a derivation
//! in a named formal proof system, so a machine-checked version of it needs,
//! at minimum:
//!
//! 1. an inductive type of IPC **formulas** (this file: [`Formula`]),
//! 2. an inductive **derivation relation** over formulas (natural-deduction
//!    rules: assumption, `∧I`/`∧E`, `∨I`/`∨E`, `→I`/`→E`, `⊥E`) — **not
//!    built here**,
//! 3. a **soundness theorem** (derivable ⟹ valid in every model of the
//!    semantics) — **not built here**,
//! 4. a **countermodel** in which `p ∨ ¬p` is not valid (this file: the
//!    3-element chain and [`declare_excluded_middle_countermodel`]).
//!
//! Soundness (2)+(3) is genuine research/engineering, comparable in size to
//! the natural-deduction developments elsewhere in this kernel (the logic
//! prelude's `not_not_em`/`dne_of_em`/`em_of_dne`/`peirce_of_em`/`em_of_peirce`
//! family in `prelude.rs` is the closest existing analogue — Prop-generic
//! equivalences *around* excluded middle, never an instance of it — and nothing
//! there is a derivation relation). Landing (1) and (4) now, and reporting the
//! honest gap for (2)/(3), is the "bounded slice" this repository's standing
//! rule asks for rather than declaring the whole fact done or deferring it.
//!
//! **What this file does NOT claim**: neither [`Formula`] nor
//! [`declare_excluded_middle_countermodel`] closes
//! `F:excluded-middle-not-intuitionistic`. That fact stays `open`, with a
//! decomposition into slices recorded in its `notes` field and in
//! `docs/plan/status/273-logic-excluded-middle.md`. What IS closed here is a
//! new, honestly-scoped, self-contained fact:
//! `F:heyting-3-chain-refutes-excluded-middle` — a semantic (not syntactic)
//! countermodel result, true and machine-checked on its own terms.
//!
//! ## The `Formula` AST
//!
//! Built via [`crate::Kernel::add_recursive_datatype_family`] — the same
//! generic mixed-carrier/self-referential-field combinator `string_prelude`'s
//! `Str` uses (`Str.rec`), and the exact template the `prelude_tests.rs`
//! `IntList` example exercises (`nil | cons (head : α) (tail : D)`). Here the
//! carrier is `Nat` (a variable INDEX) and every connective is a genuinely
//! recursive field:
//!
//! ```text
//! Formula.var : Nat -> Formula
//! Formula.bot : Formula
//! Formula.and_ : Formula -> Formula -> Formula
//! Formula.or_  : Formula -> Formula -> Formula
//! Formula.imp  : Formula -> Formula -> Formula
//! ```
//!
//! `Not p` is the standard IPC abbreviation `Imp p Bot`, so `p ∨ ¬p` for the
//! single variable `p := Var 0` is the closed term
//! `Or (Var 0) (Imp (Var 0) Bot)` (see [`pem_instance`]).
//!
//! ## The 3-element Gödel/Łukasiewicz chain `{0, 1, 2}`
//!
//! Represented directly as `Nat` values `0 < 1 < 2`, with `2` as the algebra's
//! top (`⊤`) and `0` as its bottom (`⊥`). The three Heyting operations are all
//! `Nat -> Nat -> Nat` definitions built from `Nat.ble` via a `Bool.rec`
//! selector (the same construction `nat_prelude/ops.rs`'s private
//! `bool_select_nat` uses — duplicated here in miniature rather than reused,
//! since that helper is `pub(super)` to `nat_prelude` and this file is
//! deliberately outside it):
//!
//! - `meet3 a b := if a.ble b then a else b`   (linear order meet = min)
//! - `join3 a b := if a.ble b then b else a`   (linear order join = max)
//! - `himp3 a b := if a.ble b then 2 else b`   (Gödel/relative-pseudocomplement
//!   implication: `a → b` is `⊤` exactly when `a ≤ b`, and `b` otherwise —
//!   the standard implication on a totally-ordered Heyting algebra)
//! - `not3 a := himp3 a 0`
//!
//! This is a genuine Heyting algebra (it is a finite distributive lattice with
//! relative pseudocomplements, since it is linearly ordered), so it is a sound
//! model of IPC — every IPC-derivable formula evaluates to `2` under every
//! valuation. It is NOT a model of classical logic: `join3 1 (not3 1) = 1 ≠ 2`,
//! computed below, is the required countermodel. (The classical/Boolean
//! 2-element algebra `{0, 1}` would NOT separate the two logics — `p ∨ ¬p`
//! is trivially valid there, which is exactly why the brief calls for a
//! 3-valued/Kripke-style structure rather than the simpler 2-valued one.)
//!
//! ## The countermodel theorem
//!
//! [`build_ipc_heyting_prelude`] declares
//! `ipc_heyting_join_not_ne_top : Not (Eq Nat (join3 1 (not3 1)) 2)` as a
//! kernel `Theorem`, proved from `Nat.ne_of_beq_eq_false` applied to
//! `Eq.refl : Eq Bool (Nat.beq 1 2) Bool.false` — i.e. the kernel itself
//! reduces `Nat.beq 1 2` to `Bool.false` by ι-computation, and the stated
//! type is accepted only because `join3 1 (not3 1)` is definitionally `1`
//! (checked by the SAME reduction machinery, not asserted). See
//! [`declare_excluded_middle_countermodel`] and the module tests for the
//! evaluation table this rests on.
//!
//! ## Non-vacuity: the algebra is not degenerate
//!
//! A single failing instance is not enough to trust — an algebra where
//! EVERYTHING fails to reach top would be a broken construction, not a
//! countermodel. `ipc_heyting_meet_not_countermodel_ne_top` in the test module
//! checks the SAME-KIND positive control: `not3 (meet3 1 (not3 1))` (i.e.
//! `¬(p ∧ ¬p)`, the law of non-contradiction at the same valuation `p := 1`)
//! DOES evaluate to `2`, top. So this algebra rejects exactly the classically-
//! but-not-intuitionistically-valid instance and accepts a genuinely
//! IPC-valid one at the same valuation, which is the discriminating behaviour
//! a real Heyting countermodel is supposed to have.
//!
//! ## Next slices (not attempted here)
//!
//! 1. A `Provable : Formula -> Prop` (or context-indexed `Deriv`) inductive
//!    family encoding IPC natural deduction's rules.
//! 2. A generic `eval : Formula -> (Nat -> Nat) -> Nat` via `Formula.rec`
//!    (this file only evaluates the ONE closed instance `pem_instance`
//!    directly in `Nat`, without going through the recursor at all — cheaper,
//!    but it does not generalize to arbitrary formulas).
//! 3. Soundness: `Provable f -> forall rho, eval f rho = 2` by induction on
//!    the derivation (the real mathematical content still missing).
//! 4. Combine 1–3 with this file's countermodel to conclude
//!    `Not (Provable pem_instance)`, closing
//!    `F:excluded-middle-not-intuitionistic` in the same style as
//!    `CReal.evt_attained_max_decides_sign` / `CReal.ivt_exact_root_decides_sign`
//!    (ADR-0603 row 2).

use crate::{
    BinderInfo, Declaration, ExprId, KernelError, LevelId, NameId, RecField,
    RecursiveDatatypeFamily, ReducibilityHint, build_nat_prelude,
};

/// Names produced by [`build_ipc_heyting_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IpcHeytingPrelude {
    /// The embedded `Nat` prelude (and, through it, the logic prelude).
    pub nat: NatPreludeHandle,
    /// `Formula : Type`.
    pub formula: NameId,
    /// `Formula.var : Nat -> Formula`.
    pub var: NameId,
    /// `Formula.bot : Formula`.
    pub bot: NameId,
    /// `Formula.and_ : Formula -> Formula -> Formula`.
    pub and_: NameId,
    /// `Formula.or_ : Formula -> Formula -> Formula`.
    pub or_: NameId,
    /// `Formula.imp : Formula -> Formula -> Formula`.
    pub imp: NameId,
    /// `Formula.rec`, the generated ι-computing recursor.
    pub formula_rec: NameId,
    /// `meet3 : Nat -> Nat -> Nat`, the chain's Heyting meet (`min`).
    pub meet3: NameId,
    /// `join3 : Nat -> Nat -> Nat`, the chain's Heyting join (`max`).
    pub join3: NameId,
    /// `himp3 : Nat -> Nat -> Nat`, the chain's Heyting implication.
    pub himp3: NameId,
    /// `not3 : Nat -> Nat`, `fun a => himp3 a 0`.
    pub not3: NameId,
    /// `ipc_heyting_join_not_ne_top : Not (Eq Nat (join3 1 (not3 1)) 2)`.
    pub join_not_ne_top: NameId,
}

/// A thin, `Copy`-able handle onto the [`crate::NatPrelude`] names this file needs,
/// so [`IpcHeytingPrelude`] does not have to embed the (large, non-`Copy`)
/// [`crate::NatPrelude`] by value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatPreludeHandle {
    /// `Nat : Type`.
    pub nat: NameId,
    /// `Nat.zero : Nat`.
    pub zero: NameId,
    /// `Nat.succ : Nat -> Nat`.
    pub succ: NameId,
    /// `Nat.ble : Nat -> Nat -> Bool`.
    pub ble: NameId,
    /// `Nat.ne_of_beq_eq_false`.
    pub ne_of_beq_eq_false: NameId,
    /// `Nat.beq : Nat -> Nat -> Bool`.
    pub beq: NameId,
    /// `Eq`, from the embedded logic prelude.
    pub eq: NameId,
    /// `Not`, from the embedded logic prelude.
    pub not: NameId,
    /// `Bool`, from the embedded logic prelude.
    pub bool_: NameId,
    /// `Bool.rec`, from the embedded logic prelude.
    pub bool_rec: NameId,
    /// `Bool.false`, from the embedded logic prelude.
    pub bool_false: NameId,
}

/// Build the `Formula` AST and the 3-element Heyting-chain semantics,
/// registering every declaration through the trusted
/// [`crate::Kernel::add_inductive`] / [`crate::Kernel::add_declaration`]
/// gates. Not cached (unlike the large shared preludes): this package is
/// small and cheap to rebuild per call.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_ipc_heyting_prelude(
    kernel: &mut crate::Kernel,
) -> Result<IpcHeytingPrelude, KernelError> {
    let nat_prelude = build_nat_prelude(kernel)?;
    let nat = NatPreludeHandle {
        nat: nat_prelude.nat,
        zero: nat_prelude.zero,
        succ: nat_prelude.succ,
        ble: nat_prelude.ble,
        ne_of_beq_eq_false: nat_prelude.ne_of_beq_eq_false,
        beq: nat_prelude.beq,
        eq: nat_prelude.logic.eq,
        not: nat_prelude.logic.not,
        bool_: nat_prelude.logic.bool_,
        bool_rec: nat_prelude.logic.bool_rec,
        bool_false: nat_prelude.logic.bool_false,
    };

    let anon = kernel.anon();
    let zero_lvl = kernel.level_zero();
    let one = kernel.level_succ(zero_lvl);

    // --- Formula : Type, the recursive datatype family -----------------------
    let formula = kernel.name_str(anon, "Formula");
    let var = kernel.name_str(formula, "var");
    let bot = kernel.name_str(formula, "bot");
    let and_ = kernel.name_str(formula, "and_");
    let or_ = kernel.name_str(formula, "or_");
    let imp = kernel.name_str(formula, "imp");
    let nat_const = kernel.const_(nat.nat, vec![]);
    let family: RecursiveDatatypeFamily = kernel.add_recursive_datatype_family(
        formula,
        nat_const,
        one,
        &[
            (var, vec![RecField::Carrier]),
            (bot, vec![]),
            (and_, vec![RecField::Recursive, RecField::Recursive]),
            (or_, vec![RecField::Recursive, RecField::Recursive]),
            (imp, vec![RecField::Recursive, RecField::Recursive]),
        ],
    )?;
    let formula_rec = family.rec;

    // --- The 3-element Gödel/Łukasiewicz chain, as Nat -> Nat -> Nat ---------
    let meet3_name = kernel.name_str(anon, "meet3");
    declare_chain_binop(kernel, &nat, meet3_name, ChainOp::Meet)?;

    let join3_name = kernel.name_str(anon, "join3");
    declare_chain_binop(kernel, &nat, join3_name, ChainOp::Join)?;

    let himp3_name = kernel.name_str(anon, "himp3");
    declare_chain_binop(kernel, &nat, himp3_name, ChainOp::Himp)?;

    let not3_name = kernel.name_str(anon, "not3");
    declare_not3(kernel, &nat, not3_name, himp3_name)?;

    let join_not_ne_top =
        declare_excluded_middle_countermodel(kernel, &nat, join3_name, not3_name)?;

    Ok(IpcHeytingPrelude {
        nat,
        formula,
        var,
        bot,
        and_,
        or_,
        imp,
        formula_rec,
        meet3: meet3_name,
        join3: join3_name,
        himp3: himp3_name,
        not3: not3_name,
        join_not_ne_top,
    })
}

/// `Formula.or_ (Formula.var 0) (Formula.imp (Formula.var 0) Formula.bot)` —
/// the closed AST term for "`p ∨ ¬p`" at a single variable `p := Var 0`, with
/// `¬p` spelled out as IPC's standard `p → ⊥` abbreviation. Built purely for
/// its own well-typedness check (see the module tests); this file's actual
/// countermodel computation works directly in `Nat` and does not evaluate
/// this term (that needs the generic recursor-based `eval` named as a next
/// slice in the module docs).
pub fn pem_instance(kernel: &mut crate::Kernel, p: &IpcHeytingPrelude) -> ExprId {
    let zero_nat = kernel.const_(p.nat.zero, vec![]);
    let var_const = kernel.const_(p.var, vec![]);
    let var0 = kernel.app(var_const, zero_nat);
    let bot_const = kernel.const_(p.bot, vec![]);
    let imp_const = kernel.const_(p.imp, vec![]);
    let not_var0 = apply_all(kernel, imp_const, &[var0, bot_const]);
    let or_const = kernel.const_(p.or_, vec![]);
    apply_all(kernel, or_const, &[var0, not_var0])
}

/// Which of the chain's three Heyting operations [`declare_chain_binop`]
/// should build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChainOp {
    /// `min`.
    Meet,
    /// `max`.
    Join,
    /// The Gödel/relative-pseudocomplement implication.
    Himp,
}

fn apply_all(kernel: &mut crate::Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

fn lam_fvar(kernel: &mut crate::Kernel, fvar: u64, ty: ExprId, body: ExprId) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.lam(anon, ty, body, BinderInfo::Default)
}

/// Build `Nat.ble a b`.
fn ble(kernel: &mut crate::Kernel, nat: &NatPreludeHandle, a: ExprId, b: ExprId) -> ExprId {
    let ble_const = kernel.const_(nat.ble, vec![]);
    apply_all(kernel, ble_const, &[a, b])
}

/// `Bool.rec.{1} (motive := fun _ => Nat) on_false on_true condition` — the
/// computational `if condition then on_true else on_false : Nat` selector,
/// matching `nat_prelude/ops.rs`'s private `bool_select_nat` construction.
fn select_nat(
    kernel: &mut crate::Kernel,
    nat: &NatPreludeHandle,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let bool_ty = kernel.const_(nat.bool_, vec![]);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, bool_ty, nat_ty, BinderInfo::Default);
    let zero_lvl = kernel.level_zero();
    let one = kernel.level_succ(zero_lvl);
    let bool_rec_const = kernel.const_(nat.bool_rec, vec![one]);
    apply_all(
        kernel,
        bool_rec_const,
        &[motive, on_false, on_true, condition],
    )
}

/// The unary numeral `succ^n zero`. Kept to tiny `n` (this file only ever
/// needs `0`, `1`, `2`) — see the workspace-wide gotcha about unary `Nat`
/// magnitudes blowing up kernel reduction budgets at large `n`.
fn num(kernel: &mut crate::Kernel, nat: &NatPreludeHandle, n: u32) -> ExprId {
    let mut e = kernel.const_(nat.zero, vec![]);
    let succ = kernel.const_(nat.succ, vec![]);
    for _ in 0..n {
        e = kernel.app(succ, e);
    }
    e
}

/// Declare one of `meet3` / `join3` / `himp3` : `Nat -> Nat -> Nat` as
/// `fun a b => select_nat(a.ble b, on_true, on_false)`, where `(on_true,
/// on_false)` depends on `op`:
///
/// - `Meet`: `(a, b)` — `min a b`.
/// - `Join`: `(b, a)` — `max a b`.
/// - `Himp`: `(2, b)` — the Gödel implication `a → b`.
fn declare_chain_binop(
    kernel: &mut crate::Kernel,
    nat: &NatPreludeHandle,
    fn_name: NameId,
    op: ChainOp,
) -> Result<(), KernelError> {
    let anon = kernel.anon();
    let nat_ty = kernel.const_(nat.nat, vec![]);

    let a_id = 910_101_u64;
    let b_id = 910_102_u64;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let cond = ble(kernel, nat, a, b);

    let (on_true, on_false) = match op {
        ChainOp::Meet => (a, b),
        ChainOp::Join => (b, a),
        ChainOp::Himp => {
            let top = num(kernel, nat, 2);
            (top, b)
        }
    };

    let value_body = select_nat(kernel, nat, cond, on_true, on_false);
    let value = lam_fvar(kernel, b_id, nat_ty, value_body);
    let value = lam_fvar(kernel, a_id, nat_ty, value);

    let ty = {
        let inner = kernel.pi(anon, nat_ty, nat_ty, BinderInfo::Default);
        kernel.pi(anon, nat_ty, inner, BinderInfo::Default)
    };

    kernel.add_declaration(Declaration::Definition {
        name: fn_name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })
}

/// Declare `not3 : Nat -> Nat := fun a => himp3 a 0`.
fn declare_not3(
    kernel: &mut crate::Kernel,
    nat: &NatPreludeHandle,
    not3_name: NameId,
    himp3_name: NameId,
) -> Result<(), KernelError> {
    let anon = kernel.anon();
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let a_id = 910_201_u64;
    let a = kernel.fvar(a_id);
    let himp3_const = kernel.const_(himp3_name, vec![]);
    let zero = kernel.const_(nat.zero, vec![]);
    let body = apply_all(kernel, himp3_const, &[a, zero]);
    let value = lam_fvar(kernel, a_id, nat_ty, body);
    let ty = kernel.pi(anon, nat_ty, nat_ty, BinderInfo::Default);
    kernel.add_declaration(Declaration::Definition {
        name: not3_name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })
}

/// `Eq.{u} alpha x y`.
fn eq_app(
    kernel: &mut crate::Kernel,
    eq: NameId,
    u_lvl: LevelId,
    alpha: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let e = kernel.const_(eq, vec![u_lvl]);
    apply_all(kernel, e, &[alpha, x, y])
}

/// Declare `ipc_heyting_join_not_ne_top : Not (Eq Nat (join3 1 (not3 1)) 2)`,
/// the countermodel theorem: at the valuation `p := 1` in the 3-element
/// chain, `p ∨ ¬p` (`join3 1 (not3 1)`) is definitionally `1`, and `1 != 2`
/// (`2` being the chain's top / true), so `p ∨ ¬p` is NOT valid in this
/// Heyting algebra.
///
/// Proved via `Nat.ne_of_beq_eq_false 1 2 h`, where `h : Eq Bool (Nat.beq 1 2)
/// Bool.false` is closed by `Eq.refl` alone — `Nat.beq 1 2` ι-reduces to
/// `Bool.false` at these tiny concrete numerals, so the kernel's own
/// defeq-check discharges `h`. The SAME proof term is then accepted at the
/// stronger stated type `Not (Eq Nat (join3 1 (not3 1)) 2)` only because
/// `join3 1 (not3 1)` is ALSO definitionally `1` — i.e. admission of this
/// declaration is itself the kernel-checked confirmation that the chain
/// computes the value this file claims it does, not merely evidence that `1
/// != 2`.
fn declare_excluded_middle_countermodel(
    kernel: &mut crate::Kernel,
    nat: &NatPreludeHandle,
    join3_name: NameId,
    not3_name: NameId,
) -> Result<NameId, KernelError> {
    let anon = kernel.anon();
    let one_nat = num(kernel, nat, 1);
    let two_nat = num(kernel, nat, 2);

    let not3_const = kernel.const_(not3_name, vec![]);
    let not3_one = kernel.app(not3_const, one_nat);
    let join3_const = kernel.const_(join3_name, vec![]);
    let lhs = apply_all(kernel, join3_const, &[one_nat, not3_one]);

    let nat_ty = kernel.const_(nat.nat, vec![]);
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    // `Nat`/`Bool` both live at `Sort 1` (`Type`), not `Sort 0` (`Prop`), so
    // `Eq`'s universe parameter here must be `one_lvl`. Using `zero_lvl` is
    // exactly the "expected a low-numbered ExprId (a Sort), got a Sort at the
    // wrong level" TypeMismatch this workspace's gotchas warn about.
    let eq_lhs_two = eq_app(kernel, nat.eq, one_lvl, nat_ty, lhs, two_nat);
    let logical_not_const = kernel.const_(nat.not, vec![]);
    let stated_ty = kernel.app(logical_not_const, eq_lhs_two);

    // Proof: Nat.ne_of_beq_eq_false one two (Eq.refl Bool (Nat.beq one two)).
    let bool_ty = kernel.const_(nat.bool_, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let beq_one_two = apply_all(kernel, beq_const, &[one_nat, two_nat]);
    // Eq.refl : Pi (a : Sort u) (x : a), Eq a x x -- here at Bool (Sort 1).
    // `name_str` interns hierarchically, so this re-finds the SAME `Eq.refl`
    // name the logic prelude already declared under `nat.eq` -- no separate
    // "parent of a name" lookup exists or is needed.
    let eq_refl_name = kernel.name_str(nat.eq, "refl");
    let eq_refl_const = kernel.const_(eq_refl_name, vec![one_lvl]);
    let refl_proof = apply_all(kernel, eq_refl_const, &[bool_ty, beq_one_two]);

    let ne_const = kernel.const_(nat.ne_of_beq_eq_false, vec![]);
    let value = apply_all(kernel, ne_const, &[one_nat, two_nat, refl_proof]);

    let name = kernel.name_str(anon, "ipc_heyting_join_not_ne_top");
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

    /// The prelude builds at all, and the recursive `Formula` family admits.
    #[test]
    fn ipc_heyting_prelude_builds() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");
        // `Formula.rec` must exist as a genuine declaration.
        assert!(kernel.environment().get(p.formula_rec).is_some());
    }

    /// `pem_instance` — the closed AST term for `p ∨ ¬p` — type-checks as
    /// `Formula`, confirming the connectives compose the way the module docs
    /// claim, independent of any evaluation.
    #[test]
    fn pem_instance_type_checks_as_formula() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");
        let term = pem_instance(&mut kernel, &p);
        let ty = kernel.infer(term).expect("must infer");
        let formula_const = kernel.const_(p.formula, vec![]);
        assert!(
            kernel.def_eq(ty, formula_const),
            "pem_instance must have type Formula"
        );
    }

    /// Evaluation table for `meet3`/`join3`/`himp3`/`not3` at small,
    /// DISCRIMINATING concrete arguments (never a single symmetric pair,
    /// which the `land`/`lor` gotcha in this workspace warns can pass
    /// vacuously). Every value is independently hand-computed against the
    /// module docs' definitions of the 3-element chain.
    #[test]
    fn chain_operations_compute_the_intended_values() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");
        let nat = &p.nat;

        let check_binop = |kernel: &mut Kernel, f: NameId, a: u32, b: u32, expected: u32| {
            let a_e = num(kernel, nat, a);
            let b_e = num(kernel, nat, b);
            let f_c = kernel.const_(f, vec![]);
            let applied = apply_all(kernel, f_c, &[a_e, b_e]);
            let expected_e = num(kernel, nat, expected);
            assert!(
                kernel.def_eq(applied, expected_e),
                "expected value {expected} at ({a}, {b})"
            );
        };

        // meet3 = min.
        check_binop(&mut kernel, p.meet3, 0, 0, 0);
        check_binop(&mut kernel, p.meet3, 1, 0, 0);
        check_binop(&mut kernel, p.meet3, 0, 1, 0);
        check_binop(&mut kernel, p.meet3, 1, 2, 1);
        check_binop(&mut kernel, p.meet3, 2, 1, 1);

        // join3 = max.
        check_binop(&mut kernel, p.join3, 0, 0, 0);
        check_binop(&mut kernel, p.join3, 1, 0, 1);
        check_binop(&mut kernel, p.join3, 0, 1, 1);
        check_binop(&mut kernel, p.join3, 1, 2, 2);
        check_binop(&mut kernel, p.join3, 2, 1, 2);

        // himp3 = Gödel implication (top when a <= b, else b).
        check_binop(&mut kernel, p.himp3, 0, 0, 2);
        check_binop(&mut kernel, p.himp3, 0, 1, 2);
        check_binop(&mut kernel, p.himp3, 1, 0, 0);
        check_binop(&mut kernel, p.himp3, 1, 1, 2);
        check_binop(&mut kernel, p.himp3, 2, 1, 1);
        check_binop(&mut kernel, p.himp3, 1, 2, 2);

        // not3 a := himp3 a 0.
        let check_not = |kernel: &mut Kernel, a: u32, expected: u32| {
            let a_e = num(kernel, nat, a);
            let not3_c = kernel.const_(p.not3, vec![]);
            let applied = kernel.app(not3_c, a_e);
            let expected_e = num(kernel, nat, expected);
            assert!(
                kernel.def_eq(applied, expected_e),
                "not3({a}) must be {expected}"
            );
        };
        check_not(&mut kernel, 0, 2);
        check_not(&mut kernel, 1, 0);
        check_not(&mut kernel, 2, 0);
    }

    /// The countermodel theorem admits through the trusted gate at all.
    #[test]
    fn excluded_middle_countermodel_theorem_admits() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");
        assert!(kernel.environment().get(p.join_not_ne_top).is_some());
    }

    /// `Kernel::axiom_footprint` (this kernel's `#print axioms`) for the
    /// countermodel theorem is empty: the proof rests on `Nat.ne_of_beq_eq_false`,
    /// `Eq.refl`, and the `Nat`/`Bool`/`Formula` inductive gates, none of which
    /// is an `Axiom`, `Opaque`, or `Quotient` declaration. Backs
    /// `F:heyting-3-chain-refutes-excluded-middle`'s `axiom_footprint: []`.
    #[test]
    fn excluded_middle_countermodel_theorem_is_axiom_free() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");
        let footprint = kernel.axiom_footprint(p.join_not_ne_top);
        assert!(
            footprint.is_empty(),
            "expected an axiom-free footprint, found {footprint:?}"
        );
    }

    /// **Non-vacuity / positive control.** `¬(p ∧ ¬p)` (the law of
    /// non-contradiction), at the SAME valuation `p := 1` the countermodel
    /// uses, DOES evaluate to top (`2`). This is the same-kind discriminating
    /// check this workspace's standing rule asks for: a Heyting algebra that
    /// refuted EVERY instance at this valuation would not be a countermodel,
    /// it would be broken. `not3 (meet3 1 (not3 1)) = not3 0 = 2`.
    #[test]
    fn non_contradiction_holds_at_the_same_valuation_that_refutes_excluded_middle() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");
        let nat = &p.nat;

        let one_e = num(&mut kernel, nat, 1);
        let not3_c = kernel.const_(p.not3, vec![]);
        let not3_one = kernel.app(not3_c, one_e);
        let meet3_c = kernel.const_(p.meet3, vec![]);
        let one_e2 = num(&mut kernel, nat, 1);
        let meet_val = apply_all(&mut kernel, meet3_c, &[one_e2, not3_one]);
        let not3_c2 = kernel.const_(p.not3, vec![]);
        let full = kernel.app(not3_c2, meet_val);
        let top = num(&mut kernel, nat, 2);
        assert!(
            kernel.def_eq(full, top),
            "not(p and not p) must evaluate to top at p := 1"
        );
    }

    /// Sanity check on the SCOPING claim this module's docs make: as of this
    /// lane, no declaration in this kernel's environment names a derivation
    /// relation or a proof-system object for propositional logic. Grepped by
    /// name substring against every declaration in the environment, paired
    /// with a positive control of the SAME lookup kind (`Formula` itself,
    /// which this file just declared) so an always-empty search cannot pass
    /// vacuously.
    #[test]
    fn no_prior_derivation_relation_exists_before_this_file() {
        let mut kernel = Kernel::new();
        let p = build_ipc_heyting_prelude(&mut kernel).expect("prelude must build");

        let names: Vec<String> = kernel
            .environment()
            .iter()
            .map(|(name, _)| kernel.display_name(*name).to_string())
            .collect();

        // Positive control: Formula itself, just declared, must be findable
        // by this exact lookup method.
        let formula_str = kernel.display_name(p.formula).to_string();
        assert!(
            names.iter().any(|n| n == &formula_str),
            "positive control failed: Formula itself was not found by name"
        );

        // The actual scoping claim: no "Provable"/"Derivation"/"Deriv" name
        // exists anywhere in the environment (this file adds none).
        for forbidden in ["Provable", "Derivation", ".Deriv"] {
            assert!(
                !names.iter().any(|n| n.contains(forbidden)),
                "found an unexpected `{forbidden}` declaration: derivation-relation \
                 infrastructure may already exist and the scoping note is stale"
            );
        }
    }
}
