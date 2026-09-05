//! **Slice 1 of the first-order model theory group** (`fo_*.rs`, ADR-1636):
//! the *syntax* of a single-sorted first-order language — `FO.Term`,
//! `FO.Formula`, parallel substitution on both, and the de Bruijn plumbing
//! (`shift`, `cons`, `lift`) the binder cases need.
//!
//! This group follows the `ipc_*.rs` pattern verbatim — syntax as an
//! inductive, semantics as a recursor application, soundness by induction on
//! derivations, everything axiom-free — and lifts it from propositional to
//! first-order logic. The three later slices are `fo_semantics.rs`
//! (structures, `Term.eval`, Tarski `sat`, the ℕ model),
//! `fo_substitution.rs` (the coincidence and substitution lemmas) and
//! `fo_provable.rs` / `fo_soundness.rs` (natural deduction and its soundness).
//!
//! ## Variables are de Bruijn indices
//!
//! `FO.Term.var : Nat -> Term` is a de Bruijn **index**, not a name. Two
//! reasons, both about what the later slices would otherwise have to pay for:
//!
//! - **α-equivalence disappears.** With names, `all` would bind a `Nat`, two
//!   syntactically different formulas could denote the same thing, and every
//!   theorem below would have to be stated modulo an α-relation that itself
//!   needs an inductive definition and a congruence proof. With indices,
//!   syntactic identity *is* α-equivalence, and `Eq FO.Formula` is the right
//!   notion throughout.
//! - **The eigenvariable condition becomes a shift.** `∀`-introduction's side
//!   condition — "the variable being generalized is not free in the context"
//!   — is, in de Bruijn form, the statement that the context was *shifted*
//!   before the premise was derived, so index `0` cannot occur in it. That is
//!   a syntactic operation this file already has to build (`FO.Term.shift`),
//!   rather than a `notFreeIn : Nat -> Formula -> Prop` relation plus a
//!   decidable occurs-check, which is what the named presentation would owe.
//!   See `fo_provable.rs` for the rule as landed.
//!
//! ## Signature shape: arities 0, 1, 2, given as `Nat`-indexed families
//!
//! ```text
//! FO.Term.var : Nat -> Term                              -- de Bruijn index
//! FO.Term.f0  : Nat -> Term                              -- constant symbol #k
//! FO.Term.f1  : Nat -> Term -> Term                      -- unary function symbol #k
//! FO.Term.f2  : Nat -> Term -> Term -> Term              -- binary function symbol #k
//! ```
//!
//! The textbook presentation is `Term.app : (f : Sym) -> Vector Term (arity f)
//! -> Term`, or the equivalent `Term.app : Nat -> List Term -> Term`. Both are
//! **nested** inductives (`List`/`Vector` applied to the type being defined),
//! and every function and lemma over them — substitution, evaluation, and the
//! substitution lemma — then needs a simultaneous induction over `Term` and
//! over lists of `Term`s. This kernel's `add_mutual_inductive` would have to
//! carry that nested positivity *and* the generated mutual recursor, and each
//! of the four inductions below would double.
//!
//! Arities `0, 1, 2` are a strict, honest restriction on the *signature*, not
//! on the logic: the language still has genuinely `Nat`-indexed infinite
//! families of symbols at each arity, and ℕ with `0`, `succ`, `+`, `<` — the
//! concrete structure `fo_semantics.rs` builds — needs exactly arities
//! `0, 1, 2` and relation arities `1, 2`. Every definition and every lemma
//! below treats the three function families uniformly, so extending to arity
//! `n` is mechanical (one more constructor, one more minor premise per
//! recursion) rather than conceptual.
//!
//! ## Formulas
//!
//! ```text
//! FO.Formula.bot  : Formula                              -- ⊥
//! FO.Formula.eqf  : Term -> Term -> Formula               -- t₁ = t₂
//! FO.Formula.rel1 : Nat -> Term -> Formula                -- R¹ₖ(t)
//! FO.Formula.rel2 : Nat -> Term -> Term -> Formula        -- R²ₖ(t₁, t₂)
//! FO.Formula.and_ : Formula -> Formula -> Formula
//! FO.Formula.or_  : Formula -> Formula -> Formula
//! FO.Formula.imp  : Formula -> Formula -> Formula
//! FO.Formula.all  : Formula -> Formula                    -- ∀ (binds index 0)
//! FO.Formula.ex   : Formula -> Formula                    -- ∃ (binds index 0)
//! ```
//!
//! Equality is a *logical* symbol (its own constructor), not a distinguished
//! binary relation symbol, which is what lets `fo_semantics.rs` interpret it
//! as the kernel's own `Eq` rather than as one more component of a structure.
//! `Not φ` is the usual abbreviation `imp φ bot`; there is no separate
//! constructor for it, so nothing below has to keep two negation cases in
//! step. `all` and `ex` take **one** `Formula` field and bind index `0` in
//! it — no binder name, no variable field, because there is nothing to name.
//!
//! ## Substitution is parallel, and it is a function `Nat -> Term`
//!
//! ```text
//! FO.Term.subst    : Term -> (Nat -> Term) -> Term
//! FO.Formula.subst : Formula -> (Nat -> Term) -> Formula
//! ```
//!
//! A substitution is a total function from indices to terms. This is
//! deliberate, and it is *cheaper* than single-variable substitution, not more
//! expensive: the substitution lemma for a parallel substitution is a single
//! induction whose `∀`/`∃` cases compose two substitutions, whereas the
//! single-variable version needs an auxiliary "substitution commutes with
//! shifting" lemma before it can even be stated at the binder. The four
//! operations the binder cases need are
//!
//! ```text
//! FO.Subst.id    : Nat -> Term                   := fun n => var n
//! FO.Subst.shift : Nat -> Term                   := fun n => var (succ n)
//! FO.Subst.cons  : Term -> (Nat -> Term) -> Nat -> Term
//!                                                := fun t s n => Nat.rec t (fun k _ => s k) n
//! FO.Subst.lift  : (Nat -> Term) -> Nat -> Term  := fun s => cons (var 0) (fun n => shiftTerm (s n))
//! ```
//!
//! `FO.Subst.cons t s` is written `t · s` in the literature; it is what makes
//! `∀`-elimination's instance `φ[t]` expressible as
//! `Formula.subst φ (Subst.cons t Subst.id)`. `Subst.lift` is what
//! `Formula.subst` uses when it descends under `all`/`ex`: index `0` stays put
//! and everything the old substitution produced is shifted out of the new
//! binder's way.
//!
//! `Subst.cons` goes through `Nat.rec` rather than a `Bool`-valued test on the
//! index precisely so that `Subst.cons t s Nat.zero` and
//! `Subst.cons t s (Nat.succ k)` ι-reduce to `t` and `s k`. That reduction is
//! load-bearing three slices later: it is why `fo_substitution.rs`'s `∀` case
//! discharges its index-`0` obligation by `Eq.refl` instead of by a lemma.
//!
//! ## These are `Definition`s, so admission proves nothing about them
//!
//! `Kernel::add_declaration` type-checks; a substitution that dropped its
//! argument would type-check exactly as readily. The module tests below pin
//! every one of them by **evaluation at concrete, discriminating arguments**,
//! including the two that a copy-paste error between the three function-symbol
//! families or between `all` and `ex` would survive:
//! `subst` must reach *under* a binder with the lifted substitution, and it
//! must leave index `0` alone there while shifting everything else.

// The mathematical variables in this group are the ones the literature uses --
// `M`/`S` for a structure, `w`/`v` for a valuation, `s` for a substitution,
// `t` for a term, `p`/`q` for formulas, `g` for a context, `n`/`k` for de
// Bruijn indices. Renaming them to satisfy `many_single_char_names` /
// `similar_names` would make every proof term harder to check against the
// semantics it encodes, which is the only thing that matters here. Same
// judgement, same wording, as `ipc_soundness.rs`.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
// `LogicPrelude` is a 444-byte `Copy` struct of `NameId`s and is threaded by
// value through every combinator, exactly as `NatOps::prelude()` hands it out
// everywhere else in this crate. Taking it by reference here would be a
// different convention from the rest of the kernel for no measured gain.
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::{BinderInfo, Declaration, ExprId, KernelError, LevelId, NameId, RecField};
use crate::{NatPrelude, ReducibilityHint, build_nat_prelude};

/// Names produced by [`build_fo_syntax_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoSyntaxPrelude {
    /// The embedded `Nat` prelude (and, through it, the logic prelude).
    pub nat: NatPrelude,

    // --- FO.Term -------------------------------------------------------------
    /// `FO.Term : Type`.
    pub term: NameId,
    /// `FO.Term.var : Nat -> Term` — a de Bruijn index.
    pub var: NameId,
    /// `FO.Term.f0 : Nat -> Term` — the constant symbol of index `k`.
    pub f0: NameId,
    /// `FO.Term.f1 : Nat -> Term -> Term` — the unary function symbol `k`.
    pub f1: NameId,
    /// `FO.Term.f2 : Nat -> Term -> Term -> Term` — the binary function symbol `k`.
    pub f2: NameId,
    /// `FO.Term.rec`, the generated ι-computing recursor.
    pub term_rec: NameId,

    // --- FO.Formula ----------------------------------------------------------
    /// `FO.Formula : Type`.
    pub formula: NameId,
    /// `FO.Formula.bot : Formula`.
    pub bot: NameId,
    /// `FO.Formula.eqf : Term -> Term -> Formula`.
    pub eqf: NameId,
    /// `FO.Formula.rel1 : Nat -> Term -> Formula`.
    pub rel1: NameId,
    /// `FO.Formula.rel2 : Nat -> Term -> Term -> Formula`.
    pub rel2: NameId,
    /// `FO.Formula.and_ : Formula -> Formula -> Formula`.
    pub and_: NameId,
    /// `FO.Formula.or_ : Formula -> Formula -> Formula`.
    pub or_: NameId,
    /// `FO.Formula.imp : Formula -> Formula -> Formula`.
    pub imp: NameId,
    /// `FO.Formula.all : Formula -> Formula` (binds de Bruijn index `0`).
    pub all: NameId,
    /// `FO.Formula.ex : Formula -> Formula` (binds de Bruijn index `0`).
    pub ex: NameId,
    /// `FO.Formula.rec`, the generated ι-computing recursor.
    pub formula_rec: NameId,

    // --- substitution --------------------------------------------------------
    /// `FO.Term.subst : Term -> (Nat -> Term) -> Term`.
    pub term_subst: NameId,
    /// `FO.Subst.id : Nat -> Term := fun n => var n`.
    pub subst_id: NameId,
    /// `FO.Subst.shift : Nat -> Term := fun n => var (succ n)`.
    pub subst_shift: NameId,
    /// `FO.Term.shift : Term -> Term := fun t => Term.subst t Subst.shift`.
    pub term_shift: NameId,
    /// `FO.Subst.cons : Term -> (Nat -> Term) -> Nat -> Term`.
    pub subst_cons: NameId,
    /// `FO.Subst.lift : (Nat -> Term) -> Nat -> Term`.
    pub subst_lift: NameId,
    /// `FO.Formula.subst : Formula -> (Nat -> Term) -> Formula`.
    pub formula_subst: NameId,
    /// `FO.Formula.shift : Formula -> Formula`.
    pub formula_shift: NameId,
}

/// Build the first-order syntax package: `FO.Term`, `FO.Formula`, parallel
/// substitution on both, and the de Bruijn helpers, all through the trusted
/// [`crate::Kernel::add_inductive`] / [`crate::Kernel::add_declaration`] gates.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_syntax_prelude(kernel: &mut crate::Kernel) -> Result<FoSyntaxPrelude, KernelError> {
    let nat = build_nat_prelude(kernel)?;
    let anon = kernel.anon();
    let zero_lvl = kernel.level_zero();
    let one = kernel.level_succ(zero_lvl);
    let nat_ty = kernel.const_(nat.nat, vec![]);

    let fo = kernel.name_str(anon, "FO");

    // --- FO.Term -------------------------------------------------------------
    let term = kernel.name_str(fo, "Term");
    let var = kernel.name_str(term, "var");
    let f0 = kernel.name_str(term, "f0");
    let f1 = kernel.name_str(term, "f1");
    let f2 = kernel.name_str(term, "f2");
    let term_family = kernel.add_recursive_datatype_family(
        term,
        nat_ty,
        one,
        &[
            (var, vec![RecField::Carrier]),
            (f0, vec![RecField::Carrier]),
            (f1, vec![RecField::Carrier, RecField::Recursive]),
            (
                f2,
                vec![RecField::Carrier, RecField::Recursive, RecField::Recursive],
            ),
        ],
    )?;
    let term_rec = term_family.rec;
    let term_ty = kernel.const_(term, vec![]);

    // --- FO.Formula ----------------------------------------------------------
    let formula = kernel.name_str(fo, "Formula");
    let bot = kernel.name_str(formula, "bot");
    let eqf = kernel.name_str(formula, "eqf");
    let rel1 = kernel.name_str(formula, "rel1");
    let rel2 = kernel.name_str(formula, "rel2");
    let and_ = kernel.name_str(formula, "and_");
    let or_ = kernel.name_str(formula, "or_");
    let imp = kernel.name_str(formula, "imp");
    let all = kernel.name_str(formula, "all");
    let ex = kernel.name_str(formula, "ex");
    declare_formula_inductive(
        kernel,
        &FormulaCtors {
            formula,
            bot,
            eqf,
            rel1,
            rel2,
            and_,
            or_,
            imp,
            all,
            ex,
        },
        nat_ty,
        term_ty,
        one,
    )?;
    let formula_rec = kernel.name_str(formula, "rec");
    let formula_ty = kernel.const_(formula, vec![]);

    // --- substitution --------------------------------------------------------
    let syn = SyntaxNames {
        fo,
        term,
        var,
        f0,
        f1,
        f2,
        term_rec,
        formula,
        bot,
        eqf,
        rel1,
        rel2,
        and_,
        or_,
        imp,
        all,
        ex,
        formula_rec,
        nat_ty,
        term_ty,
        formula_ty,
        nat_zero: nat.zero,
        nat_succ: nat.succ,
        nat_rec: nat.rec,
    };

    let term_subst = declare_term_subst(kernel, &syn, one)?;
    let subst_id = declare_subst_id(kernel, &syn)?;
    let subst_shift = declare_subst_shift(kernel, &syn)?;
    let term_shift = declare_term_shift(kernel, &syn, term_subst, subst_shift)?;
    let subst_cons = declare_subst_cons(kernel, &syn, one)?;
    let subst_lift = declare_subst_lift(kernel, &syn, subst_cons, term_shift)?;
    let formula_subst = declare_formula_subst(kernel, &syn, term_subst, subst_lift, one)?;
    let formula_shift = declare_formula_shift(kernel, &syn, formula_subst, subst_shift)?;

    Ok(FoSyntaxPrelude {
        nat,
        term,
        var,
        f0,
        f1,
        f2,
        term_rec,
        formula,
        bot,
        eqf,
        rel1,
        rel2,
        and_,
        or_,
        imp,
        all,
        ex,
        formula_rec,
        term_subst,
        subst_id,
        subst_shift,
        term_shift,
        subst_cons,
        subst_lift,
        formula_subst,
        formula_shift,
    })
}

/// The `FO.Formula` constructor names, gathered so
/// [`declare_formula_inductive`] takes one argument instead of ten.
struct FormulaCtors {
    formula: NameId,
    bot: NameId,
    eqf: NameId,
    rel1: NameId,
    rel2: NameId,
    and_: NameId,
    or_: NameId,
    imp: NameId,
    all: NameId,
    ex: NameId,
}

/// Every name the substitution builders below need, gathered so each takes one
/// argument instead of a dozen.
pub(crate) struct SyntaxNames {
    pub(crate) fo: NameId,
    pub(crate) term: NameId,
    pub(crate) var: NameId,
    pub(crate) f0: NameId,
    pub(crate) f1: NameId,
    pub(crate) f2: NameId,
    pub(crate) term_rec: NameId,
    pub(crate) formula: NameId,
    pub(crate) bot: NameId,
    pub(crate) eqf: NameId,
    pub(crate) rel1: NameId,
    pub(crate) rel2: NameId,
    pub(crate) and_: NameId,
    pub(crate) or_: NameId,
    pub(crate) imp: NameId,
    pub(crate) all: NameId,
    pub(crate) ex: NameId,
    pub(crate) formula_rec: NameId,
    pub(crate) nat_ty: ExprId,
    pub(crate) term_ty: ExprId,
    pub(crate) formula_ty: ExprId,
    pub(crate) nat_zero: NameId,
    pub(crate) nat_succ: NameId,
    pub(crate) nat_rec: NameId,
}

impl FoSyntaxPrelude {
    /// Re-gather the interned names this prelude's builders pass around.
    /// Later slices (`fo_semantics.rs`, `fo_substitution.rs`) build recursor
    /// applications over exactly the same names.
    pub(crate) fn names(&self, kernel: &mut crate::Kernel) -> SyntaxNames {
        let anon = kernel.anon();
        let fo = kernel.name_str(anon, "FO");
        let nat_ty = kernel.const_(self.nat.nat, vec![]);
        let term_ty = kernel.const_(self.term, vec![]);
        let formula_ty = kernel.const_(self.formula, vec![]);
        SyntaxNames {
            fo,
            term: self.term,
            var: self.var,
            f0: self.f0,
            f1: self.f1,
            f2: self.f2,
            term_rec: self.term_rec,
            formula: self.formula,
            bot: self.bot,
            eqf: self.eqf,
            rel1: self.rel1,
            rel2: self.rel2,
            and_: self.and_,
            or_: self.or_,
            imp: self.imp,
            all: self.all,
            ex: self.ex,
            formula_rec: self.formula_rec,
            nat_ty,
            term_ty,
            formula_ty,
            nat_zero: self.nat.zero,
            nat_succ: self.nat.succ,
            nat_rec: self.nat.rec,
        }
    }
}

// ============================================================================
// Small expression combinators, local to the `fo_*` group.
// ============================================================================

pub(crate) fn apply_all(
    kernel: &mut crate::Kernel,
    mut function: ExprId,
    arguments: &[ExprId],
) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// `fun (_ : ty) => body`, abstracting the single fvar `id` out of `body`.
pub(crate) fn lam_fv(kernel: &mut crate::Kernel, id: u64, ty: ExprId, body: ExprId) -> ExprId {
    let anon = kernel.anon();
    let abstracted = kernel.abstract_fvars(body, &[id]);
    kernel.lam(anon, ty, abstracted, BinderInfo::Default)
}

/// `Pi (_ : ty), body`, abstracting the single fvar `id` out of `body`.
pub(crate) fn pi_fv(kernel: &mut crate::Kernel, id: u64, ty: ExprId, body: ExprId) -> ExprId {
    let anon = kernel.anon();
    let abstracted = kernel.abstract_fvars(body, &[id]);
    kernel.pi(anon, ty, abstracted, BinderInfo::Default)
}

/// The non-dependent arrow `dom -> cod`.
pub(crate) fn arrow(kernel: &mut crate::Kernel, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, dom, cod, BinderInfo::Default)
}

/// A chain of `fun` binders over consecutive fvar ids, innermost last:
/// `lams(&[(id0, ty0), (id1, ty1)], body)` is `fun (x0 : ty0) (x1 : ty1) => body`.
pub(crate) fn lams(kernel: &mut crate::Kernel, binders: &[(u64, ExprId)], body: ExprId) -> ExprId {
    let mut result = body;
    for &(id, ty) in binders.iter().rev() {
        result = lam_fv(kernel, id, ty, result);
    }
    result
}

/// A chain of `Pi` binders over consecutive fvar ids, innermost last.
pub(crate) fn pis(kernel: &mut crate::Kernel, binders: &[(u64, ExprId)], body: ExprId) -> ExprId {
    let mut result = body;
    for &(id, ty) in binders.iter().rev() {
        result = pi_fv(kernel, id, ty, result);
    }
    result
}

// ============================================================================
// FO.Formula, the inductive.
// ============================================================================

/// Declare `FO.Formula : Type` with its nine constructors, in the order the
/// module docs list them (which fixes the minor-premise order of every
/// `FO.Formula.rec` application in this group).
fn declare_formula_inductive(
    kernel: &mut crate::Kernel,
    c: &FormulaCtors,
    nat_ty: ExprId,
    term_ty: ExprId,
    one: LevelId,
) -> Result<(), KernelError> {
    let formula_ty = kernel.sort(one);
    let formula_const = kernel.const_(c.formula, vec![]);

    // A constructor type is a right-nested Pi over the given field types,
    // ending in `FO.Formula`. All fields are non-dependent, so a plain fold
    // over the reversed field list is enough.
    let mk = |kernel: &mut crate::Kernel, fields: &[ExprId]| -> ExprId {
        let anon = kernel.anon();
        let mut ty = formula_const;
        for &field in fields.iter().rev() {
            ty = kernel.pi(anon, field, ty, BinderInfo::Default);
        }
        ty
    };

    let bot_ty = mk(kernel, &[]);
    let eqf_ty = mk(kernel, &[term_ty, term_ty]);
    let rel1_ty = mk(kernel, &[nat_ty, term_ty]);
    let rel2_ty = mk(kernel, &[nat_ty, term_ty, term_ty]);
    let and_ty = mk(kernel, &[formula_const, formula_const]);
    let or_ty = mk(kernel, &[formula_const, formula_const]);
    let imp_ty = mk(kernel, &[formula_const, formula_const]);
    let all_ty = mk(kernel, &[formula_const]);
    let ex_ty = mk(kernel, &[formula_const]);

    kernel.add_inductive(
        c.formula,
        &[],
        0,
        formula_ty,
        &[
            (c.bot, bot_ty),
            (c.eqf, eqf_ty),
            (c.rel1, rel1_ty),
            (c.rel2, rel2_ty),
            (c.and_, and_ty),
            (c.or_, or_ty),
            (c.imp, imp_ty),
            (c.all, all_ty),
            (c.ex, ex_ty),
        ],
    )
}

// ============================================================================
// Substitution.
// ============================================================================

/// The type `Nat -> FO.Term` of a parallel substitution.
pub(crate) fn subst_ty(kernel: &mut crate::Kernel, syn: &SyntaxNames) -> ExprId {
    arrow(kernel, syn.nat_ty, syn.term_ty)
}

/// `FO.Term.var i`.
pub(crate) fn var_app(kernel: &mut crate::Kernel, syn: &SyntaxNames, i: ExprId) -> ExprId {
    let c = kernel.const_(syn.var, vec![]);
    kernel.app(c, i)
}

/// `Nat.succ n`.
pub(crate) fn succ_app(kernel: &mut crate::Kernel, syn: &SyntaxNames, n: ExprId) -> ExprId {
    let c = kernel.const_(syn.nat_succ, vec![]);
    kernel.app(c, n)
}

/// Declare `FO.Term.subst : Term -> (Nat -> Term) -> Term`, a `FO.Term.rec`
/// application at the non-dependent motive `fun _ => (Nat -> Term) -> Term`.
///
/// Minor premises, one per constructor in declaration order (`var, f0, f1,
/// f2`), with induction hypotheses appended after the field binders in field
/// order:
///
/// ```text
/// m_var : Nat -> (Nat -> Term) -> Term            := fun i s => s i
/// m_f0  : Nat -> (Nat -> Term) -> Term            := fun k s => f0 k
/// m_f1  : Nat -> Term -> C -> (Nat -> Term) -> Term
///                                                 := fun k _ ih s => f1 k (ih s)
/// m_f2  : Nat -> Term -> Term -> C -> C -> (Nat -> Term) -> Term
///                                                 := fun k _ _ ia ib s => f2 k (ia s) (ib s)
/// ```
///
/// where `C` is the motive codomain `(Nat -> Term) -> Term`. **Only `m_var`
/// consults the substitution**; every other case rebuilds its constructor and
/// pushes the substitution inward, which is what makes `subst` the identity on
/// closed terms and what the module tests check directly.
fn declare_term_subst(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let sub_ty = subst_ty(kernel, syn);
    let codomain = arrow(kernel, sub_ty, syn.term_ty);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, syn.term_ty, codomain, BinderInfo::Default);

    // m_var := fun (i : Nat) (s : Nat -> Term) => s i
    let m_var = {
        let i_id = 1_636_101_u64;
        let s_id = 1_636_102_u64;
        let i = kernel.fvar(i_id);
        let s = kernel.fvar(s_id);
        let body = kernel.app(s, i);
        lams(kernel, &[(i_id, syn.nat_ty), (s_id, sub_ty)], body)
    };

    // m_f0 := fun (k : Nat) (s : Nat -> Term) => FO.Term.f0 k
    let m_f0 = {
        let k_id = 1_636_111_u64;
        let s_id = 1_636_112_u64;
        let k = kernel.fvar(k_id);
        let f0_const = kernel.const_(syn.f0, vec![]);
        let body = kernel.app(f0_const, k);
        lams(kernel, &[(k_id, syn.nat_ty), (s_id, sub_ty)], body)
    };

    // m_f1 := fun (k : Nat) (_ : Term) (ih : C) (s : Nat -> Term) => FO.Term.f1 k (ih s)
    let m_f1 = {
        let k_id = 1_636_121_u64;
        let t_id = 1_636_122_u64;
        let ih_id = 1_636_123_u64;
        let s_id = 1_636_124_u64;
        let k = kernel.fvar(k_id);
        let ih = kernel.fvar(ih_id);
        let s = kernel.fvar(s_id);
        let ih_s = kernel.app(ih, s);
        let f1_const = kernel.const_(syn.f1, vec![]);
        let body = apply_all(kernel, f1_const, &[k, ih_s]);
        lams(
            kernel,
            &[
                (k_id, syn.nat_ty),
                (t_id, syn.term_ty),
                (ih_id, codomain),
                (s_id, sub_ty),
            ],
            body,
        )
    };

    // m_f2 := fun k _ _ ia ib s => FO.Term.f2 k (ia s) (ib s)
    let m_f2 = {
        let k_id = 1_636_131_u64;
        let a_id = 1_636_132_u64;
        let b_id = 1_636_133_u64;
        let ia_id = 1_636_134_u64;
        let ib_id = 1_636_135_u64;
        let s_id = 1_636_136_u64;
        let k = kernel.fvar(k_id);
        let ia = kernel.fvar(ia_id);
        let ib = kernel.fvar(ib_id);
        let s = kernel.fvar(s_id);
        let ia_s = kernel.app(ia, s);
        let ib_s = kernel.app(ib, s);
        let f2_const = kernel.const_(syn.f2, vec![]);
        let body = apply_all(kernel, f2_const, &[k, ia_s, ib_s]);
        lams(
            kernel,
            &[
                (k_id, syn.nat_ty),
                (a_id, syn.term_ty),
                (b_id, syn.term_ty),
                (ia_id, codomain),
                (ib_id, codomain),
                (s_id, sub_ty),
            ],
            body,
        )
    };

    let rec_const = kernel.const_(syn.term_rec, vec![one]);
    let applied = apply_all(kernel, rec_const, &[motive, m_var, m_f0, m_f1, m_f2]);

    let t_id = 1_636_141_u64;
    let t = kernel.fvar(t_id);
    let body = kernel.app(applied, t);
    let value = lam_fv(kernel, t_id, syn.term_ty, body);
    let ty = arrow(kernel, syn.term_ty, codomain);

    let name = kernel.name_str(syn.term, "subst");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Subst.id : Nat -> FO.Term := fun n => FO.Term.var n` — the identity
/// substitution.
fn declare_subst_id(kernel: &mut crate::Kernel, syn: &SyntaxNames) -> Result<NameId, KernelError> {
    let n_id = 1_636_201_u64;
    let n = kernel.fvar(n_id);
    let body = var_app(kernel, syn, n);
    let value = lam_fv(kernel, n_id, syn.nat_ty, body);
    let ty = subst_ty(kernel, syn);
    let subst_ns = kernel.name_str(syn.fo, "Subst");
    let name = kernel.name_str(subst_ns, "id");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Subst.shift : Nat -> FO.Term := fun n => FO.Term.var (Nat.succ n)` —
/// the substitution that renames every index one step out of a freshly opened
/// binder's way.
fn declare_subst_shift(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
) -> Result<NameId, KernelError> {
    let n_id = 1_636_211_u64;
    let n = kernel.fvar(n_id);
    let sn = succ_app(kernel, syn, n);
    let body = var_app(kernel, syn, sn);
    let value = lam_fv(kernel, n_id, syn.nat_ty, body);
    let ty = subst_ty(kernel, syn);
    let subst_ns = kernel.name_str(syn.fo, "Subst");
    let name = kernel.name_str(subst_ns, "shift");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Term.shift : Term -> Term := fun t => FO.Term.subst t FO.Subst.shift`.
fn declare_term_shift(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    term_subst: NameId,
    subst_shift: NameId,
) -> Result<NameId, KernelError> {
    let t_id = 1_636_221_u64;
    let t = kernel.fvar(t_id);
    let subst_const = kernel.const_(term_subst, vec![]);
    let shift_const = kernel.const_(subst_shift, vec![]);
    let body = apply_all(kernel, subst_const, &[t, shift_const]);
    let value = lam_fv(kernel, t_id, syn.term_ty, body);
    let ty = arrow(kernel, syn.term_ty, syn.term_ty);
    let name = kernel.name_str(syn.term, "shift");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Subst.cons : Term -> (Nat -> Term) -> Nat -> Term`, written `t · s`:
///
/// ```text
/// fun (t : Term) (s : Nat -> Term) (n : Nat) =>
///   Nat.rec.{1} (motive := fun _ => Term) t (fun k _ => s k) n
/// ```
///
/// so `cons t s Nat.zero` ι-reduces to `t` and `cons t s (Nat.succ k)` to
/// `s k`. Both reductions are relied on downstream: `∀`-elimination's
/// instance is `Formula.subst φ (cons t Subst.id)`, and `fo_substitution.rs`
/// discharges the index-`0` half of its `∀` case by `Eq.refl` because of the
/// first one.
fn declare_subst_cons(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let sub_ty = subst_ty(kernel, syn);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, syn.nat_ty, syn.term_ty, BinderInfo::Default);

    let t_id = 1_636_231_u64;
    let s_id = 1_636_232_u64;
    let n_id = 1_636_233_u64;
    let k_id = 1_636_234_u64;
    let ih_id = 1_636_235_u64;

    let t = kernel.fvar(t_id);
    let s = kernel.fvar(s_id);
    let n = kernel.fvar(n_id);
    let k = kernel.fvar(k_id);

    // step := fun (k : Nat) (_ : Term) => s k
    let s_k = kernel.app(s, k);
    let step = lams(kernel, &[(k_id, syn.nat_ty), (ih_id, syn.term_ty)], s_k);

    let nat_rec = kernel.const_(syn.nat_rec, vec![one]);
    let body = apply_all(kernel, nat_rec, &[motive, t, step, n]);
    let value = lams(
        kernel,
        &[(t_id, syn.term_ty), (s_id, sub_ty), (n_id, syn.nat_ty)],
        body,
    );

    let cod = arrow(kernel, syn.nat_ty, syn.term_ty);
    let ty = {
        let inner = arrow(kernel, sub_ty, cod);
        arrow(kernel, syn.term_ty, inner)
    };

    let subst_ns = kernel.name_str(syn.fo, "Subst");
    let name = kernel.name_str(subst_ns, "cons");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Subst.lift : (Nat -> Term) -> Nat -> Term`, the substitution to use
/// under a binder:
///
/// ```text
/// fun (s : Nat -> Term) => FO.Subst.cons (FO.Term.var 0) (fun n => FO.Term.shift (s n))
/// ```
///
/// Index `0` — the one the binder just introduced — is mapped to itself, and
/// every term the old substitution produced is shifted so its free indices
/// still point past the new binder.
fn declare_subst_lift(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    subst_cons: NameId,
    term_shift: NameId,
) -> Result<NameId, KernelError> {
    let sub_ty = subst_ty(kernel, syn);
    let s_id = 1_636_241_u64;
    let n_id = 1_636_242_u64;
    let s = kernel.fvar(s_id);
    let n = kernel.fvar(n_id);

    let s_n = kernel.app(s, n);
    let shift_const = kernel.const_(term_shift, vec![]);
    let shifted = kernel.app(shift_const, s_n);
    let tail = lam_fv(kernel, n_id, syn.nat_ty, shifted);

    let zero = kernel.const_(syn.nat_zero, vec![]);
    let head = var_app(kernel, syn, zero);
    let cons_const = kernel.const_(subst_cons, vec![]);
    let body = apply_all(kernel, cons_const, &[head, tail]);
    let value = lam_fv(kernel, s_id, sub_ty, body);

    let ty = arrow(kernel, sub_ty, sub_ty);
    let subst_ns = kernel.name_str(syn.fo, "Subst");
    let name = kernel.name_str(subst_ns, "lift");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// Declare `FO.Formula.subst : Formula -> (Nat -> Term) -> Formula`, a
/// `FO.Formula.rec` application at the non-dependent motive
/// `fun _ => (Nat -> Term) -> Formula`.
///
/// The two cases that carry all the content:
///
/// ```text
/// m_all : Formula -> C -> (Nat -> Term) -> Formula
///       := fun _ ih s => FO.Formula.all (ih (FO.Subst.lift s))
/// m_ex  := the same with FO.Formula.ex
/// ```
///
/// Everything else pushes the substitution into its subterms unchanged. The
/// `lift` in the binder cases is the only difference between this and a
/// substitution that would capture; the module tests check exactly that, by
/// substituting a term with a free index under an `all` and reading back the
/// shifted index.
fn declare_formula_subst(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    term_subst: NameId,
    subst_lift: NameId,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let sub_ty = subst_ty(kernel, syn);
    let codomain = arrow(kernel, sub_ty, syn.formula_ty);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, syn.formula_ty, codomain, BinderInfo::Default);

    // `FO.Term.subst t s`, used by the four atomic cases.
    let tsub = |kernel: &mut crate::Kernel, t: ExprId, s: ExprId| -> ExprId {
        let c = kernel.const_(term_subst, vec![]);
        apply_all(kernel, c, &[t, s])
    };

    // m_bot := fun (s : Nat -> Term) => FO.Formula.bot
    let m_bot = {
        let s_id = 1_636_301_u64;
        let bot_const = kernel.const_(syn.bot, vec![]);
        lam_fv(kernel, s_id, sub_ty, bot_const)
    };

    // m_eqf := fun (a b : Term) (s) => FO.Formula.eqf (a[s]) (b[s])
    let m_eqf = {
        let a_id = 1_636_311_u64;
        let b_id = 1_636_312_u64;
        let s_id = 1_636_313_u64;
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let s = kernel.fvar(s_id);
        let a_s = tsub(kernel, a, s);
        let b_s = tsub(kernel, b, s);
        let c = kernel.const_(syn.eqf, vec![]);
        let body = apply_all(kernel, c, &[a_s, b_s]);
        lams(
            kernel,
            &[(a_id, syn.term_ty), (b_id, syn.term_ty), (s_id, sub_ty)],
            body,
        )
    };

    // m_rel1 := fun (k : Nat) (t : Term) (s) => FO.Formula.rel1 k (t[s])
    let m_rel1 = {
        let k_id = 1_636_321_u64;
        let t_id = 1_636_322_u64;
        let s_id = 1_636_323_u64;
        let k = kernel.fvar(k_id);
        let t = kernel.fvar(t_id);
        let s = kernel.fvar(s_id);
        let t_s = tsub(kernel, t, s);
        let c = kernel.const_(syn.rel1, vec![]);
        let body = apply_all(kernel, c, &[k, t_s]);
        lams(
            kernel,
            &[(k_id, syn.nat_ty), (t_id, syn.term_ty), (s_id, sub_ty)],
            body,
        )
    };

    // m_rel2 := fun (k : Nat) (a b : Term) (s) => FO.Formula.rel2 k (a[s]) (b[s])
    let m_rel2 = {
        let k_id = 1_636_331_u64;
        let a_id = 1_636_332_u64;
        let b_id = 1_636_333_u64;
        let s_id = 1_636_334_u64;
        let k = kernel.fvar(k_id);
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let s = kernel.fvar(s_id);
        let a_s = tsub(kernel, a, s);
        let b_s = tsub(kernel, b, s);
        let c = kernel.const_(syn.rel2, vec![]);
        let body = apply_all(kernel, c, &[k, a_s, b_s]);
        lams(
            kernel,
            &[
                (k_id, syn.nat_ty),
                (a_id, syn.term_ty),
                (b_id, syn.term_ty),
                (s_id, sub_ty),
            ],
            body,
        )
    };

    // The three binary connectives share a shape.
    let binary = |kernel: &mut crate::Kernel, ctor: NameId, base: u64| -> ExprId {
        let a_id = base;
        let b_id = base + 1;
        let ia_id = base + 2;
        let ib_id = base + 3;
        let s_id = base + 4;
        let ia = kernel.fvar(ia_id);
        let ib = kernel.fvar(ib_id);
        let s = kernel.fvar(s_id);
        let ia_s = kernel.app(ia, s);
        let ib_s = kernel.app(ib, s);
        let c = kernel.const_(ctor, vec![]);
        let body = apply_all(kernel, c, &[ia_s, ib_s]);
        lams(
            kernel,
            &[
                (a_id, syn.formula_ty),
                (b_id, syn.formula_ty),
                (ia_id, codomain),
                (ib_id, codomain),
                (s_id, sub_ty),
            ],
            body,
        )
    };
    let m_and = binary(kernel, syn.and_, 1_636_341_u64);
    let m_or = binary(kernel, syn.or_, 1_636_351_u64);
    let m_imp = binary(kernel, syn.imp, 1_636_361_u64);

    // The two quantifiers share a shape, and it is the one with the `lift`.
    let quantifier = |kernel: &mut crate::Kernel, ctor: NameId, base: u64| -> ExprId {
        let a_id = base;
        let ia_id = base + 1;
        let s_id = base + 2;
        let ia = kernel.fvar(ia_id);
        let s = kernel.fvar(s_id);
        let lift_const = kernel.const_(subst_lift, vec![]);
        let lifted = kernel.app(lift_const, s);
        let ia_lifted = kernel.app(ia, lifted);
        let c = kernel.const_(ctor, vec![]);
        let body = kernel.app(c, ia_lifted);
        lams(
            kernel,
            &[(a_id, syn.formula_ty), (ia_id, codomain), (s_id, sub_ty)],
            body,
        )
    };
    let m_all = quantifier(kernel, syn.all, 1_636_371_u64);
    let m_ex = quantifier(kernel, syn.ex, 1_636_381_u64);

    let rec_const = kernel.const_(syn.formula_rec, vec![one]);
    let applied = apply_all(
        kernel,
        rec_const,
        &[
            motive, m_bot, m_eqf, m_rel1, m_rel2, m_and, m_or, m_imp, m_all, m_ex,
        ],
    );

    let p_id = 1_636_391_u64;
    let p = kernel.fvar(p_id);
    let body = kernel.app(applied, p);
    let value = lam_fv(kernel, p_id, syn.formula_ty, body);
    let ty = arrow(kernel, syn.formula_ty, codomain);

    let name = kernel.name_str(syn.formula, "subst");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Formula.shift : Formula -> Formula := fun p => FO.Formula.subst p FO.Subst.shift`.
/// This is what `fo_provable.rs` applies to a whole context in the
/// `∀`-introduction rule.
fn declare_formula_shift(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    formula_subst: NameId,
    subst_shift: NameId,
) -> Result<NameId, KernelError> {
    let p_id = 1_636_401_u64;
    let p = kernel.fvar(p_id);
    let subst_const = kernel.const_(formula_subst, vec![]);
    let shift_const = kernel.const_(subst_shift, vec![]);
    let body = apply_all(kernel, subst_const, &[p, shift_const]);
    let value = lam_fv(kernel, p_id, syn.formula_ty, body);
    let ty = arrow(kernel, syn.formula_ty, syn.formula_ty);
    let name = kernel.name_str(syn.formula, "shift");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

// ============================================================================
// Carrier-generic `Eq` and `Iff` combinators.
//
// `NatOps`'s `eq`/`refl`/`transport`/`symm`/`trans`/`congr` family HARDCODES
// `Nat` as the equality's carrier (`nat_prelude/ops.rs`: `fn eq` applies
// `Eq.{1}` to `self.nat_ty()`). This group needs equalities at four different
// carriers — `Nat` for indices, `FO.Term`, `FO.Formula`, and the structure's
// own `M` — so it carries its own copies, parameterized by the carrier. Using
// the `NatOps` ones here fails as one opaque `TypeMismatch`, which is the
// workspace's standing "dev helpers hardcode a carrier" gotcha.
//
// Every carrier this group uses lives at `Sort 1`, so the universe arguments
// are fixed: `Eq.{1}`, `Eq.refl.{1}`, `Eq.rec.{0,1}` (motive in `Prop`).
// ============================================================================

/// `Eq.{1} ty x y`.
pub(crate) fn geq(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    ty: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let c = kernel.const_(logic.eq, vec![one]);
    apply_all(kernel, c, &[ty, x, y])
}

/// `Eq.refl.{1} ty a : Eq ty a a`.
pub(crate) fn grefl(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    ty: ExprId,
    a: ExprId,
) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let c = kernel.const_(logic.eq_refl, vec![one]);
    apply_all(kernel, c, &[ty, a])
}

/// `Eq.rec.{0,1} ty p motive refl_case q h : motive q h`.
pub(crate) fn gtransport(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    ty: ExprId,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let c = kernel.const_(logic.eq_rec, vec![zero, one]);
    apply_all(kernel, c, &[ty, p, motive, refl_case, q, h])
}

/// The `Eq.rec` motive `fun (x : ty) (_ : Eq ty a x) => body(x)`, at a
/// `Prop`-valued `body`.
pub(crate) fn geq_motive(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    ty: ExprId,
    a: ExprId,
    body: &dyn Fn(&mut crate::Kernel, ExprId) -> ExprId,
    fv: u64,
) -> ExprId {
    let x = kernel.fvar(fv);
    let concl = body(kernel, x);
    let hyp = geq(kernel, logic, ty, a, x);
    let anon = kernel.anon();
    let inner = kernel.lam(anon, hyp, concl, BinderInfo::Default);
    lam_fv(kernel, fv, ty, inner)
}

/// `h : Eq ty a b ⊢ Eq ty b a`.
pub(crate) fn gsymm(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    fv: u64,
) -> ExprId {
    let motive = geq_motive(kernel, logic, ty, a, &|k, x| geq(k, logic, ty, x, a), fv);
    let refl_case = grefl(kernel, logic, ty, a);
    gtransport(kernel, logic, ty, a, motive, refl_case, b, h)
}

/// `h1 : Eq ty a b`, `h2 : Eq ty b c ⊢ Eq ty a c`.
pub(crate) fn gtrans(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
    fv: u64,
) -> ExprId {
    let motive = geq_motive(kernel, logic, ty, b, &|k, x| geq(k, logic, ty, a, x), fv);
    gtransport(kernel, logic, ty, b, motive, h1, c, h2)
}

/// Congruence in a one-hole context that may change carrier:
/// `h : Eq src a b ⊢ Eq dst (f a) (f b)`.
pub(crate) fn gcongr(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    src: ExprId,
    dst: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut crate::Kernel, ExprId) -> ExprId,
    fv: u64,
) -> ExprId {
    let fa = f(kernel, a);
    let motive = geq_motive(
        kernel,
        logic,
        src,
        a,
        &|k, x| {
            let fx = f(k, x);
            geq(k, logic, dst, fa, fx)
        },
        fv,
    );
    let refl_case = grefl(kernel, logic, dst, fa);
    gtransport(kernel, logic, src, a, motive, refl_case, b, h)
}

/// `Iff.intro a b mp mpr : Iff a b`.
pub(crate) fn iff_intro(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    a: ExprId,
    b: ExprId,
    mp: ExprId,
    mpr: ExprId,
) -> ExprId {
    let c = kernel.const_(logic.iff_intro, vec![]);
    apply_all(kernel, c, &[a, b, mp, mpr])
}

/// `Iff.mp a b h : a -> b`.
pub(crate) fn iff_mp(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let c = kernel.const_(logic.iff_mp, vec![]);
    apply_all(kernel, c, &[a, b, h])
}

/// `Iff.mpr a b h : b -> a`.
pub(crate) fn iff_mpr(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let c = kernel.const_(logic.iff_mpr, vec![]);
    apply_all(kernel, c, &[a, b, h])
}

/// `Iff a b`.
pub(crate) fn iff_ty(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let c = kernel.const_(logic.iff, vec![]);
    apply_all(kernel, c, &[a, b])
}

/// `h1 : Iff a b`, `h2 : Iff b c ⊢ Iff a c`. The kernel's `LogicPrelude` has
/// `Iff.intro`/`Iff.mp`/`Iff.mpr` but no `Iff.trans`, so it is spelled out
/// here (the same construction `proof_plan.rs`'s private `iff_trans` uses,
/// which is `NatOps`-generic and therefore not callable from this group).
pub(crate) fn giff_trans(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
    base_fv: u64,
) -> ExprId {
    let mp = {
        let fv = base_fv;
        let x = kernel.fvar(fv);
        let step1 = iff_mp(kernel, logic, a, b, h1);
        let in_b = kernel.app(step1, x);
        let step2 = iff_mp(kernel, logic, b, c, h2);
        let in_c = kernel.app(step2, in_b);
        lam_fv(kernel, fv, a, in_c)
    };
    let mpr = {
        let fv = base_fv + 1;
        let x = kernel.fvar(fv);
        let step2 = iff_mpr(kernel, logic, b, c, h2);
        let in_b = kernel.app(step2, x);
        let step1 = iff_mpr(kernel, logic, a, b, h1);
        let in_a = kernel.app(step1, in_b);
        lam_fv(kernel, fv, c, in_a)
    };
    iff_intro(kernel, logic, a, c, mp, mpr)
}

/// `Iff a a`, proved by the identity in both directions.
pub(crate) fn giff_refl(
    kernel: &mut crate::Kernel,
    logic: crate::LogicPrelude,
    a: ExprId,
    fv: u64,
) -> ExprId {
    let x = kernel.fvar(fv);
    let id = lam_fv(kernel, fv, a, x);
    iff_intro(kernel, logic, a, a, id, id)
}

#[cfg(test)]
mod tests;
