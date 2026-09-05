//! **Slice 3 of the first-order model theory group** (`fo_*.rs`, ADR-1636):
//! a context type, context satisfaction, and `FO.Provable` — a first-order
//! natural-deduction relation with the eleven intuitionistic propositional
//! rules of `ipc_provable.rs` plus five first-order ones.
//!
//! ## `FO.Context` and `FO.ctxSat`
//!
//! ```text
//! FO.Context      : Type                                    -- nil | cons Formula Context
//! FO.Context.shift : Context -> Context                     -- Formula.shift on every entry
//! FO.ctxSat : Π (M : Type) (S : FO.Structure M), Context -> (Nat -> M) -> Prop
//!   nil       ↦ True
//!   cons a l  ↦ And (FO.sat M S a v) (FO.ctxSat M S l v)
//! ```
//!
//! `ctxSat` is the `Prop`-valued analogue of `ipc_soundness.rs`'s `ipc_sat`,
//! and unlike that development it is the statement soundness is actually
//! proved in: the 3-element-chain semantics needed a *meet of the context*
//! because "every hypothesis is top" carried no induction through
//! `imp_intro`. Here it does, because `sat (imp φ ψ) v` **is** the kernel's
//! own function type `sat φ v -> sat ψ v`, so `imp_intro`'s case is a lambda.
//!
//! ## The sixteen rules
//!
//! The eleven propositional rules are `ipc_provable.rs`'s, transcribed to
//! `FO.Formula` (`ax_head`, `weaken`, `and_intro`, `and_elim1`, `and_elim2`,
//! `or_intro1`, `or_intro2`, `or_elim`, `imp_intro`, `imp_elim`, `bot_elim`).
//! Membership in the context is again `ax_head` + `weaken` rather than a
//! separate `Mem` relation, for the same reason: the two together generate
//! exactly "the goal occurs somewhere in the context".
//!
//! The five first-order rules:
//!
//! ```text
//! all_intro : Π g p,   Provable (Context.shift g) p
//!                        -> Provable g (all p)
//! all_elim  : Π g p t, Provable g (all p)
//!                        -> Provable g (Formula.subst p (Subst.cons t Subst.id))
//! ex_intro  : Π g p t, Provable g (Formula.subst p (Subst.cons t Subst.id))
//!                        -> Provable g (ex p)
//! ex_elim   : Π g p q, Provable g (ex p)
//!                        -> Provable (Context.cons p (Context.shift g)) (Formula.shift q)
//!                        -> Provable g q
//! eqf_refl  : Π g t,   Provable g (eqf t t)
//! ```
//!
//! ### The eigenvariable condition, stated as a shift
//!
//! `all_intro` is where the side condition lives, and in de Bruijn form it is
//! not a side condition at all — it is the shape of the premise. The textbook
//! rule is
//!
//! > from `Γ ⊢ φ[x]` infer `Γ ⊢ ∀y. φ[y]`, **provided `x` is not free in `Γ`**
//!
//! and the proviso is what stops `p(x) ⊢ ∀y. p(y)`. Here the premise's context
//! is `Context.shift g`: every free index in `g` has been raised by one, so
//! **de Bruijn index `0` — the one `all` is about to bind — cannot occur
//! anywhere in the premise's context**. That is the eigenvariable condition,
//! enforced structurally by the constructor's type rather than by an
//! `occursIn : Nat -> Formula -> Prop` predicate the rule would have to carry
//! as an extra hypothesis. `fo_soundness.rs`'s `all_intro` case is where it
//! pays: the induction hypothesis is available at the *extended* valuation
//! `Val.cons x v` precisely because the context it constrains is the shifted
//! one, and `FO.ctxSat_shift` bridges the two.
//!
//! `ex_elim` carries the same condition twice over: the minor premise's
//! context shifts `g` (so `g` cannot mention the witness) **and** its
//! conclusion is `Formula.shift q` (so the conclusion cannot mention it
//! either). Dropping either half makes the rule unsound, and
//! `fo_soundness.rs`'s case for it uses both.
//!
//! `all_elim` and `ex_intro` instantiate at an arbitrary term `t` via the
//! parallel substitution `Subst.cons t Subst.id` — "put `t` at index `0`, and
//! shift everything else down one" — which is exactly `φ[t/x]` in de Bruijn
//! form. No capture check is needed, because `Formula.subst` lifts under
//! binders (`fo_syntax.rs`).
//!
//! ### `eqf_refl`, and what is deliberately *not* here
//!
//! `eqf_refl` is the only equality rule. It makes `FO.Formula.eqf` a
//! non-decorative constructor and its soundness case is `Eq.refl`. The
//! Leibniz rule — from `s = t` and `φ[s]` infer `φ[t]` — is **not** landed:
//! it is sound, but its soundness case needs a congruence of `FO.sat` along an
//! equality *between the evaluations of two terms under a substitution*, which
//! is a fifth induction over `FO.Formula` this slice does not build. It is
//! recorded as the next increment rather than claimed.
//!
//! Completeness is likewise not attempted, and is not a gap this file is
//! hiding: it needs a term model over a maximal consistent extension, i.e.
//! Lindenbaum's lemma, and in a kernel with no `Classical.em` the classical
//! completeness theorem is not the statement to aim at. See the `open` fact
//! `F:fo-completeness-henkin` for the decomposition.
//!
//! ## Non-vacuity
//!
//! An inductive relation can type-check and be uninhabited, or inhabited only
//! in trivial ways, exactly as a `Definition` can compute the wrong value.
//! Three closed derivations are landed as kernel `Theorem`s, chosen so that
//! between them every quantifier rule is exercised:
//!
//! - `FO.provable_imp_self : Provable nil (imp a a)` — propositional only.
//! - `FO.provable_all_imp_self : Provable nil (all (imp a a))` — uses
//!   `all_intro`, and goes through because `Context.shift nil` ι-reduces to
//!   `nil`.
//! - `FO.provable_all_imp_ex : Provable nil (imp (all p) (ex p))` — uses
//!   `all_elim` **and** `ex_intro` at the same instance term, the genuinely
//!   first-order derivation of the group.

use crate::fo_syntax::SyntaxNames;
use crate::fo_syntax::{apply_all, arrow, lam_fv, lams, pis};
use crate::{BinderInfo, Declaration, ExprId, FoSemanticsPrelude, KernelError, LevelId, NameId};
use crate::{RecField, ReducibilityHint, build_fo_semantics_prelude};

/// Names produced by [`build_fo_provable_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoProvablePrelude {
    /// `FO.Structure`, `FO.Term.eval`, `FO.sat` and the syntax below them.
    pub semantics: FoSemanticsPrelude,

    // --- FO.Context ----------------------------------------------------------
    /// `FO.Context : Type`.
    pub context: NameId,
    /// `FO.Context.nil : Context`.
    pub nil: NameId,
    /// `FO.Context.cons : Formula -> Context -> Context`.
    pub cons: NameId,
    /// `FO.Context.rec`.
    pub context_rec: NameId,
    /// `FO.Context.shift : Context -> Context`.
    pub context_shift: NameId,
    /// `FO.ctxSat : Π (M) (S), Context -> (Nat -> M) -> Prop`.
    pub ctx_sat: NameId,

    // --- FO.Provable ---------------------------------------------------------
    /// `FO.Provable : Context -> Formula -> Prop`.
    pub provable: NameId,
    /// `FO.Provable.rec`.
    pub provable_rec: NameId,
    /// The sixteen constructors, in declaration order (which fixes the
    /// minor-premise order of every `FO.Provable.rec` application).
    pub rules: [NameId; 16],

    // --- example derivations -------------------------------------------------
    /// `FO.provable_imp_self : Provable nil (imp a a)`.
    pub provable_imp_self: NameId,
    /// `FO.provable_all_imp_self : Provable nil (all (imp a a))`.
    pub provable_all_imp_self: NameId,
    /// `FO.provable_all_imp_ex : Provable nil (imp (all p) (ex p))`.
    pub provable_all_imp_ex: NameId,
}

/// Index of each rule inside [`FoProvablePrelude::rules`].
pub(crate) mod rule {
    /// `ax_head`.
    pub(crate) const AX_HEAD: usize = 0;
    /// `weaken`.
    pub(crate) const WEAKEN: usize = 1;
    /// `and_intro`.
    pub(crate) const AND_INTRO: usize = 2;
    /// `and_elim1`.
    pub(crate) const AND_ELIM1: usize = 3;
    /// `and_elim2`.
    pub(crate) const AND_ELIM2: usize = 4;
    /// `or_intro1`.
    pub(crate) const OR_INTRO1: usize = 5;
    /// `or_intro2`.
    pub(crate) const OR_INTRO2: usize = 6;
    /// `or_elim`.
    pub(crate) const OR_ELIM: usize = 7;
    /// `imp_intro`.
    pub(crate) const IMP_INTRO: usize = 8;
    /// `imp_elim`.
    pub(crate) const IMP_ELIM: usize = 9;
    /// `bot_elim`.
    pub(crate) const BOT_ELIM: usize = 10;
    /// `all_intro`.
    pub(crate) const ALL_INTRO: usize = 11;
    /// `all_elim`.
    pub(crate) const ALL_ELIM: usize = 12;
    /// `ex_intro`.
    pub(crate) const EX_INTRO: usize = 13;
    /// `ex_elim`.
    pub(crate) const EX_ELIM: usize = 14;
    /// `eqf_refl`.
    pub(crate) const EQF_REFL: usize = 15;
}

/// The names the rule builders below share.
pub(crate) struct CalcNames {
    pub(crate) context_ty: ExprId,
    pub(crate) formula_ty: ExprId,
    pub(crate) term_ty: ExprId,
    pub(crate) provable: NameId,
    pub(crate) nil: NameId,
    pub(crate) cons: NameId,
    pub(crate) context_shift: NameId,
    pub(crate) and_: NameId,
    pub(crate) or_: NameId,
    pub(crate) imp: NameId,
    pub(crate) all: NameId,
    pub(crate) ex: NameId,
    pub(crate) eqf: NameId,
    pub(crate) bot: NameId,
    pub(crate) formula_subst: NameId,
    pub(crate) formula_shift: NameId,
    pub(crate) subst_cons: NameId,
    pub(crate) subst_id: NameId,
}

impl FoProvablePrelude {
    /// Re-gather the names the rule and soundness builders share.
    pub(crate) fn calc(&self, kernel: &mut crate::Kernel) -> CalcNames {
        let syntax = self.semantics.syntax;
        let context_ty = kernel.const_(self.context, vec![]);
        let formula_ty = kernel.const_(syntax.formula, vec![]);
        let term_ty = kernel.const_(syntax.term, vec![]);
        CalcNames {
            context_ty,
            formula_ty,
            term_ty,
            provable: self.provable,
            nil: self.nil,
            cons: self.cons,
            context_shift: self.context_shift,
            and_: syntax.and_,
            or_: syntax.or_,
            imp: syntax.imp,
            all: syntax.all,
            ex: syntax.ex,
            eqf: syntax.eqf,
            bot: syntax.bot,
            formula_subst: syntax.formula_subst,
            formula_shift: syntax.formula_shift,
            subst_cons: syntax.subst_cons,
            subst_id: syntax.subst_id,
        }
    }
}

/// Build `FO.Context`, `FO.ctxSat`, the `FO.Provable` calculus and the three
/// example derivations.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_provable_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoProvablePrelude, KernelError> {
    let semantics = build_fo_semantics_prelude(kernel)?;
    let syntax = semantics.syntax;
    let syn = syntax.names(kernel);
    let zero_lvl = kernel.level_zero();
    let one = kernel.level_succ(zero_lvl);

    // --- FO.Context : Type, nil | cons (head : Formula) (tail : Context) -----
    let context = kernel.name_str(syn.fo, "Context");
    let nil = kernel.name_str(context, "nil");
    let cons = kernel.name_str(context, "cons");
    let family = kernel.add_recursive_datatype_family(
        context,
        syn.formula_ty,
        one,
        &[
            (nil, vec![]),
            (cons, vec![RecField::Carrier, RecField::Recursive]),
        ],
    )?;
    let context_rec = family.rec;
    let context_ty = kernel.const_(context, vec![]);

    let context_shift = declare_context_shift(
        kernel,
        &syn,
        context,
        context_ty,
        context_rec,
        nil,
        cons,
        syntax.formula_shift,
        one,
    )?;
    let ctx_sat = declare_ctx_sat(kernel, &syn, &semantics, context_ty, context_rec, one)?;

    // --- FO.Provable : Context -> Formula -> Prop ----------------------------
    let provable = kernel.name_str(syn.fo, "Provable");
    let names: [&str; 16] = [
        "ax_head",
        "weaken",
        "and_intro",
        "and_elim1",
        "and_elim2",
        "or_intro1",
        "or_intro2",
        "or_elim",
        "imp_intro",
        "imp_elim",
        "bot_elim",
        "all_intro",
        "all_elim",
        "ex_intro",
        "ex_elim",
        "eqf_refl",
    ];
    let mut rules = [nil; 16];
    for (slot, label) in rules.iter_mut().zip(names) {
        *slot = kernel.name_str(provable, label);
    }

    let c = CalcNames {
        context_ty,
        formula_ty: syn.formula_ty,
        term_ty: syn.term_ty,
        provable,
        nil,
        cons,
        context_shift,
        and_: syn.and_,
        or_: syn.or_,
        imp: syn.imp,
        all: syn.all,
        ex: syn.ex,
        eqf: syn.eqf,
        bot: syn.bot,
        formula_subst: syntax.formula_subst,
        formula_shift: syntax.formula_shift,
        subst_cons: syntax.subst_cons,
        subst_id: syntax.subst_id,
    };

    let provable_ty = {
        let prop = kernel.sort_zero();
        let inner = arrow(kernel, syn.formula_ty, prop);
        arrow(kernel, context_ty, inner)
    };
    let ctor_decls: Vec<(NameId, ExprId)> = rules
        .iter()
        .enumerate()
        .map(|(i, &name)| (name, rule_type(kernel, &c, i)))
        .collect();
    kernel.add_inductive(provable, &[], 0, provable_ty, &ctor_decls)?;
    let provable_rec = kernel.name_str(provable, "rec");

    let provable_imp_self = declare_imp_self(kernel, &syn, &c, &rules)?;
    let provable_all_imp_self = declare_all_imp_self(kernel, &syn, &c, &rules)?;
    let provable_all_imp_ex = declare_all_imp_ex(kernel, &syn, &c, &rules)?;

    Ok(FoProvablePrelude {
        semantics,
        context,
        nil,
        cons,
        context_rec,
        context_shift,
        ctx_sat,
        provable,
        provable_rec,
        rules,
        provable_imp_self,
        provable_all_imp_self,
        provable_all_imp_ex,
    })
}

// ============================================================================
// FO.Context.shift and FO.ctxSat.
// ============================================================================

/// `FO.Context.shift : Context -> Context`, mapping `FO.Formula.shift` over
/// every entry. This is the operation the eigenvariable condition is stated
/// with; see the module docs.
#[allow(clippy::too_many_arguments)]
fn declare_context_shift(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    context: NameId,
    context_ty: ExprId,
    context_rec: NameId,
    nil: NameId,
    cons: NameId,
    formula_shift: NameId,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let anon = kernel.anon();
    let motive = kernel.lam(anon, context_ty, context_ty, BinderInfo::Default);

    let m_nil = kernel.const_(nil, vec![]);

    let m_cons = {
        let a_id = 1_636_801_u64;
        let l_id = 1_636_802_u64;
        let ih_id = 1_636_803_u64;
        let a = kernel.fvar(a_id);
        let ih = kernel.fvar(ih_id);
        let fshift = kernel.const_(formula_shift, vec![]);
        let head = kernel.app(fshift, a);
        let cons_const = kernel.const_(cons, vec![]);
        let body = apply_all(kernel, cons_const, &[head, ih]);
        lams(
            kernel,
            &[
                (a_id, syn.formula_ty),
                (l_id, context_ty),
                (ih_id, context_ty),
            ],
            body,
        )
    };

    let rec_const = kernel.const_(context_rec, vec![one]);
    let applied = apply_all(kernel, rec_const, &[motive, m_nil, m_cons]);

    let g_id = 1_636_811_u64;
    let g = kernel.fvar(g_id);
    let body = kernel.app(applied, g);
    let value = lam_fv(kernel, g_id, context_ty, body);
    let ty = arrow(kernel, context_ty, context_ty);

    let name = kernel.name_str(context, "shift");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.ctxSat : Π (M : Type) (S : FO.Structure M), Context -> (Nat -> M) -> Prop`,
/// a `FO.Context.rec` application at the motive `fun _ => (Nat -> M) -> Prop`:
/// `True` at `nil`, `And (sat a v) (ih v)` at `cons a l`.
fn declare_ctx_sat(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    semantics: &FoSemanticsPrelude,
    context_ty: ExprId,
    context_rec: NameId,
    one: LevelId,
) -> Result<NameId, KernelError> {
    let logic = semantics.syntax.nat.logic;
    let type_sort = kernel.sort(one);
    let prop = kernel.sort_zero();

    let m_id = 1_636_821_u64;
    let s_id = 1_636_822_u64;
    let m = kernel.fvar(m_id);
    let s = kernel.fvar(s_id);

    let structure_const = kernel.const_(semantics.structure, vec![]);
    let struct_m = kernel.app(structure_const, m);

    let val_ty = arrow(kernel, syn.nat_ty, m);
    let codomain = arrow(kernel, val_ty, prop);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, context_ty, codomain, BinderInfo::Default);

    let m_nil = {
        let v_id = 1_636_831_u64;
        let true_ = kernel.const_(logic.true_, vec![]);
        lam_fv(kernel, v_id, val_ty, true_)
    };

    let m_cons = {
        let a_id = 1_636_841_u64;
        let l_id = 1_636_842_u64;
        let ih_id = 1_636_843_u64;
        let v_id = 1_636_844_u64;
        let a = kernel.fvar(a_id);
        let ih = kernel.fvar(ih_id);
        let v = kernel.fvar(v_id);
        let sat_const = kernel.const_(semantics.sat, vec![]);
        let head = apply_all(kernel, sat_const, &[m, s, a, v]);
        let tail = kernel.app(ih, v);
        let and_const = kernel.const_(logic.and, vec![]);
        let body = apply_all(kernel, and_const, &[head, tail]);
        lams(
            kernel,
            &[
                (a_id, syn.formula_ty),
                (l_id, context_ty),
                (ih_id, codomain),
                (v_id, val_ty),
            ],
            body,
        )
    };

    let rec_const = kernel.const_(context_rec, vec![one]);
    let applied = apply_all(kernel, rec_const, &[motive, m_nil, m_cons]);

    let g_id = 1_636_851_u64;
    let g = kernel.fvar(g_id);
    let inner = kernel.app(applied, g);
    let with_ctx = lam_fv(kernel, g_id, context_ty, inner);

    let binders = [(m_id, type_sort), (s_id, struct_m)];
    let value = lams(kernel, &binders, with_ctx);
    let cod = arrow(kernel, context_ty, codomain);
    let ty = pis(kernel, &binders, cod);

    let name = kernel.name_str(syn.fo, "ctxSat");
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
// The sixteen rule types.
// ============================================================================

pub(crate) fn provable_app(
    kernel: &mut crate::Kernel,
    c: &CalcNames,
    ctx: ExprId,
    phi: ExprId,
) -> ExprId {
    let head = kernel.const_(c.provable, vec![]);
    apply_all(kernel, head, &[ctx, phi])
}

pub(crate) fn cons_app(
    kernel: &mut crate::Kernel,
    c: &CalcNames,
    head: ExprId,
    tail: ExprId,
) -> ExprId {
    let ctor = kernel.const_(c.cons, vec![]);
    apply_all(kernel, ctor, &[head, tail])
}

pub(crate) fn ctx_shift_app(kernel: &mut crate::Kernel, c: &CalcNames, g: ExprId) -> ExprId {
    let head = kernel.const_(c.context_shift, vec![]);
    kernel.app(head, g)
}

pub(crate) fn f_shift_app(kernel: &mut crate::Kernel, c: &CalcNames, p: ExprId) -> ExprId {
    let head = kernel.const_(c.formula_shift, vec![]);
    kernel.app(head, p)
}

/// `FO.Formula.subst p (FO.Subst.cons t FO.Subst.id)` — the de Bruijn spelling
/// of `p[t/x]`.
pub(crate) fn instantiate(
    kernel: &mut crate::Kernel,
    c: &CalcNames,
    p: ExprId,
    t: ExprId,
) -> ExprId {
    let id = kernel.const_(c.subst_id, vec![]);
    let cons = kernel.const_(c.subst_cons, vec![]);
    let sigma = apply_all(kernel, cons, &[t, id]);
    let subst = kernel.const_(c.formula_subst, vec![]);
    apply_all(kernel, subst, &[p, sigma])
}

fn binary_formula(kernel: &mut crate::Kernel, ctor: NameId, a: ExprId, b: ExprId) -> ExprId {
    let head = kernel.const_(ctor, vec![]);
    apply_all(kernel, head, &[a, b])
}

fn unary_formula(kernel: &mut crate::Kernel, ctor: NameId, a: ExprId) -> ExprId {
    let head = kernel.const_(ctor, vec![]);
    kernel.app(head, a)
}

/// Build the type of rule `index` (see the [`rule`] index constants and the
/// module docs' rule table).
#[allow(clippy::too_many_lines)]
fn rule_type(kernel: &mut crate::Kernel, c: &CalcNames, index: usize) -> ExprId {
    // Distinct fvar blocks per rule so two rules never share an id.
    let base = 1_637_000_u64 + 10 * index as u64;
    let g_id = base;
    let p_id = base + 1;
    let q_id = base + 2;
    let r_id = base + 3;
    let t_id = base + 4;

    let g = kernel.fvar(g_id);
    let p = kernel.fvar(p_id);
    let q = kernel.fvar(q_id);
    let r = kernel.fvar(r_id);
    let t = kernel.fvar(t_id);

    let ctx = c.context_ty;
    let fml = c.formula_ty;
    let trm = c.term_ty;

    match index {
        // ax_head : Π g p, Provable (cons p g) p
        rule::AX_HEAD => {
            let extended = cons_app(kernel, c, p, g);
            let concl = provable_app(kernel, c, extended, p);
            pis(kernel, &[(g_id, ctx), (p_id, fml)], concl)
        }
        // weaken : Π g p q, Provable g p -> Provable (cons q g) p
        rule::WEAKEN => {
            let hyp = provable_app(kernel, c, g, p);
            let extended = cons_app(kernel, c, q, g);
            let concl = provable_app(kernel, c, extended, p);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // and_intro : Π g p q, Provable g p -> Provable g q -> Provable g (and_ p q)
        rule::AND_INTRO => {
            let h1 = provable_app(kernel, c, g, p);
            let h2 = provable_app(kernel, c, g, q);
            let conj = binary_formula(kernel, c.and_, p, q);
            let concl = provable_app(kernel, c, g, conj);
            let inner = arrow(kernel, h2, concl);
            let body = arrow(kernel, h1, inner);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // and_elim1/2 : Π g p q, Provable g (and_ p q) -> Provable g p (resp. q)
        rule::AND_ELIM1 | rule::AND_ELIM2 => {
            let conj = binary_formula(kernel, c.and_, p, q);
            let hyp = provable_app(kernel, c, g, conj);
            let target = if index == rule::AND_ELIM1 { p } else { q };
            let concl = provable_app(kernel, c, g, target);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // or_intro1/2 : Π g p q, Provable g p (resp. q) -> Provable g (or_ p q)
        rule::OR_INTRO1 | rule::OR_INTRO2 => {
            let source = if index == rule::OR_INTRO1 { p } else { q };
            let hyp = provable_app(kernel, c, g, source);
            let disj = binary_formula(kernel, c.or_, p, q);
            let concl = provable_app(kernel, c, g, disj);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // or_elim : Π g p q r, Provable g (or_ p q) -> Provable (cons p g) r
        //           -> Provable (cons q g) r -> Provable g r
        rule::OR_ELIM => {
            let disj = binary_formula(kernel, c.or_, p, q);
            let h1 = provable_app(kernel, c, g, disj);
            let ctx_p = cons_app(kernel, c, p, g);
            let h2 = provable_app(kernel, c, ctx_p, r);
            let ctx_q = cons_app(kernel, c, q, g);
            let h3 = provable_app(kernel, c, ctx_q, r);
            let concl = provable_app(kernel, c, g, r);
            let inner = arrow(kernel, h3, concl);
            let inner = arrow(kernel, h2, inner);
            let body = arrow(kernel, h1, inner);
            pis(
                kernel,
                &[(g_id, ctx), (p_id, fml), (q_id, fml), (r_id, fml)],
                body,
            )
        }
        // imp_intro : Π g p q, Provable (cons p g) q -> Provable g (imp p q)
        rule::IMP_INTRO => {
            let ctx_p = cons_app(kernel, c, p, g);
            let hyp = provable_app(kernel, c, ctx_p, q);
            let implication = binary_formula(kernel, c.imp, p, q);
            let concl = provable_app(kernel, c, g, implication);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // imp_elim : Π g p q, Provable g (imp p q) -> Provable g p -> Provable g q
        rule::IMP_ELIM => {
            let implication = binary_formula(kernel, c.imp, p, q);
            let h1 = provable_app(kernel, c, g, implication);
            let h2 = provable_app(kernel, c, g, p);
            let concl = provable_app(kernel, c, g, q);
            let inner = arrow(kernel, h2, concl);
            let body = arrow(kernel, h1, inner);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // bot_elim : Π g p, Provable g bot -> Provable g p
        rule::BOT_ELIM => {
            let bot = kernel.const_(c.bot, vec![]);
            let hyp = provable_app(kernel, c, g, bot);
            let concl = provable_app(kernel, c, g, p);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml)], body)
        }
        // all_intro : Π g p, Provable (Context.shift g) p -> Provable g (all p)
        rule::ALL_INTRO => {
            let shifted = ctx_shift_app(kernel, c, g);
            let hyp = provable_app(kernel, c, shifted, p);
            let quantified = unary_formula(kernel, c.all, p);
            let concl = provable_app(kernel, c, g, quantified);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml)], body)
        }
        // all_elim : Π g p t, Provable g (all p) -> Provable g (p[t])
        rule::ALL_ELIM => {
            let quantified = unary_formula(kernel, c.all, p);
            let hyp = provable_app(kernel, c, g, quantified);
            let instance = instantiate(kernel, c, p, t);
            let concl = provable_app(kernel, c, g, instance);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (t_id, trm)], body)
        }
        // ex_intro : Π g p t, Provable g (p[t]) -> Provable g (ex p)
        rule::EX_INTRO => {
            let instance = instantiate(kernel, c, p, t);
            let hyp = provable_app(kernel, c, g, instance);
            let quantified = unary_formula(kernel, c.ex, p);
            let concl = provable_app(kernel, c, g, quantified);
            let body = arrow(kernel, hyp, concl);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (t_id, trm)], body)
        }
        // ex_elim : Π g p q, Provable g (ex p)
        //           -> Provable (cons p (Context.shift g)) (Formula.shift q)
        //           -> Provable g q
        rule::EX_ELIM => {
            let quantified = unary_formula(kernel, c.ex, p);
            let h1 = provable_app(kernel, c, g, quantified);
            let shifted_ctx = ctx_shift_app(kernel, c, g);
            let extended = cons_app(kernel, c, p, shifted_ctx);
            let shifted_goal = f_shift_app(kernel, c, q);
            let h2 = provable_app(kernel, c, extended, shifted_goal);
            let concl = provable_app(kernel, c, g, q);
            let inner = arrow(kernel, h2, concl);
            let body = arrow(kernel, h1, inner);
            pis(kernel, &[(g_id, ctx), (p_id, fml), (q_id, fml)], body)
        }
        // eqf_refl : Π g t, Provable g (eqf t t)
        _ => {
            let atom = binary_formula(kernel, c.eqf, t, t);
            let concl = provable_app(kernel, c, g, atom);
            pis(kernel, &[(g_id, ctx), (t_id, trm)], concl)
        }
    }
}

// ============================================================================
// Three example derivations.
// ============================================================================

/// The closed atomic formula `FO.Formula.rel1 0 (FO.Term.f0 0)`, used as the
/// propositional variable of the example derivations. It is closed (no `var`),
/// so `Formula.shift` fixes it and the derivations below stay small.
pub(crate) fn example_atom(kernel: &mut crate::Kernel, syn: &SyntaxNames) -> ExprId {
    let zero = kernel.const_(syn.nat_zero, vec![]);
    let f0 = kernel.const_(syn.f0, vec![]);
    let constant = kernel.app(f0, zero);
    let zero2 = kernel.const_(syn.nat_zero, vec![]);
    let rel1 = kernel.const_(syn.rel1, vec![]);
    apply_all(kernel, rel1, &[zero2, constant])
}

/// `FO.provable_imp_self : Provable nil (imp a a)` where `a` is
/// [`example_atom`], proved by `imp_intro nil a a (ax_head nil a)`.
fn declare_imp_self(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    c: &CalcNames,
    rules: &[NameId; 16],
) -> Result<NameId, KernelError> {
    let nil = kernel.const_(c.nil, vec![]);
    let a = example_atom(kernel, syn);

    let ax_head = kernel.const_(rules[rule::AX_HEAD], vec![]);
    let assumption = apply_all(kernel, ax_head, &[nil, a]);
    let imp_intro = kernel.const_(rules[rule::IMP_INTRO], vec![]);
    let value = apply_all(kernel, imp_intro, &[nil, a, a, assumption]);

    let self_imp = binary_formula(kernel, c.imp, a, a);
    let ty = provable_app(kernel, c, nil, self_imp);

    let name = kernel.name_str(syn.fo, "provable_imp_self");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.provable_all_imp_self : Provable nil (all (imp a a))`, proved by
/// `all_intro nil (imp a a) (imp_intro …)`.
///
/// `all_intro`'s premise is over `Context.shift nil`, which ι-reduces to
/// `nil` — so the propositional derivation is reusable verbatim, and the
/// kernel accepting this term is a check that `Context.shift` really does
/// compute at `nil`.
fn declare_all_imp_self(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    c: &CalcNames,
    rules: &[NameId; 16],
) -> Result<NameId, KernelError> {
    let nil = kernel.const_(c.nil, vec![]);
    let a = example_atom(kernel, syn);
    let self_imp = binary_formula(kernel, c.imp, a, a);

    // The inner derivation is built over `nil`, NOT over `Context.shift nil`,
    // so admitting `all_intro nil _ inner` forces the kernel to reduce
    // `Context.shift FO.Context.nil` to `FO.Context.nil` by delta + iota. A
    // `Context.shift` that returned something else at `nil` is rejected here.
    let ax_head = kernel.const_(rules[rule::AX_HEAD], vec![]);
    let assumption = apply_all(kernel, ax_head, &[nil, a]);
    let imp_intro = kernel.const_(rules[rule::IMP_INTRO], vec![]);
    let inner = apply_all(kernel, imp_intro, &[nil, a, a, assumption]);

    let all_intro = kernel.const_(rules[rule::ALL_INTRO], vec![]);
    let value = apply_all(kernel, all_intro, &[nil, self_imp, inner]);

    let quantified = unary_formula(kernel, c.all, self_imp);
    let ty = provable_app(kernel, c, nil, quantified);

    let name = kernel.name_str(syn.fo, "provable_all_imp_self");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `FO.provable_all_imp_ex : Provable nil (imp (all p) (ex p))` for
/// `p := rel1 0 (var 0)` — the genuinely first-order derivation, using
/// `all_elim` and `ex_intro` at the same instance term `FO.Term.f0 0`:
///
/// ```text
/// imp_intro nil (all p) (ex p)
///   (ex_intro (cons (all p) nil) p t
///     (all_elim (cons (all p) nil) p t
///       (ax_head nil (all p))))
/// ```
fn declare_all_imp_ex(
    kernel: &mut crate::Kernel,
    syn: &SyntaxNames,
    c: &CalcNames,
    rules: &[NameId; 16],
) -> Result<NameId, KernelError> {
    let nil = kernel.const_(c.nil, vec![]);

    // p := rel1 0 (var 0) — an atom with a genuinely free de Bruijn index, so
    // both quantifier rules do real work.
    let p = {
        let zero = kernel.const_(syn.nat_zero, vec![]);
        let var = kernel.const_(syn.var, vec![]);
        let v0 = kernel.app(var, zero);
        let zero2 = kernel.const_(syn.nat_zero, vec![]);
        let rel1 = kernel.const_(syn.rel1, vec![]);
        apply_all(kernel, rel1, &[zero2, v0])
    };
    // t := f0 0, a closed instance term.
    let t = {
        let zero = kernel.const_(syn.nat_zero, vec![]);
        let f0 = kernel.const_(syn.f0, vec![]);
        kernel.app(f0, zero)
    };

    let universal = unary_formula(kernel, c.all, p);
    let existential = unary_formula(kernel, c.ex, p);
    let ctx = cons_app(kernel, c, universal, nil);

    let ax_head = kernel.const_(rules[rule::AX_HEAD], vec![]);
    let assumption = apply_all(kernel, ax_head, &[nil, universal]);

    let all_elim = kernel.const_(rules[rule::ALL_ELIM], vec![]);
    let instance = apply_all(kernel, all_elim, &[ctx, p, t, assumption]);

    let ex_intro = kernel.const_(rules[rule::EX_INTRO], vec![]);
    let witnessed = apply_all(kernel, ex_intro, &[ctx, p, t, instance]);

    let imp_intro = kernel.const_(rules[rule::IMP_INTRO], vec![]);
    let value = apply_all(kernel, imp_intro, &[nil, universal, existential, witnessed]);

    let implication = binary_formula(kernel, c.imp, universal, existential);
    let ty = provable_app(kernel, c, nil, implication);

    let name = kernel.name_str(syn.fo, "provable_all_imp_ex");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests;
