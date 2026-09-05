//! **Slice 5, the last one** of the first-order model theory group
//! (`fo_*.rs`, ADR-1636): **soundness** of `FO.Provable` with respect to
//! Tarski satisfaction, and the consistency corollary it buys.
//!
//! ```text
//! FO.ctxSat_shift : Π M S g w (a : M),
//!      FO.ctxSat M S g w -> FO.ctxSat M S (FO.Context.shift g) (FO.Val.cons M a w)
//!
//! FO.soundness : Π (M : Type) (S : FO.Structure M) (g : FO.Context) (p : FO.Formula),
//!      FO.Provable g p -> Π (w : Nat -> M), FO.ctxSat M S g w -> FO.sat M S p w
//!
//! FO.consistency : Not (FO.Provable FO.Context.nil FO.Formula.bot)
//! ```
//!
//! ## The statement, and why it is the obvious one this time
//!
//! `ipc_soundness.rs` could **not** state soundness as "every valuation
//! satisfying the context satisfies the goal": over its 3-element Heyting
//! chain that statement carries no induction through `imp_intro`, and it had
//! to be replaced by an inequality over the *meet* of the context, with the
//! sat-shaped version recovered afterwards as a corollary.
//!
//! Here the sat-shaped statement is the one that works, and the reason is that
//! `FO.sat` lands in `Prop` rather than in a chain: `FO.sat M S (imp p q) w`
//! **is** the kernel's own function type `FO.sat M S p w -> FO.sat M S q w`,
//! so `imp_intro`'s minor is a lambda and `imp_elim`'s is an application.
//! Nine of the sixteen minors below are one line for the same reason —
//! `And.intro`, `And.left`, `Or.inl`, `Or.elim`, `False.rec`, `Eq.refl` — with
//! no algebra layer in between.
//!
//! ## The five that carry the content
//!
//! | rule | closed by |
//! | --- | --- |
//! | `all_intro` | `FO.ctxSat_shift` |
//! | `all_elim` | `FO.sat_inst` (backward) |
//! | `ex_intro` | `FO.sat_inst` (forward) + `Exists.intro` |
//! | `ex_elim` | `Exists.rec` + `FO.ctxSat_shift` + `FO.sat_shift` (forward) |
//! | `eqf_refl` | `Eq.refl` |
//!
//! `all_intro` is where the eigenvariable condition is paid for. Its premise
//! is a derivation over `FO.Context.shift g`, so the induction hypothesis is
//! `Π w, ctxSat (Context.shift g) w -> sat p w` — available at **any**
//! valuation, in particular at `FO.Val.cons M z w` for the freshly universally
//! quantified `z`. `FO.ctxSat_shift` supplies the hypothesis at that
//! valuation, and it is itself a `Context.rec` induction whose `cons` case is
//! one application of `FO.sat_shift`'s backward direction. Had the rule's
//! premise been over the *unshifted* `g`, the induction hypothesis would only
//! constrain `w`, and there would be nothing to feed the goal at
//! `Val.cons M z w` — which is exactly why that mutation is unsound and why
//! `fo_provable.rs`'s module test pins the rule's shape.
//!
//! `ex_elim` uses both halves of its own condition: `FO.ctxSat_shift` for the
//! context half and `FO.sat_shift` for the conclusion half. Removing either
//! leaves the minor unbuildable.
//!
//! ## Consistency, via ℕ
//!
//! ```text
//! FO.consistency : Not (FO.Provable FO.Context.nil FO.Formula.bot)
//! ```
//!
//! The proof is one line and it is worth reading, because it is the whole
//! point of having a *model*:
//!
//! ```text
//! fun d => FO.soundness Nat FO.natStructure FO.Context.nil FO.Formula.bot d
//!            (fun _ => Nat.zero) True.intro
//! ```
//!
//! Soundness sends the assumed derivation to `FO.sat Nat FO.natStructure bot v`
//! at the constant-zero valuation; the empty context's `ctxSat` ι-reduces to
//! `True`, discharged by `True.intro`; and `FO.sat _ _ bot _` ι-reduces to
//! `False`. So a derivation of `⊥` from nothing yields `False`. The ℕ
//! structure is doing real work here — an arbitrary `FO.Structure M` would
//! not do, because `M` could be empty and the argument still needs a
//! valuation `Nat -> M` to exist. Using a structure whose carrier is
//! inhabited is what makes the corollary constructive.
//!
//! This is the first-order analogue of `ipc_soundness.rs`'s
//! `ipc_excluded_middle_not_provable`, and the same shape of result: a
//! **negative** fact about a proof system, obtained by pushing a derivation
//! through a model.

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

use crate::fo_provable::{CalcNames, cons_app, ctx_shift_app, f_shift_app, instantiate, rule};
use crate::fo_substitution::declare_fo_substitution_over;
use crate::fo_syntax::SyntaxNames;
use crate::fo_syntax::{apply_all, arrow, iff_mp, iff_mpr, lam_fv, lams, pi_fv, pis};
use crate::{
    BinderInfo, Declaration, ExprId, FoProvablePrelude, FoSubstitutionPrelude, KernelError,
    LevelId, LogicPrelude, NameId, build_fo_provable_prelude,
};

/// Names produced by [`build_fo_soundness_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoSoundnessPrelude {
    /// `FO.Context`, `FO.ctxSat` and the `FO.Provable` calculus.
    pub calculus: FoProvablePrelude,
    /// The substitution lemma package.
    pub substitution: FoSubstitutionPrelude,
    /// `FO.ctxSat_shift`.
    pub ctx_sat_shift: NameId,
    /// `FO.soundness`.
    pub soundness: NameId,
    /// `FO.consistency : Not (Provable nil bot)`.
    pub consistency: NameId,
}

/// Build `FO.ctxSat_shift`, `FO.soundness` and `FO.consistency`.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_soundness_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoSoundnessPrelude, KernelError> {
    let calculus = build_fo_provable_prelude(kernel)?;
    // NOT `build_fo_substitution_prelude`: that would re-run
    // `build_fo_semantics_prelude`, and the trusted gate refuses the second
    // `FO.Structure` with `DeclarationExists`. Both packages sit on the ONE
    // semantics prelude the calculus already built.
    let substitution = declare_fo_substitution_over(kernel, &calculus.semantics)?;
    let env = SoundEnv::new(kernel, &calculus, &substitution);
    let ctx_sat_shift = declare_ctx_sat_shift(kernel, &env)?;
    let soundness = declare_soundness(kernel, &env, ctx_sat_shift)?;
    let consistency = declare_consistency(kernel, &env, soundness)?;
    Ok(FoSoundnessPrelude {
        calculus,
        substitution,
        ctx_sat_shift,
        soundness,
        consistency,
    })
}

/// The ambient context for the two inductions: the interned names, the fixed
/// levels, and the `M` / `S` free variables every statement is quantified
/// over.
struct SoundEnv {
    logic: LogicPrelude,
    syn: SyntaxNames,
    calc: CalcNames,
    calculus: FoProvablePrelude,
    subst: FoSubstitutionPrelude,
    type_sort: ExprId,
    one: LevelId,
    zero: LevelId,
    m_id: u64,
    s_id: u64,
    m: ExprId,
    s: ExprId,
    struct_m: ExprId,
    val_ty: ExprId,
}

impl SoundEnv {
    fn new(
        kernel: &mut crate::Kernel,
        calculus: &FoProvablePrelude,
        subst: &FoSubstitutionPrelude,
    ) -> Self {
        let syntax = calculus.semantics.syntax;
        let syn = syntax.names(kernel);
        let calc = calculus.calc(kernel);
        let logic = syntax.nat.logic;
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let type_sort = kernel.sort(one);

        let m_id = 1_642_001_u64;
        let s_id = 1_642_002_u64;
        let m = kernel.fvar(m_id);
        let s = kernel.fvar(s_id);
        let structure_const = kernel.const_(calculus.semantics.structure, vec![]);
        let struct_m = kernel.app(structure_const, m);
        let val_ty = arrow(kernel, syn.nat_ty, m);

        Self {
            logic,
            syn,
            calc,
            calculus: *calculus,
            subst: *subst,
            type_sort,
            one,
            zero,
            m_id,
            s_id,
            m,
            s,
            struct_m,
            val_ty,
        }
    }

    fn ambient(&self) -> [(u64, ExprId); 2] {
        [(self.m_id, self.type_sort), (self.s_id, self.struct_m)]
    }
}

/// `FO.sat M S p w`.
fn sat_of(kernel: &mut crate::Kernel, e: &SoundEnv, p: ExprId, w: ExprId) -> ExprId {
    let c = kernel.const_(e.calculus.semantics.sat, vec![]);
    apply_all(kernel, c, &[e.m, e.s, p, w])
}

/// `FO.ctxSat M S g w`.
fn ctx_sat_of(kernel: &mut crate::Kernel, e: &SoundEnv, g: ExprId, w: ExprId) -> ExprId {
    let c = kernel.const_(e.calculus.ctx_sat, vec![]);
    apply_all(kernel, c, &[e.m, e.s, g, w])
}

/// `FO.Val.cons M a w`.
fn vcons(kernel: &mut crate::Kernel, e: &SoundEnv, a: ExprId, w: ExprId) -> ExprId {
    let c = kernel.const_(e.calculus.semantics.val_cons, vec![]);
    apply_all(kernel, c, &[e.m, a, w])
}

/// `FO.Term.eval M S t w`.
fn ev(kernel: &mut crate::Kernel, e: &SoundEnv, t: ExprId, w: ExprId) -> ExprId {
    let c = kernel.const_(e.calculus.semantics.term_eval, vec![]);
    apply_all(kernel, c, &[e.m, e.s, t, w])
}

/// `And.intro a b ha hb`.
fn and_intro(
    kernel: &mut crate::Kernel,
    e: &SoundEnv,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let c = kernel.const_(e.logic.and_intro, vec![]);
    apply_all(kernel, c, &[a, b, ha, hb])
}

/// `And.left a b h`.
fn and_left(kernel: &mut crate::Kernel, e: &SoundEnv, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let c = kernel.const_(e.logic.and_left, vec![]);
    apply_all(kernel, c, &[a, b, h])
}

/// `And.right a b h`.
fn and_right(kernel: &mut crate::Kernel, e: &SoundEnv, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let c = kernel.const_(e.logic.and_right, vec![]);
    apply_all(kernel, c, &[a, b, h])
}

/// A `Formula` constructor applied to one or two arguments.
fn fapp(kernel: &mut crate::Kernel, ctor: NameId, args: &[ExprId]) -> ExprId {
    let c = kernel.const_(ctor, vec![]);
    apply_all(kernel, c, args)
}

// ============================================================================
// FO.ctxSat_shift
// ============================================================================

/// `FO.ctxSat_shift : Π M S g w (a : M),
/// ctxSat M S g w -> ctxSat M S (Context.shift g) (Val.cons M a w)`.
///
/// `FO.Context.rec` on the context. `nil` is `True.intro` (both sides
/// ι-reduce to `True`); `cons x l` is `And.intro` of `FO.sat_shift`'s backward
/// direction on the head and the induction hypothesis on the tail.
fn declare_ctx_sat_shift(kernel: &mut crate::Kernel, e: &SoundEnv) -> Result<NameId, KernelError> {
    let base = 1_642_100_u64;
    let ctx_ty = e.calc.context_ty;

    // motive_at g := Π (w : Nat -> M) (a : M),
    //   ctxSat g w -> ctxSat (Context.shift g) (Val.cons M a w)
    let motive_at = |kernel: &mut crate::Kernel, g: ExprId, blk: u64| -> ExprId {
        let w_id = blk;
        let a_id = blk + 1;
        let w = kernel.fvar(w_id);
        let a = kernel.fvar(a_id);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let shifted = ctx_shift_app(kernel, &e.calc, g);
        let extended = vcons(kernel, e, a, w);
        let concl = ctx_sat_of(kernel, e, shifted, extended);
        let body = arrow(kernel, hyp, concl);
        pis(kernel, &[(w_id, e.val_ty), (a_id, e.m)], body)
    };

    let motive = {
        let g_id = base;
        let g = kernel.fvar(g_id);
        let body = motive_at(kernel, g, base + 1);
        lam_fv(kernel, g_id, ctx_ty, body)
    };

    // m_nil := fun w a _ => True.intro
    let m_nil = {
        let blk = base + 10;
        let w_id = blk;
        let a_id = blk + 1;
        let h_id = blk + 2;
        let w = kernel.fvar(w_id);
        let nil = kernel.const_(e.calc.nil, vec![]);
        let hyp = ctx_sat_of(kernel, e, nil, w);
        let body = kernel.const_(e.logic.true_intro, vec![]);
        lams(kernel, &[(w_id, e.val_ty), (a_id, e.m), (h_id, hyp)], body)
    };

    // m_cons := fun x l ih w a h => And.intro _ _ (sat_shift.mpr (h.left)) (ih w a h.right)
    let m_cons = {
        let blk = base + 20;
        let x_id = blk;
        let l_id = blk + 1;
        let ih_id = blk + 2;
        let w_id = blk + 3;
        let a_id = blk + 4;
        let h_id = blk + 5;
        let x = kernel.fvar(x_id);
        let l = kernel.fvar(l_id);
        let ih = kernel.fvar(ih_id);
        let w = kernel.fvar(w_id);
        let a = kernel.fvar(a_id);
        let h = kernel.fvar(h_id);

        let ih_ty = motive_at(kernel, l, blk + 6);
        let entry = cons_app(kernel, &e.calc, x, l);
        let hyp = ctx_sat_of(kernel, e, entry, w);

        let head_sat = sat_of(kernel, e, x, w);
        let tail_sat = ctx_sat_of(kernel, e, l, w);
        let head_proof = and_left(kernel, e, head_sat, tail_sat, h);
        let tail_proof = and_right(kernel, e, head_sat, tail_sat, h);

        let extended = vcons(kernel, e, a, w);
        let shifted_head = f_shift_app(kernel, &e.calc, x);
        let shifted_head_sat = sat_of(kernel, e, shifted_head, extended);
        let head_moved = {
            let c = kernel.const_(e.subst.sat_shift, vec![]);
            let lemma = apply_all(kernel, c, &[e.m, e.s, x, w, a]);
            let mover = iff_mpr(kernel, e.logic, shifted_head_sat, head_sat, lemma);
            kernel.app(mover, head_proof)
        };

        let shifted_tail = ctx_shift_app(kernel, &e.calc, l);
        let shifted_tail_sat = ctx_sat_of(kernel, e, shifted_tail, extended);
        let tail_moved = apply_all(kernel, ih, &[w, a, tail_proof]);

        let body = and_intro(
            kernel,
            e,
            shifted_head_sat,
            shifted_tail_sat,
            head_moved,
            tail_moved,
        );

        lams(
            kernel,
            &[
                (x_id, e.syn.formula_ty),
                (l_id, ctx_ty),
                (ih_id, ih_ty),
                (w_id, e.val_ty),
                (a_id, e.m),
                (h_id, hyp),
            ],
            body,
        )
    };

    let rec_const = kernel.const_(e.calculus.context_rec, vec![e.zero]);
    let applied = apply_all(kernel, rec_const, &[motive, m_nil, m_cons]);

    let g_id = base + 40;
    let g = kernel.fvar(g_id);
    let body = kernel.app(applied, g);
    let value = lam_fv(kernel, g_id, ctx_ty, body);
    let concl = motive_at(kernel, g, base + 41);
    let ty = pi_fv(kernel, g_id, ctx_ty, concl);

    let binders = e.ambient();
    let full_ty = pis(kernel, &binders, ty);
    let full_value = lams(kernel, &binders, value);
    let name = kernel.name_str(e.syn.fo, "ctxSat_shift");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: full_ty,
        value: full_value,
    })?;
    Ok(name)
}

// ============================================================================
// FO.soundness
// ============================================================================

/// `FO.soundness : Π M S g p, FO.Provable g p -> Π w, ctxSat M S g w -> sat M S p w`,
/// by `FO.Provable.rec` — one minor per rule, in declaration order.
fn declare_soundness(
    kernel: &mut crate::Kernel,
    e: &SoundEnv,
    ctx_sat_shift: NameId,
) -> Result<NameId, KernelError> {
    let base = 1_643_000_u64;
    let ctx_ty = e.calc.context_ty;
    let fml = e.calc.formula_ty;
    let trm = e.calc.term_ty;

    // C(g, p) := Π (w : Nat -> M), ctxSat g w -> sat p w
    let carrier = |kernel: &mut crate::Kernel, g: ExprId, p: ExprId, blk: u64| -> ExprId {
        let w_id = blk;
        let w = kernel.fvar(w_id);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let concl = sat_of(kernel, e, p, w);
        let body = arrow(kernel, hyp, concl);
        pi_fv(kernel, w_id, e.val_ty, body)
    };

    // motive := fun g p (_ : Provable g p) => C(g, p)
    let motive = {
        let g_id = base;
        let p_id = base + 1;
        let d_id = base + 2;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let deriv_ty = {
            let c = kernel.const_(e.calc.provable, vec![]);
            apply_all(kernel, c, &[g, p])
        };
        let body = carrier(kernel, g, p, base + 3);
        let inner = lam_fv(kernel, d_id, deriv_ty, body);
        let inner = lam_fv(kernel, p_id, fml, inner);
        lam_fv(kernel, g_id, ctx_ty, inner)
    };

    let prov = |kernel: &mut crate::Kernel, g: ExprId, p: ExprId| -> ExprId {
        let c = kernel.const_(e.calc.provable, vec![]);
        apply_all(kernel, c, &[g, p])
    };

    let mut minors: Vec<ExprId> = Vec::with_capacity(16);

    // ---- 0. ax_head : Π g p, Provable (cons p g) p -------------------------
    minors.push({
        let blk = base + 100;
        let g_id = blk;
        let p_id = blk + 1;
        let w_id = blk + 2;
        let h_id = blk + 3;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let entry = cons_app(kernel, &e.calc, p, g);
        let hyp = ctx_sat_of(kernel, e, entry, w);
        let head = sat_of(kernel, e, p, w);
        let tail = ctx_sat_of(kernel, e, g, w);
        let body = and_left(kernel, e, head, tail, h);
        lams(
            kernel,
            &[(g_id, ctx_ty), (p_id, fml), (w_id, e.val_ty), (h_id, hyp)],
            body,
        )
    });

    // ---- 1. weaken : Π g p q, Provable g p -> Provable (cons q g) p --------
    minors.push({
        let blk = base + 110;
        let g_id = blk;
        let p_id = blk + 1;
        let q_id = blk + 2;
        let d_id = blk + 3;
        let ih_id = blk + 4;
        let w_id = blk + 5;
        let h_id = blk + 6;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let ih = kernel.fvar(ih_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let d_ty = prov(kernel, g, p);
        let ih_ty = carrier(kernel, g, p, blk + 7);
        let entry = cons_app(kernel, &e.calc, q, g);
        let hyp = ctx_sat_of(kernel, e, entry, w);
        let head = sat_of(kernel, e, q, w);
        let tail = ctx_sat_of(kernel, e, g, w);
        let rest = and_right(kernel, e, head, tail, h);
        let body = apply_all(kernel, ih, &[w, rest]);
        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (q_id, fml),
                (d_id, d_ty),
                (ih_id, ih_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 2. and_intro ------------------------------------------------------
    minors.push({
        let blk = base + 120;
        let g_id = blk;
        let p_id = blk + 1;
        let q_id = blk + 2;
        let d1_id = blk + 3;
        let d2_id = blk + 4;
        let i1_id = blk + 5;
        let i2_id = blk + 6;
        let w_id = blk + 7;
        let h_id = blk + 8;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let i1 = kernel.fvar(i1_id);
        let i2 = kernel.fvar(i2_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let d1_ty = prov(kernel, g, p);
        let d2_ty = prov(kernel, g, q);
        let i1_ty = carrier(kernel, g, p, blk + 9);
        let i2_ty = carrier(kernel, g, q, blk + 11);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let sp = sat_of(kernel, e, p, w);
        let sq = sat_of(kernel, e, q, w);
        let hp = apply_all(kernel, i1, &[w, h]);
        let hq = apply_all(kernel, i2, &[w, h]);
        let body = and_intro(kernel, e, sp, sq, hp, hq);
        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (q_id, fml),
                (d1_id, d1_ty),
                (d2_id, d2_ty),
                (i1_id, i1_ty),
                (i2_id, i2_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 3, 4. and_elim1 / and_elim2 ---------------------------------------
    for first in [true, false] {
        minors.push({
            let blk = base + if first { 130 } else { 140 };
            let g_id = blk;
            let p_id = blk + 1;
            let q_id = blk + 2;
            let d_id = blk + 3;
            let i_id = blk + 4;
            let w_id = blk + 5;
            let h_id = blk + 6;
            let g = kernel.fvar(g_id);
            let p = kernel.fvar(p_id);
            let q = kernel.fvar(q_id);
            let i = kernel.fvar(i_id);
            let w = kernel.fvar(w_id);
            let h = kernel.fvar(h_id);
            let conj = fapp(kernel, e.calc.and_, &[p, q]);
            let d_ty = prov(kernel, g, conj);
            let i_ty = carrier(kernel, g, conj, blk + 7);
            let hyp = ctx_sat_of(kernel, e, g, w);
            let sp = sat_of(kernel, e, p, w);
            let sq = sat_of(kernel, e, q, w);
            let both = apply_all(kernel, i, &[w, h]);
            let body = if first {
                and_left(kernel, e, sp, sq, both)
            } else {
                and_right(kernel, e, sp, sq, both)
            };
            lams(
                kernel,
                &[
                    (g_id, ctx_ty),
                    (p_id, fml),
                    (q_id, fml),
                    (d_id, d_ty),
                    (i_id, i_ty),
                    (w_id, e.val_ty),
                    (h_id, hyp),
                ],
                body,
            )
        });
    }

    // ---- 5, 6. or_intro1 / or_intro2 ---------------------------------------
    for first in [true, false] {
        minors.push({
            let blk = base + if first { 150 } else { 160 };
            let g_id = blk;
            let p_id = blk + 1;
            let q_id = blk + 2;
            let d_id = blk + 3;
            let i_id = blk + 4;
            let w_id = blk + 5;
            let h_id = blk + 6;
            let g = kernel.fvar(g_id);
            let p = kernel.fvar(p_id);
            let q = kernel.fvar(q_id);
            let i = kernel.fvar(i_id);
            let w = kernel.fvar(w_id);
            let h = kernel.fvar(h_id);
            let source = if first { p } else { q };
            let d_ty = prov(kernel, g, source);
            let i_ty = carrier(kernel, g, source, blk + 7);
            let hyp = ctx_sat_of(kernel, e, g, w);
            let sp = sat_of(kernel, e, p, w);
            let sq = sat_of(kernel, e, q, w);
            let proof = apply_all(kernel, i, &[w, h]);
            let ctor = if first {
                e.logic.or_inl
            } else {
                e.logic.or_inr
            };
            let c = kernel.const_(ctor, vec![]);
            let body = apply_all(kernel, c, &[sp, sq, proof]);
            lams(
                kernel,
                &[
                    (g_id, ctx_ty),
                    (p_id, fml),
                    (q_id, fml),
                    (d_id, d_ty),
                    (i_id, i_ty),
                    (w_id, e.val_ty),
                    (h_id, hyp),
                ],
                body,
            )
        });
    }

    // ---- 7. or_elim --------------------------------------------------------
    minors.push({
        let blk = base + 170;
        let g_id = blk;
        let p_id = blk + 1;
        let q_id = blk + 2;
        let r_id = blk + 3;
        let d1_id = blk + 4;
        let d2_id = blk + 5;
        let d3_id = blk + 6;
        let i1_id = blk + 7;
        let i2_id = blk + 8;
        let i3_id = blk + 9;
        let w_id = blk + 10;
        let h_id = blk + 11;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let r = kernel.fvar(r_id);
        let i1 = kernel.fvar(i1_id);
        let i2 = kernel.fvar(i2_id);
        let i3 = kernel.fvar(i3_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);

        let disj = fapp(kernel, e.calc.or_, &[p, q]);
        let d1_ty = prov(kernel, g, disj);
        let ctx_p = cons_app(kernel, &e.calc, p, g);
        let ctx_q = cons_app(kernel, &e.calc, q, g);
        let d2_ty = prov(kernel, ctx_p, r);
        let d3_ty = prov(kernel, ctx_q, r);
        let i1_ty = carrier(kernel, g, disj, blk + 12);
        let i2_ty = carrier(kernel, ctx_p, r, blk + 14);
        let i3_ty = carrier(kernel, ctx_q, r, blk + 16);
        let hyp = ctx_sat_of(kernel, e, g, w);

        let sp = sat_of(kernel, e, p, w);
        let sq = sat_of(kernel, e, q, w);
        let sr = sat_of(kernel, e, r, w);
        let ctx_ok = ctx_sat_of(kernel, e, g, w);
        let major = apply_all(kernel, i1, &[w, h]);

        let left_branch = {
            let hp_id = blk + 20;
            let hp = kernel.fvar(hp_id);
            let extended = and_intro(kernel, e, sp, ctx_ok, hp, h);
            let body = apply_all(kernel, i2, &[w, extended]);
            lam_fv(kernel, hp_id, sp, body)
        };
        let right_branch = {
            let hq_id = blk + 21;
            let hq = kernel.fvar(hq_id);
            let extended = and_intro(kernel, e, sq, ctx_ok, hq, h);
            let body = apply_all(kernel, i3, &[w, extended]);
            lam_fv(kernel, hq_id, sq, body)
        };
        let elim = kernel.const_(e.logic.or_elim, vec![]);
        let body = apply_all(
            kernel,
            elim,
            &[sp, sq, sr, major, left_branch, right_branch],
        );

        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (q_id, fml),
                (r_id, fml),
                (d1_id, d1_ty),
                (d2_id, d2_ty),
                (d3_id, d3_ty),
                (i1_id, i1_ty),
                (i2_id, i2_ty),
                (i3_id, i3_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 8. imp_intro ------------------------------------------------------
    minors.push({
        let blk = base + 190;
        let g_id = blk;
        let p_id = blk + 1;
        let q_id = blk + 2;
        let d_id = blk + 3;
        let i_id = blk + 4;
        let w_id = blk + 5;
        let h_id = blk + 6;
        let hp_id = blk + 7;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let i = kernel.fvar(i_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let hp = kernel.fvar(hp_id);
        let ctx_p = cons_app(kernel, &e.calc, p, g);
        let d_ty = prov(kernel, ctx_p, q);
        let i_ty = carrier(kernel, ctx_p, q, blk + 8);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let sp = sat_of(kernel, e, p, w);
        let ctx_ok = ctx_sat_of(kernel, e, g, w);
        let extended = and_intro(kernel, e, sp, ctx_ok, hp, h);
        let applied = apply_all(kernel, i, &[w, extended]);
        let body = lam_fv(kernel, hp_id, sp, applied);
        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (q_id, fml),
                (d_id, d_ty),
                (i_id, i_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 9. imp_elim -------------------------------------------------------
    minors.push({
        let blk = base + 200;
        let g_id = blk;
        let p_id = blk + 1;
        let q_id = blk + 2;
        let d1_id = blk + 3;
        let d2_id = blk + 4;
        let i1_id = blk + 5;
        let i2_id = blk + 6;
        let w_id = blk + 7;
        let h_id = blk + 8;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let i1 = kernel.fvar(i1_id);
        let i2 = kernel.fvar(i2_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let implication = fapp(kernel, e.calc.imp, &[p, q]);
        let d1_ty = prov(kernel, g, implication);
        let d2_ty = prov(kernel, g, p);
        let i1_ty = carrier(kernel, g, implication, blk + 9);
        let i2_ty = carrier(kernel, g, p, blk + 11);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let f = apply_all(kernel, i1, &[w, h]);
        let x = apply_all(kernel, i2, &[w, h]);
        let body = kernel.app(f, x);
        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (q_id, fml),
                (d1_id, d1_ty),
                (d2_id, d2_ty),
                (i1_id, i1_ty),
                (i2_id, i2_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 10. bot_elim ------------------------------------------------------
    minors.push({
        let blk = base + 210;
        let g_id = blk;
        let p_id = blk + 1;
        let d_id = blk + 2;
        let i_id = blk + 3;
        let w_id = blk + 4;
        let h_id = blk + 5;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let i = kernel.fvar(i_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let bot = kernel.const_(e.calc.bot, vec![]);
        let d_ty = prov(kernel, g, bot);
        let i_ty = carrier(kernel, g, bot, blk + 6);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let absurd = apply_all(kernel, i, &[w, h]);
        let target = sat_of(kernel, e, p, w);
        let false_ty = kernel.const_(e.logic.false_, vec![]);
        let anon = kernel.anon();
        let false_motive = kernel.lam(anon, false_ty, target, BinderInfo::Default);
        let false_rec = kernel.const_(e.logic.false_rec, vec![e.zero]);
        let body = apply_all(kernel, false_rec, &[false_motive, absurd]);
        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (d_id, d_ty),
                (i_id, i_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 11. all_intro -----------------------------------------------------
    minors.push({
        let blk = base + 220;
        let g_id = blk;
        let p_id = blk + 1;
        let d_id = blk + 2;
        let i_id = blk + 3;
        let w_id = blk + 4;
        let h_id = blk + 5;
        let z_id = blk + 6;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let i = kernel.fvar(i_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let z = kernel.fvar(z_id);
        let shifted = ctx_shift_app(kernel, &e.calc, g);
        let d_ty = prov(kernel, shifted, p);
        let i_ty = carrier(kernel, shifted, p, blk + 7);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let extended = vcons(kernel, e, z, w);
        let shifted_ctx_ok = {
            let c = kernel.const_(ctx_sat_shift, vec![]);
            apply_all(kernel, c, &[e.m, e.s, g, w, z, h])
        };
        let applied = apply_all(kernel, i, &[extended, shifted_ctx_ok]);
        let body = lam_fv(kernel, z_id, e.m, applied);
        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (d_id, d_ty),
                (i_id, i_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 12. all_elim ------------------------------------------------------
    minors.push({
        let blk = base + 230;
        let g_id = blk;
        let p_id = blk + 1;
        let t_id = blk + 2;
        let d_id = blk + 3;
        let i_id = blk + 4;
        let w_id = blk + 5;
        let h_id = blk + 6;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let t = kernel.fvar(t_id);
        let i = kernel.fvar(i_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let quantified = fapp(kernel, e.calc.all, &[p]);
        let d_ty = prov(kernel, g, quantified);
        let i_ty = carrier(kernel, g, quantified, blk + 7);
        let hyp = ctx_sat_of(kernel, e, g, w);

        let universal = apply_all(kernel, i, &[w, h]);
        let t_val = ev(kernel, e, t, w);
        let at_witness = kernel.app(universal, t_val);

        let instance = instantiate(kernel, &e.calc, p, t);
        let lhs = sat_of(kernel, e, instance, w);
        let extended = vcons(kernel, e, t_val, w);
        let rhs = sat_of(kernel, e, p, extended);
        let lemma = {
            let c = kernel.const_(e.subst.sat_inst, vec![]);
            apply_all(kernel, c, &[e.m, e.s, p, t, w])
        };
        let mover = iff_mpr(kernel, e.logic, lhs, rhs, lemma);
        let body = kernel.app(mover, at_witness);

        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (t_id, trm),
                (d_id, d_ty),
                (i_id, i_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 13. ex_intro ------------------------------------------------------
    minors.push({
        let blk = base + 240;
        let g_id = blk;
        let p_id = blk + 1;
        let t_id = blk + 2;
        let d_id = blk + 3;
        let i_id = blk + 4;
        let w_id = blk + 5;
        let h_id = blk + 6;
        let z_id = blk + 7;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let t = kernel.fvar(t_id);
        let i = kernel.fvar(i_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let z = kernel.fvar(z_id);
        let instance = instantiate(kernel, &e.calc, p, t);
        let d_ty = prov(kernel, g, instance);
        let i_ty = carrier(kernel, g, instance, blk + 8);
        let hyp = ctx_sat_of(kernel, e, g, w);

        let t_val = ev(kernel, e, t, w);
        let extended = vcons(kernel, e, t_val, w);
        let lhs = sat_of(kernel, e, instance, w);
        let rhs = sat_of(kernel, e, p, extended);
        let lemma = {
            let c = kernel.const_(e.subst.sat_inst, vec![]);
            apply_all(kernel, c, &[e.m, e.s, p, t, w])
        };
        let mover = iff_mp(kernel, e.logic, lhs, rhs, lemma);
        let at_witness = {
            let proof = apply_all(kernel, i, &[w, h]);
            kernel.app(mover, proof)
        };

        let pred = {
            let ext = vcons(kernel, e, z, w);
            let inner = sat_of(kernel, e, p, ext);
            lam_fv(kernel, z_id, e.m, inner)
        };
        let intro = kernel.const_(e.logic.exists_intro, vec![e.one]);
        let body = apply_all(kernel, intro, &[e.m, pred, t_val, at_witness]);

        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (t_id, trm),
                (d_id, d_ty),
                (i_id, i_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 14. ex_elim -------------------------------------------------------
    minors.push({
        let blk = base + 250;
        let g_id = blk;
        let p_id = blk + 1;
        let q_id = blk + 2;
        let d1_id = blk + 3;
        let d2_id = blk + 4;
        let i1_id = blk + 5;
        let i2_id = blk + 6;
        let w_id = blk + 7;
        let h_id = blk + 8;
        let z_id = blk + 9;
        let hz_id = blk + 10;
        let g = kernel.fvar(g_id);
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let i1 = kernel.fvar(i1_id);
        let i2 = kernel.fvar(i2_id);
        let w = kernel.fvar(w_id);
        let h = kernel.fvar(h_id);
        let z = kernel.fvar(z_id);
        let hz = kernel.fvar(hz_id);

        let quantified = fapp(kernel, e.calc.ex, &[p]);
        let d1_ty = prov(kernel, g, quantified);
        let shifted_ctx = ctx_shift_app(kernel, &e.calc, g);
        let minor_ctx = cons_app(kernel, &e.calc, p, shifted_ctx);
        let shifted_goal = f_shift_app(kernel, &e.calc, q);
        let d2_ty = prov(kernel, minor_ctx, shifted_goal);
        let i1_ty = carrier(kernel, g, quantified, blk + 11);
        let i2_ty = carrier(kernel, minor_ctx, shifted_goal, blk + 13);
        let hyp = ctx_sat_of(kernel, e, g, w);

        let pred = {
            let ext = vcons(kernel, e, z, w);
            let inner = sat_of(kernel, e, p, ext);
            lam_fv(kernel, z_id, e.m, inner)
        };
        let major = apply_all(kernel, i1, &[w, h]);
        let target = sat_of(kernel, e, q, w);

        let minor_term = {
            let extended = vcons(kernel, e, z, w);
            let head_sat = sat_of(kernel, e, p, extended);
            let shifted_ctx_sat = ctx_sat_of(kernel, e, shifted_ctx, extended);
            let shifted_ctx_ok = {
                let c = kernel.const_(ctx_sat_shift, vec![]);
                apply_all(kernel, c, &[e.m, e.s, g, w, z, h])
            };
            let full_ctx = and_intro(kernel, e, head_sat, shifted_ctx_sat, hz, shifted_ctx_ok);
            let shifted_goal_sat = sat_of(kernel, e, shifted_goal, extended);
            let inner = apply_all(kernel, i2, &[extended, full_ctx]);
            let lemma = {
                let c = kernel.const_(e.subst.sat_shift, vec![]);
                apply_all(kernel, c, &[e.m, e.s, q, w, z])
            };
            let mover = iff_mp(kernel, e.logic, shifted_goal_sat, target, lemma);
            let moved = kernel.app(mover, inner);
            let hz_ty = sat_of(kernel, e, p, extended);
            let with_hz = lam_fv(kernel, hz_id, hz_ty, moved);
            lam_fv(kernel, z_id, e.m, with_hz)
        };

        let rec_motive = {
            let anon = kernel.anon();
            let exists_ty = {
                let c = kernel.const_(e.logic.exists_, vec![e.one]);
                apply_all(kernel, c, &[e.m, pred])
            };
            kernel.lam(anon, exists_ty, target, BinderInfo::Default)
        };
        let rec_const = kernel.const_(e.logic.exists_rec, vec![e.one]);
        let body = apply_all(
            kernel,
            rec_const,
            &[e.m, pred, rec_motive, minor_term, major],
        );

        lams(
            kernel,
            &[
                (g_id, ctx_ty),
                (p_id, fml),
                (q_id, fml),
                (d1_id, d1_ty),
                (d2_id, d2_ty),
                (i1_id, i1_ty),
                (i2_id, i2_ty),
                (w_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    });

    // ---- 15. eqf_refl ------------------------------------------------------
    minors.push({
        let blk = base + 270;
        let g_id = blk;
        let t_id = blk + 1;
        let w_id = blk + 2;
        let h_id = blk + 3;
        let g = kernel.fvar(g_id);
        let t = kernel.fvar(t_id);
        let w = kernel.fvar(w_id);
        let hyp = ctx_sat_of(kernel, e, g, w);
        let value = ev(kernel, e, t, w);
        let refl = kernel.const_(e.logic.eq_refl, vec![e.one]);
        let body = apply_all(kernel, refl, &[e.m, value]);
        lams(
            kernel,
            &[(g_id, ctx_ty), (t_id, trm), (w_id, e.val_ty), (h_id, hyp)],
            body,
        )
    });

    assert_eq!(
        minors.len(),
        rule::EQF_REFL + 1,
        "one minor per FO.Provable rule, in declaration order"
    );

    // `FO.Provable` is `Prop`-valued with sixteen constructors, so it is not a
    // syntactic subsingleton and `inductive.rs` restricts its recursor's motive
    // to `Sort 0`. A restricted recursor carries NO universe parameter -- the
    // same shape `ipc_soundness.rs` applies `Provable.rec` with. Passing one
    // here is rejected.
    let rec_const = kernel.const_(e.calculus.provable_rec, vec![]);
    let mut args = vec![motive];
    args.extend_from_slice(&minors);
    let applied = apply_all(kernel, rec_const, &args);

    let g_id = base + 300;
    let p_id = base + 301;
    let d_id = base + 302;
    let g = kernel.fvar(g_id);
    let p = kernel.fvar(p_id);
    let d = kernel.fvar(d_id);
    let d_ty = prov(kernel, g, p);
    let body = apply_all(kernel, applied, &[g, p, d]);
    let concl = carrier(kernel, g, p, base + 303);

    let binders = [(g_id, ctx_ty), (p_id, fml), (d_id, d_ty)];
    let value = lams(kernel, &binders, body);
    let ty = pis(kernel, &binders, concl);

    let ambient = e.ambient();
    let full_ty = pis(kernel, &ambient, ty);
    let full_value = lams(kernel, &ambient, value);

    let name = kernel.name_str(e.syn.fo, "soundness");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: full_ty,
        value: full_value,
    })?;
    Ok(name)
}

/// `FO.consistency : Not (FO.Provable FO.Context.nil FO.Formula.bot)` — see the
/// module docs. One application of soundness at the ℕ structure.
fn declare_consistency(
    kernel: &mut crate::Kernel,
    e: &SoundEnv,
    soundness: NameId,
) -> Result<NameId, KernelError> {
    let semantics = e.calculus.semantics;
    let nat = semantics.syntax.nat;
    let nat_ty = kernel.const_(nat.nat, vec![]);
    let structure = kernel.const_(semantics.nat_structure, vec![]);
    let nil = kernel.const_(e.calc.nil, vec![]);
    let bot = kernel.const_(e.calc.bot, vec![]);

    let d_id = 1_644_001_u64;
    let junk_id = 1_644_002_u64;
    let d = kernel.fvar(d_id);

    // The constant-zero valuation: ℕ is inhabited, which is what makes the
    // corollary constructive.
    let valuation = {
        let zero = kernel.const_(nat.zero, vec![]);
        lam_fv(kernel, junk_id, nat_ty, zero)
    };
    let true_intro = kernel.const_(e.logic.true_intro, vec![]);

    let c = kernel.const_(soundness, vec![]);
    let body = apply_all(
        kernel,
        c,
        &[nat_ty, structure, nil, bot, d, valuation, true_intro],
    );

    let deriv_ty = {
        let c = kernel.const_(e.calc.provable, vec![]);
        apply_all(kernel, c, &[nil, bot])
    };
    let value = lam_fv(kernel, d_id, deriv_ty, body);

    let ty = {
        let not_const = kernel.const_(e.logic.not, vec![]);
        kernel.app(not_const, deriv_ty)
    };

    let name = kernel.name_str(e.syn.fo, "consistency");
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
