//! **Slice 4 of the first-order model theory group** (`fo_*.rs`, ADR-1636):
//! the **substitution lemma** for first-order satisfaction, and the two
//! coincidence lemmas it needs.
//!
//! ```text
//! FO.Val.cons_congr  : Π M (a : M) (w1 w2 : Nat -> M),
//!                        (Π n, Eq M (w1 n) (w2 n))
//!                        -> Π n, Eq M (Val.cons M a w1 n) (Val.cons M a w2 n)
//! FO.Term.eval_congr : Π M S t w1 w2, (Π n, Eq M (w1 n) (w2 n))
//!                        -> Eq M (Term.eval M S t w1) (Term.eval M S t w2)
//! FO.sat_congr       : Π M S p w1 w2, (Π n, Eq M (w1 n) (w2 n))
//!                        -> Iff (sat M S p w1) (sat M S p w2)
//! FO.Term.eval_subst : Π M S t s w,
//!      Eq M (Term.eval M S (Term.subst t s) w)
//!           (Term.eval M S t (fun n => Term.eval M S (s n) w))
//! FO.sat_subst       : Π M S p s w,
//!      Iff (sat M S (Formula.subst p s) w)
//!          (sat M S p (fun n => Term.eval M S (s n) w))
//! FO.sat_shift       : Π M S p w (a : M),
//!      Iff (sat M S (Formula.shift p) (Val.cons M a w)) (sat M S p w)
//! FO.sat_inst        : Π M S p t w,
//!      Iff (sat M S (Formula.subst p (Subst.cons t Subst.id)) w)
//!          (sat M S p (Val.cons M (Term.eval M S t w) w))
//! ```
//!
//! `FO.sat_subst` is the theorem this whole group is arranged around, and the
//! last two are the corollaries `fo_soundness.rs` actually consumes — one per
//! quantifier rule.
//!
//! ## Why the coincidence lemmas exist, and why they are `Iff`
//!
//! The substitution lemma's `∀` case produces a satisfaction claim at the
//! valuation `fun n => Term.eval M S (Subst.lift s n) (Val.cons M a w)`, and
//! needs it at `Val.cons M a (fun n => Term.eval M S (s n) w)`. Those two
//! functions agree at every index, but they are **not** the same term, and
//! this kernel has no `funext` (`prelude.rs`: no `Classical.em`, no `propext`,
//! no `Quot.sound`, so no `funext` either). Pointwise agreement is therefore
//! all one can have, and `FO.sat_congr` — "satisfaction only looks at the
//! valuation pointwise" — is what converts it into a statement about `sat`.
//!
//! `sat_congr` is stated as an `Iff` rather than a one-directional
//! implication, and it has to be: the `imp` clause of `FO.sat` puts a
//! subformula in **negative** position, so the forward direction at
//! `imp p q` consumes the *backward* direction at `p`. A single-direction
//! induction does not close. (The hypothesis `Π n, Eq M (w1 n) (w2 n)` is not
//! symmetric, so "prove one direction and apply it twice" would need the
//! pointwise `Eq.symm` at every index — an `Iff` motive is strictly cheaper.)
//!
//! ## What the `Nat.rec`-shaped `Val.cons`/`Subst.cons` buy
//!
//! Both binder cases end at an obligation of the form
//!
//! ```text
//! Π n, Eq M (Term.eval M S (Subst.lift s n) (Val.cons M a w)) (Val.cons M a w' n)
//! ```
//!
//! and it is discharged by a **two-line** `Nat.rec`:
//!
//! - at `Nat.zero` both sides ι-reduce to `a`, so the base case is `Eq.refl`;
//! - at `Nat.succ k` the step case is *exactly* `FO.Term.eval_subst` applied
//!   at `s k` and `FO.Subst.shift`, with **no** rewriting in between.
//!
//! The second point is the one worth stating, because it is where a
//! `funext`-free kernel would normally start paying. `Term.eval_subst`'s
//! right-hand side at that instance is
//! `Term.eval M S (s k) (fun m => Term.eval M S (Subst.shift m) (Val.cons M a w))`,
//! and the inner lambda is **definitionally** `w`: its body ι-reduces to
//! `Val.cons M a w (Nat.succ m)` and then to `w m`, and the kernel's η rule
//! closes `fun m => w m` against `w`. So the "shift and read past the new
//! slot" step costs nothing at all. `fo_semantics.rs`'s module test
//! `shifting_past_the_new_slot_is_definitionally_the_old_valuation` measures
//! that claim directly rather than leaving it as an assertion in prose.
//!
//! The same reduction is what makes `FO.sat_shift` a **zero-cost corollary**:
//! its proof term is literally `FO.sat_subst M S p FO.Subst.shift
//! (FO.Val.cons M a w)`, and the stated type is that term's own type written
//! in reduced form. `FO.sat_inst` needs one extra `Nat.rec` key (both of whose
//! cases are `Eq.refl`) and one `Iff` composition.
//!
//! ## The eleven inductions, and where each lives
//!
//! | lemma | recursion on | minors |
//! | --- | --- | --- |
//! | `Val.cons_congr` | `Nat` | 2 |
//! | `Term.eval_congr` | `FO.Term` | 4 |
//! | `Term.eval_subst` | `FO.Term` | 4 |
//! | `sat_congr` | `FO.Formula` | 9 |
//! | `sat_subst` | `FO.Formula` | 9 |
//!
//! Both `FO.Formula` inductions carry an `Iff` motive and eliminate into
//! `Prop`; both `FO.Term` inductions carry an `Eq` motive and do the same.
//! Every minor is closed by the kernel's own `Eq`/`Iff`/`And`/`Or`/`Exists`
//! combinators — there is no chain-algebra layer here, because the semantics
//! is `Prop`-valued rather than valued in a Heyting chain (contrast
//! `ipc_soundness.rs`, whose eleven minors each needed a lattice lemma).

#![allow(clippy::similar_names)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::fo_syntax::SyntaxNames;
use crate::fo_syntax::{
    apply_all, arrow, gcongr, geq, geq_motive, giff_refl, giff_trans, grefl, gsymm, gtrans,
    gtransport, iff_intro, iff_mp, iff_mpr, iff_ty, lam_fv, lams, pi_fv, pis,
};
use crate::{
    BinderInfo, Declaration, ExprId, FoSemanticsPrelude, KernelError, LevelId, LogicPrelude,
    NameId, build_fo_semantics_prelude,
};

/// Names produced by [`build_fo_substitution_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoSubstitutionPrelude {
    /// `FO.Structure`, `FO.Term.eval`, `FO.sat` and the syntax below them.
    pub semantics: FoSemanticsPrelude,
    /// `FO.Val.cons_congr`.
    pub val_cons_congr: NameId,
    /// `FO.Term.eval_congr`.
    pub eval_congr: NameId,
    /// `FO.Term.eval_subst`.
    pub eval_subst: NameId,
    /// `FO.sat_congr`.
    pub sat_congr: NameId,
    /// `FO.sat_subst` — the substitution lemma.
    pub sat_subst: NameId,
    /// `FO.sat_shift`.
    pub sat_shift: NameId,
    /// `FO.sat_inst`.
    pub sat_inst: NameId,
}

/// Build the coincidence and substitution lemmas.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_substitution_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoSubstitutionPrelude, KernelError> {
    let semantics = build_fo_semantics_prelude(kernel)?;
    declare_fo_substitution_over(kernel, &semantics)
}

/// The same package, over a semantics prelude **already** in this kernel.
///
/// `fo_soundness.rs` needs both `fo_provable.rs`'s calculus and these lemmas in
/// ONE environment, and both packages sit on top of `fo_semantics.rs`. Calling
/// the two `build_*` entry points in sequence re-runs
/// `build_fo_semantics_prelude` and the trusted gate refuses the second
/// `FO.Structure` with `DeclarationExists` — measured 2026-09-05, which is why
/// this split exists rather than as a stylistic preference. This is the same
/// shape `ipc_soundness.rs` handles by re-declaring `ipc_eval` itself instead
/// of calling slice 3's builder.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub(crate) fn declare_fo_substitution_over(
    kernel: &mut crate::Kernel,
    semantics: &FoSemanticsPrelude,
) -> Result<FoSubstitutionPrelude, KernelError> {
    let semantics = *semantics;
    let val_cons_congr = declare_val_cons_congr(kernel, &semantics)?;
    let eval_congr = declare_eval_congr(kernel, &semantics)?;
    let eval_subst = declare_eval_subst(kernel, &semantics)?;
    let sat_congr = declare_sat_congr(kernel, &semantics, eval_congr, val_cons_congr)?;
    let sat_subst = declare_sat_subst(kernel, &semantics, eval_subst, sat_congr)?;
    let sat_shift = declare_sat_shift(kernel, &semantics, sat_subst)?;
    let sat_inst = declare_sat_inst(kernel, &semantics, sat_subst, sat_congr)?;
    Ok(FoSubstitutionPrelude {
        semantics,
        val_cons_congr,
        eval_congr,
        eval_subst,
        sat_congr,
        sat_subst,
        sat_shift,
        sat_inst,
    })
}

// ============================================================================
// The shared ambient context.
// ============================================================================

/// Everything the lemma builders need: the interned names, the two fixed
/// levels, and the ambient `M` / `S` free variables every statement in this
/// file is universally quantified over.
pub(crate) struct Env {
    pub(crate) logic: LogicPrelude,
    pub(crate) syn: SyntaxNames,
    pub(crate) sem: FoSemanticsPrelude,
    /// `Sort 1`, the carrier's universe.
    pub(crate) type_sort: ExprId,
    pub(crate) one: LevelId,
    /// The fvar id of the ambient carrier `M`.
    pub(crate) m_id: u64,
    /// The fvar id of the ambient structure `S`.
    pub(crate) s_id: u64,
    /// `M` as an expression.
    pub(crate) m: ExprId,
    /// `S` as an expression.
    pub(crate) s: ExprId,
    /// `FO.Structure M`.
    pub(crate) struct_m: ExprId,
    /// `Nat -> M`, the type of a valuation.
    pub(crate) val_ty: ExprId,
    /// `Nat -> FO.Term`, the type of a substitution.
    pub(crate) sub_ty: ExprId,
}

impl Env {
    fn new(kernel: &mut crate::Kernel, sem: &FoSemanticsPrelude) -> Self {
        let syn = sem.syntax.names(kernel);
        let logic = sem.syntax.nat.logic;
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let type_sort = kernel.sort(one);

        let m_id = 1_638_001_u64;
        let s_id = 1_638_002_u64;
        let m = kernel.fvar(m_id);
        let s = kernel.fvar(s_id);
        let structure_const = kernel.const_(sem.structure, vec![]);
        let struct_m = kernel.app(structure_const, m);
        let val_ty = arrow(kernel, syn.nat_ty, m);
        let sub_ty = arrow(kernel, syn.nat_ty, syn.term_ty);

        Self {
            logic,
            syn,
            sem: *sem,
            type_sort,
            one,
            m_id,
            s_id,
            m,
            s,
            struct_m,
            val_ty,
            sub_ty,
        }
    }

    /// The two ambient binders `(M : Type) (S : FO.Structure M)`.
    fn ambient(&self) -> [(u64, ExprId); 2] {
        [(self.m_id, self.type_sort), (self.s_id, self.struct_m)]
    }
}

/// `FO.Term.eval M S t v`.
fn ev(kernel: &mut crate::Kernel, e: &Env, t: ExprId, v: ExprId) -> ExprId {
    let c = kernel.const_(e.sem.term_eval, vec![]);
    apply_all(kernel, c, &[e.m, e.s, t, v])
}

/// `FO.sat M S p v`.
fn sat_of(kernel: &mut crate::Kernel, e: &Env, p: ExprId, v: ExprId) -> ExprId {
    let c = kernel.const_(e.sem.sat, vec![]);
    apply_all(kernel, c, &[e.m, e.s, p, v])
}

/// `FO.Val.cons M a v`.
fn vcons(kernel: &mut crate::Kernel, e: &Env, a: ExprId, v: ExprId) -> ExprId {
    let c = kernel.const_(e.sem.val_cons, vec![]);
    apply_all(kernel, c, &[e.m, a, v])
}

/// `FO.Structure.<field> M S args…`.
fn field(kernel: &mut crate::Kernel, e: &Env, name: NameId, args: &[ExprId]) -> ExprId {
    let c = kernel.const_(name, vec![]);
    let head = apply_all(kernel, c, &[e.m, e.s]);
    apply_all(kernel, head, args)
}

/// `Eq M x y`.
fn eqm(kernel: &mut crate::Kernel, e: &Env, x: ExprId, y: ExprId) -> ExprId {
    geq(kernel, e.logic, e.m, x, y)
}

/// `Π (n : Nat), Eq M (w1 n) (w2 n)` — pointwise agreement of two valuations.
fn pointwise(kernel: &mut crate::Kernel, e: &Env, w1: ExprId, w2: ExprId, fv: u64) -> ExprId {
    let n = kernel.fvar(fv);
    let l = kernel.app(w1, n);
    let r = kernel.app(w2, n);
    let body = eqm(kernel, e, l, r);
    pi_fv(kernel, fv, e.syn.nat_ty, body)
}

/// `fun (n : Nat) => FO.Term.eval M S (s n) w` — the valuation a substitution
/// induces from a valuation.
fn compose(kernel: &mut crate::Kernel, e: &Env, s: ExprId, w: ExprId, fv: u64) -> ExprId {
    let n = kernel.fvar(fv);
    let s_n = kernel.app(s, n);
    let body = ev(kernel, e, s_n, w);
    lam_fv(kernel, fv, e.syn.nat_ty, body)
}

/// Declare a `Theorem` with the two ambient binders already wrapped around
/// both its type and its value.
fn declare_ambient(
    kernel: &mut crate::Kernel,
    e: &Env,
    name: NameId,
    ty: ExprId,
    value: ExprId,
) -> Result<NameId, KernelError> {
    let binders = e.ambient();
    let full_ty = pis(kernel, &binders, ty);
    let full_value = lams(kernel, &binders, value);
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: full_ty,
        value: full_value,
    })?;
    Ok(name)
}

// ============================================================================
// FO.Val.cons_congr
// ============================================================================

/// `FO.Val.cons_congr : Π M (a : M) (w1 w2 : Nat -> M),
/// (Π n, Eq M (w1 n) (w2 n)) -> Π n, Eq M (Val.cons M a w1 n) (Val.cons M a w2 n)`.
///
/// `Nat.rec` on the index: at `Nat.zero` both sides ι-reduce to `a`
/// (`Eq.refl`), at `Nat.succ k` to `w1 k` and `w2 k` (the hypothesis at `k`).
/// This is the only lemma in the file that does not need the structure `S`,
/// so it takes only `M`.
fn declare_val_cons_congr(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);

    let a_id = 1_638_011_u64;
    let w1_id = 1_638_012_u64;
    let w2_id = 1_638_013_u64;
    let h_id = 1_638_014_u64;
    let n_id = 1_638_015_u64;
    let k_id = 1_638_016_u64;
    let ih_id = 1_638_017_u64;

    let a = kernel.fvar(a_id);
    let w1 = kernel.fvar(w1_id);
    let w2 = kernel.fvar(w2_id);
    let h = kernel.fvar(h_id);
    let n = kernel.fvar(n_id);
    let k = kernel.fvar(k_id);

    let hyp_ty = pointwise(kernel, &e, w1, w2, 1_638_018_u64);

    // motive := fun (n : Nat) => Eq M (Val.cons M a w1 n) (Val.cons M a w2 n)
    let goal_at = |kernel: &mut crate::Kernel, idx: ExprId| -> ExprId {
        let left = vcons(kernel, &e, a, w1);
        let left = kernel.app(left, idx);
        let right = vcons(kernel, &e, a, w2);
        let right = kernel.app(right, idx);
        eqm(kernel, &e, left, right)
    };
    let motive = {
        let mv_id = 1_638_019_u64;
        let mv = kernel.fvar(mv_id);
        let body = goal_at(kernel, mv);
        lam_fv(kernel, mv_id, e.syn.nat_ty, body)
    };

    let base = grefl(kernel, e.logic, e.m, a);
    let step = {
        let ih_ty = goal_at(kernel, k);
        let body = kernel.app(h, k);
        lams(kernel, &[(k_id, e.syn.nat_ty), (ih_id, ih_ty)], body)
    };

    let zero_lvl = kernel.level_zero();
    let nat_rec = kernel.const_(e.syn.nat_rec, vec![zero_lvl]);
    let applied = apply_all(kernel, nat_rec, &[motive, base, step, n]);

    let concl = goal_at(kernel, n);
    let binders = [
        (a_id, e.m),
        (w1_id, e.val_ty),
        (w2_id, e.val_ty),
        (h_id, hyp_ty),
        (n_id, e.syn.nat_ty),
    ];
    let ty = pis(kernel, &binders, concl);
    let value = lams(kernel, &binders, applied);

    // Only `M` is ambient here, not `S`.
    let ty = pi_fv(kernel, e.m_id, e.type_sort, ty);
    let value = lam_fv(kernel, e.m_id, e.type_sort, value);

    let val_ns = kernel.name_str(e.syn.fo, "Val");
    let name = kernel.name_str(val_ns, "cons_congr");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ============================================================================
// The two FO.Term inductions.
// ============================================================================

/// `FO.Term.eval_congr : Π M S t w1 w2, (Π n, Eq M (w1 n) (w2 n))
/// -> Eq M (Term.eval M S t w1) (Term.eval M S t w2)`.
///
/// `FO.Term.rec` at the `Prop` motive
/// `fun t => Π w1 w2 h, Eq M (eval t w1) (eval t w2)`. `var` reads the
/// hypothesis at its index; `f0` is `Eq.refl`; `f1` and `f2` are one and two
/// congruence steps in the structure's interpretation.
fn declare_eval_congr(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);
    let base = 1_638_100_u64;

    // motive_at t := Π (w1 w2 : Nat -> M) (h : ptwise), Eq M (eval t w1) (eval t w2)
    let motive_at = |kernel: &mut crate::Kernel, t: ExprId, blk: u64| -> ExprId {
        let w1_id = blk;
        let w2_id = blk + 1;
        let h_id = blk + 2;
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 3);
        let l = ev(kernel, &e, t, w1);
        let r = ev(kernel, &e, t, w2);
        let concl = eqm(kernel, &e, l, r);
        pis(
            kernel,
            &[(w1_id, e.val_ty), (w2_id, e.val_ty), (h_id, hyp)],
            concl,
        )
    };

    let motive = {
        let t_id = base;
        let t = kernel.fvar(t_id);
        let body = motive_at(kernel, t, base + 1);
        lam_fv(kernel, t_id, e.syn.term_ty, body)
    };

    // m_var := fun i w1 w2 h => h i
    let m_var = {
        let blk = base + 10;
        let i_id = blk;
        let w1_id = blk + 1;
        let w2_id = blk + 2;
        let h_id = blk + 3;
        let i = kernel.fvar(i_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 4);
        let body = kernel.app(h, i);
        lams(
            kernel,
            &[
                (i_id, e.syn.nat_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    // m_f0 := fun k w1 w2 h => Eq.refl M (S.fn0 k)
    let m_f0 = {
        let blk = base + 20;
        let k_id = blk;
        let w1_id = blk + 1;
        let w2_id = blk + 2;
        let h_id = blk + 3;
        let k = kernel.fvar(k_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 4);
        let value = field(kernel, &e, e.sem.fn0, &[k]);
        let body = grefl(kernel, e.logic, e.m, value);
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    // m_f1 := fun k t ih w1 w2 h => congr (fun z => S.fn1 k z) (ih w1 w2 h)
    let m_f1 = {
        let blk = base + 30;
        let k_id = blk;
        let t_id = blk + 1;
        let ih_id = blk + 2;
        let w1_id = blk + 3;
        let w2_id = blk + 4;
        let h_id = blk + 5;
        let k = kernel.fvar(k_id);
        let t = kernel.fvar(t_id);
        let ih = kernel.fvar(ih_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 6);
        let ih_ty = motive_at(kernel, t, blk + 7);
        let sub = apply_all(kernel, ih, &[w1, w2, h]);
        let a = ev(kernel, &e, t, w1);
        let b = ev(kernel, &e, t, w2);
        let body = gcongr(
            kernel,
            e.logic,
            e.m,
            e.m,
            a,
            b,
            sub,
            &|kernel, z| field(kernel, &e, e.sem.fn1, &[k, z]),
            blk + 8,
        );
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (t_id, e.syn.term_ty),
                (ih_id, ih_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    // m_f2 := fun k a b ia ib w1 w2 h => trans (congr in the 1st slot) (congr in the 2nd)
    let m_f2 = {
        let blk = base + 40;
        let k_id = blk;
        let a_id = blk + 1;
        let b_id = blk + 2;
        let ia_id = blk + 3;
        let ib_id = blk + 4;
        let w1_id = blk + 5;
        let w2_id = blk + 6;
        let h_id = blk + 7;
        let k = kernel.fvar(k_id);
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let ia = kernel.fvar(ia_id);
        let ib = kernel.fvar(ib_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 8);
        let ia_ty = motive_at(kernel, a, blk + 9);
        let ib_ty = motive_at(kernel, b, blk + 12);

        let a1 = ev(kernel, &e, a, w1);
        let a2 = ev(kernel, &e, a, w2);
        let b1 = ev(kernel, &e, b, w1);
        let b2 = ev(kernel, &e, b, w2);
        let ea = apply_all(kernel, ia, &[w1, w2, h]);
        let eb = apply_all(kernel, ib, &[w1, w2, h]);

        let step1 = gcongr(
            kernel,
            e.logic,
            e.m,
            e.m,
            a1,
            a2,
            ea,
            &|kernel, z| field(kernel, &e, e.sem.fn2, &[k, z, b1]),
            blk + 15,
        );
        let step2 = gcongr(
            kernel,
            e.logic,
            e.m,
            e.m,
            b1,
            b2,
            eb,
            &|kernel, z| field(kernel, &e, e.sem.fn2, &[k, a2, z]),
            blk + 16,
        );
        let x = field(kernel, &e, e.sem.fn2, &[k, a1, b1]);
        let y = field(kernel, &e, e.sem.fn2, &[k, a2, b1]);
        let z = field(kernel, &e, e.sem.fn2, &[k, a2, b2]);
        let body = gtrans(kernel, e.logic, e.m, x, y, z, step1, step2, blk + 17);

        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (a_id, e.syn.term_ty),
                (b_id, e.syn.term_ty),
                (ia_id, ia_ty),
                (ib_id, ib_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    let zero_lvl = kernel.level_zero();
    let rec_const = kernel.const_(e.syn.term_rec, vec![zero_lvl]);
    let applied = apply_all(kernel, rec_const, &[motive, m_var, m_f0, m_f1, m_f2]);

    let t_id = base + 60;
    let t = kernel.fvar(t_id);
    let body = kernel.app(applied, t);
    let value = lam_fv(kernel, t_id, e.syn.term_ty, body);
    let concl = motive_at(kernel, t, base + 61);
    let ty = pi_fv(kernel, t_id, e.syn.term_ty, concl);

    let name = kernel.name_str(e.syn.term, "eval_congr");
    declare_ambient(kernel, &e, name, ty, value)
}

/// `FO.Term.eval_subst : Π M S t s w,
/// Eq M (eval (Term.subst t s) w) (eval t (fun n => eval (s n) w))`.
///
/// The term half of the substitution lemma, and the workhorse: both binder
/// cases of [`declare_sat_subst`] discharge their `Nat.succ` obligation by a
/// bare instance of this theorem.
fn declare_eval_subst(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);
    let base = 1_638_200_u64;

    let tsub = |kernel: &mut crate::Kernel, t: ExprId, s: ExprId| -> ExprId {
        let c = kernel.const_(e.sem.syntax.term_subst, vec![]);
        apply_all(kernel, c, &[t, s])
    };

    // motive_at t := Π (s : Nat -> Term) (w : Nat -> M),
    //   Eq M (eval (Term.subst t s) w) (eval t (fun n => eval (s n) w))
    let motive_at = |kernel: &mut crate::Kernel, t: ExprId, blk: u64| -> ExprId {
        let s_id = blk;
        let w_id = blk + 1;
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let substituted = tsub(kernel, t, s);
        let l = ev(kernel, &e, substituted, w);
        let composed = compose(kernel, &e, s, w, blk + 2);
        let r = ev(kernel, &e, t, composed);
        let concl = eqm(kernel, &e, l, r);
        pis(kernel, &[(s_id, e.sub_ty), (w_id, e.val_ty)], concl)
    };

    let motive = {
        let t_id = base;
        let t = kernel.fvar(t_id);
        let body = motive_at(kernel, t, base + 1);
        lam_fv(kernel, t_id, e.syn.term_ty, body)
    };

    // m_var := fun i s w => Eq.refl M (eval (s i) w)
    let m_var = {
        let blk = base + 10;
        let i_id = blk;
        let s_id = blk + 1;
        let w_id = blk + 2;
        let i = kernel.fvar(i_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let s_i = kernel.app(s, i);
        let value = ev(kernel, &e, s_i, w);
        let body = grefl(kernel, e.logic, e.m, value);
        lams(
            kernel,
            &[(i_id, e.syn.nat_ty), (s_id, e.sub_ty), (w_id, e.val_ty)],
            body,
        )
    };

    // m_f0 := fun k s w => Eq.refl M (S.fn0 k)
    let m_f0 = {
        let blk = base + 20;
        let k_id = blk;
        let s_id = blk + 1;
        let w_id = blk + 2;
        let k = kernel.fvar(k_id);
        let value = field(kernel, &e, e.sem.fn0, &[k]);
        let body = grefl(kernel, e.logic, e.m, value);
        lams(
            kernel,
            &[(k_id, e.syn.nat_ty), (s_id, e.sub_ty), (w_id, e.val_ty)],
            body,
        )
    };

    // m_f1 := fun k t ih s w => congr (fun z => S.fn1 k z) (ih s w)
    let m_f1 = {
        let blk = base + 30;
        let k_id = blk;
        let t_id = blk + 1;
        let ih_id = blk + 2;
        let s_id = blk + 3;
        let w_id = blk + 4;
        let k = kernel.fvar(k_id);
        let t = kernel.fvar(t_id);
        let ih = kernel.fvar(ih_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let ih_ty = motive_at(kernel, t, blk + 5);
        let sub = apply_all(kernel, ih, &[s, w]);
        let substituted = tsub(kernel, t, s);
        let a = ev(kernel, &e, substituted, w);
        let composed = compose(kernel, &e, s, w, blk + 8);
        let b = ev(kernel, &e, t, composed);
        let body = gcongr(
            kernel,
            e.logic,
            e.m,
            e.m,
            a,
            b,
            sub,
            &|kernel, z| field(kernel, &e, e.sem.fn1, &[k, z]),
            blk + 9,
        );
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (t_id, e.syn.term_ty),
                (ih_id, ih_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };

    // m_f2 := fun k a b ia ib s w => trans (congr 1st slot) (congr 2nd slot)
    let m_f2 = {
        let blk = base + 40;
        let k_id = blk;
        let a_id = blk + 1;
        let b_id = blk + 2;
        let ia_id = blk + 3;
        let ib_id = blk + 4;
        let s_id = blk + 5;
        let w_id = blk + 6;
        let k = kernel.fvar(k_id);
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let ia = kernel.fvar(ia_id);
        let ib = kernel.fvar(ib_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let ia_ty = motive_at(kernel, a, blk + 7);
        let ib_ty = motive_at(kernel, b, blk + 10);

        let a_sub = tsub(kernel, a, s);
        let b_sub = tsub(kernel, b, s);
        let a1 = ev(kernel, &e, a_sub, w);
        let b1 = ev(kernel, &e, b_sub, w);
        let composed = compose(kernel, &e, s, w, blk + 13);
        let a2 = ev(kernel, &e, a, composed);
        let b2 = ev(kernel, &e, b, composed);
        let ea = apply_all(kernel, ia, &[s, w]);
        let eb = apply_all(kernel, ib, &[s, w]);

        let step1 = gcongr(
            kernel,
            e.logic,
            e.m,
            e.m,
            a1,
            a2,
            ea,
            &|kernel, z| field(kernel, &e, e.sem.fn2, &[k, z, b1]),
            blk + 14,
        );
        let step2 = gcongr(
            kernel,
            e.logic,
            e.m,
            e.m,
            b1,
            b2,
            eb,
            &|kernel, z| field(kernel, &e, e.sem.fn2, &[k, a2, z]),
            blk + 15,
        );
        let x = field(kernel, &e, e.sem.fn2, &[k, a1, b1]);
        let y = field(kernel, &e, e.sem.fn2, &[k, a2, b1]);
        let z = field(kernel, &e, e.sem.fn2, &[k, a2, b2]);
        let body = gtrans(kernel, e.logic, e.m, x, y, z, step1, step2, blk + 16);

        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (a_id, e.syn.term_ty),
                (b_id, e.syn.term_ty),
                (ia_id, ia_ty),
                (ib_id, ib_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };

    let zero_lvl = kernel.level_zero();
    let rec_const = kernel.const_(e.syn.term_rec, vec![zero_lvl]);
    let applied = apply_all(kernel, rec_const, &[motive, m_var, m_f0, m_f1, m_f2]);

    let t_id = base + 60;
    let t = kernel.fvar(t_id);
    let body = kernel.app(applied, t);
    let value = lam_fv(kernel, t_id, e.syn.term_ty, body);
    let concl = motive_at(kernel, t, base + 61);
    let ty = pi_fv(kernel, t_id, e.syn.term_ty, concl);

    let name = kernel.name_str(e.syn.term, "eval_subst");
    declare_ambient(kernel, &e, name, ty, value)
}

// ============================================================================
// The two FO.Formula inductions.
// ============================================================================

/// The shared shape of an `Iff` minor over two atomic arguments, used by both
/// `Formula.rec` inductions at `eqf`: from `ea : Eq M a1 a2` and
/// `eb : Eq M b1 b2`, build `Iff (Eq M a1 b1) (Eq M a2 b2)`.
fn eqf_minor_body(
    kernel: &mut crate::Kernel,
    e: &Env,
    a1: ExprId,
    a2: ExprId,
    b1: ExprId,
    b2: ExprId,
    ea: ExprId,
    eb: ExprId,
    blk: u64,
) -> ExprId {
    let lhs = eqm(kernel, e, a1, b1);
    let rhs = eqm(kernel, e, a2, b2);

    let mp = {
        let p_id = blk;
        let p = kernel.fvar(p_id);
        let s1 = gsymm(kernel, e.logic, e.m, a1, a2, ea, blk + 1);
        let s2 = gtrans(kernel, e.logic, e.m, a1, b1, b2, p, eb, blk + 2);
        let body = gtrans(kernel, e.logic, e.m, a2, a1, b2, s1, s2, blk + 3);
        lam_fv(kernel, p_id, lhs, body)
    };
    let mpr = {
        let q_id = blk + 4;
        let q = kernel.fvar(q_id);
        let t1 = gtrans(kernel, e.logic, e.m, a1, a2, b2, ea, q, blk + 5);
        let t2 = gsymm(kernel, e.logic, e.m, b1, b2, eb, blk + 6);
        let body = gtrans(kernel, e.logic, e.m, a1, b2, b1, t1, t2, blk + 7);
        lam_fv(kernel, q_id, rhs, body)
    };
    iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
}

/// `Iff (S.rel1 k x1) (S.rel1 k x2)` from `h : Eq M x1 x2`, by transport in
/// each direction.
fn rel1_minor_body(
    kernel: &mut crate::Kernel,
    e: &Env,
    k: ExprId,
    x1: ExprId,
    x2: ExprId,
    h: ExprId,
    blk: u64,
) -> ExprId {
    let lhs = field(kernel, e, e.sem.rel1, &[k, x1]);
    let rhs = field(kernel, e, e.sem.rel1, &[k, x2]);

    let mp = {
        let p_id = blk;
        let p = kernel.fvar(p_id);
        let motive = geq_motive(
            kernel,
            e.logic,
            e.m,
            x1,
            &|kernel, z| field(kernel, e, e.sem.rel1, &[k, z]),
            blk + 1,
        );
        let body = gtransport(kernel, e.logic, e.m, x1, motive, p, x2, h);
        lam_fv(kernel, p_id, lhs, body)
    };
    let mpr = {
        let q_id = blk + 2;
        let q = kernel.fvar(q_id);
        let back = gsymm(kernel, e.logic, e.m, x1, x2, h, blk + 3);
        let motive = geq_motive(
            kernel,
            e.logic,
            e.m,
            x2,
            &|kernel, z| field(kernel, e, e.sem.rel1, &[k, z]),
            blk + 4,
        );
        let body = gtransport(kernel, e.logic, e.m, x2, motive, q, x1, back);
        lam_fv(kernel, q_id, rhs, body)
    };
    iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
}

/// `Iff (S.rel2 k a1 b1) (S.rel2 k a2 b2)` from `ea : Eq M a1 a2` and
/// `eb : Eq M b1 b2`, by two transports in each direction.
fn rel2_minor_body(
    kernel: &mut crate::Kernel,
    e: &Env,
    k: ExprId,
    a1: ExprId,
    a2: ExprId,
    b1: ExprId,
    b2: ExprId,
    ea: ExprId,
    eb: ExprId,
    blk: u64,
) -> ExprId {
    let lhs = field(kernel, e, e.sem.rel2, &[k, a1, b1]);
    let rhs = field(kernel, e, e.sem.rel2, &[k, a2, b2]);

    let mp = {
        let p_id = blk;
        let p = kernel.fvar(p_id);
        // first slot: a1 -> a2, keeping b1
        let motive1 = geq_motive(
            kernel,
            e.logic,
            e.m,
            a1,
            &|kernel, z| field(kernel, e, e.sem.rel2, &[k, z, b1]),
            blk + 1,
        );
        let mid = gtransport(kernel, e.logic, e.m, a1, motive1, p, a2, ea);
        // second slot: b1 -> b2, keeping a2
        let motive2 = geq_motive(
            kernel,
            e.logic,
            e.m,
            b1,
            &|kernel, z| field(kernel, e, e.sem.rel2, &[k, a2, z]),
            blk + 2,
        );
        let body = gtransport(kernel, e.logic, e.m, b1, motive2, mid, b2, eb);
        lam_fv(kernel, p_id, lhs, body)
    };
    let mpr = {
        let q_id = blk + 3;
        let q = kernel.fvar(q_id);
        let back_a = gsymm(kernel, e.logic, e.m, a1, a2, ea, blk + 4);
        let back_b = gsymm(kernel, e.logic, e.m, b1, b2, eb, blk + 5);
        let motive1 = geq_motive(
            kernel,
            e.logic,
            e.m,
            a2,
            &|kernel, z| field(kernel, e, e.sem.rel2, &[k, z, b2]),
            blk + 6,
        );
        let mid = gtransport(kernel, e.logic, e.m, a2, motive1, q, a1, back_a);
        let motive2 = geq_motive(
            kernel,
            e.logic,
            e.m,
            b2,
            &|kernel, z| field(kernel, e, e.sem.rel2, &[k, a1, z]),
            blk + 7,
        );
        let body = gtransport(kernel, e.logic, e.m, b2, motive2, mid, b1, back_b);
        lam_fv(kernel, q_id, rhs, body)
    };
    iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
}

/// `Iff (And a1 b1) (And a2 b2)` from `Iff a1 a2` and `Iff b1 b2`.
fn and_minor_body(
    kernel: &mut crate::Kernel,
    e: &Env,
    a1: ExprId,
    a2: ExprId,
    b1: ExprId,
    b2: ExprId,
    ia: ExprId,
    ib: ExprId,
    blk: u64,
) -> ExprId {
    let and_const = kernel.const_(e.logic.and, vec![]);
    let lhs = apply_all(kernel, and_const, &[a1, b1]);
    let and_const = kernel.const_(e.logic.and, vec![]);
    let rhs = apply_all(kernel, and_const, &[a2, b2]);

    let build = |kernel: &mut crate::Kernel, forward: bool, fv: u64| -> ExprId {
        let (src, dst, sa, da, sb, db) = if forward {
            (lhs, rhs, a1, a2, b1, b2)
        } else {
            (rhs, lhs, a2, a1, b2, b1)
        };
        let x = kernel.fvar(fv);
        let left_const = kernel.const_(e.logic.and_left, vec![]);
        let left = apply_all(kernel, left_const, &[sa, sb, x]);
        let right_const = kernel.const_(e.logic.and_right, vec![]);
        let right = apply_all(kernel, right_const, &[sa, sb, x]);
        let (fa, fb) = if forward {
            let fa = iff_mp(kernel, e.logic, a1, a2, ia);
            let fb = iff_mp(kernel, e.logic, b1, b2, ib);
            (fa, fb)
        } else {
            let fa = iff_mpr(kernel, e.logic, a1, a2, ia);
            let fb = iff_mpr(kernel, e.logic, b1, b2, ib);
            (fa, fb)
        };
        let la = kernel.app(fa, left);
        let rb = kernel.app(fb, right);
        let intro = kernel.const_(e.logic.and_intro, vec![]);
        let body = apply_all(kernel, intro, &[da, db, la, rb]);
        let _ = dst;
        lam_fv(kernel, fv, src, body)
    };

    let mp = build(kernel, true, blk);
    let mpr = build(kernel, false, blk + 1);
    iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
}

/// `Iff (Or a1 b1) (Or a2 b2)` from `Iff a1 a2` and `Iff b1 b2`.
fn or_minor_body(
    kernel: &mut crate::Kernel,
    e: &Env,
    a1: ExprId,
    a2: ExprId,
    b1: ExprId,
    b2: ExprId,
    ia: ExprId,
    ib: ExprId,
    blk: u64,
) -> ExprId {
    let or_const = kernel.const_(e.logic.or, vec![]);
    let lhs = apply_all(kernel, or_const, &[a1, b1]);
    let or_const = kernel.const_(e.logic.or, vec![]);
    let rhs = apply_all(kernel, or_const, &[a2, b2]);

    let build = |kernel: &mut crate::Kernel, forward: bool, fv: u64| -> ExprId {
        let (src, dst, sa, sb, da, db) = if forward {
            (lhs, rhs, a1, b1, a2, b2)
        } else {
            (rhs, lhs, a2, b2, a1, b1)
        };
        let x = kernel.fvar(fv);
        let left_branch = {
            let h_id = fv + 100;
            let h = kernel.fvar(h_id);
            let f = if forward {
                iff_mp(kernel, e.logic, a1, a2, ia)
            } else {
                iff_mpr(kernel, e.logic, a1, a2, ia)
            };
            let moved = kernel.app(f, h);
            let inl = kernel.const_(e.logic.or_inl, vec![]);
            let injected = apply_all(kernel, inl, &[da, db, moved]);
            lam_fv(kernel, h_id, sa, injected)
        };
        let right_branch = {
            let h_id = fv + 200;
            let h = kernel.fvar(h_id);
            let f = if forward {
                iff_mp(kernel, e.logic, b1, b2, ib)
            } else {
                iff_mpr(kernel, e.logic, b1, b2, ib)
            };
            let moved = kernel.app(f, h);
            let inr = kernel.const_(e.logic.or_inr, vec![]);
            let injected = apply_all(kernel, inr, &[da, db, moved]);
            lam_fv(kernel, h_id, sb, injected)
        };
        let elim = kernel.const_(e.logic.or_elim, vec![]);
        let body = apply_all(kernel, elim, &[sa, sb, dst, x, left_branch, right_branch]);
        lam_fv(kernel, fv, src, body)
    };

    let mp = build(kernel, true, blk);
    let mpr = build(kernel, false, blk + 1);
    iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
}

/// `Iff (a1 -> b1) (a2 -> b2)` from `Iff a1 a2` and `Iff b1 b2`. The forward
/// direction consumes `ia`'s BACKWARD half — the reason `sat_congr`'s motive
/// has to be an `Iff`.
fn imp_minor_body(
    kernel: &mut crate::Kernel,
    e: &Env,
    a1: ExprId,
    a2: ExprId,
    b1: ExprId,
    b2: ExprId,
    ia: ExprId,
    ib: ExprId,
    blk: u64,
) -> ExprId {
    let lhs = arrow(kernel, a1, b1);
    let rhs = arrow(kernel, a2, b2);

    let mp = {
        let x_id = blk;
        let y_id = blk + 1;
        let x = kernel.fvar(x_id);
        let y = kernel.fvar(y_id);
        let back = iff_mpr(kernel, e.logic, a1, a2, ia);
        let in_a1 = kernel.app(back, y);
        let in_b1 = kernel.app(x, in_a1);
        let fwd = iff_mp(kernel, e.logic, b1, b2, ib);
        let in_b2 = kernel.app(fwd, in_b1);
        let inner = lam_fv(kernel, y_id, a2, in_b2);
        lam_fv(kernel, x_id, lhs, inner)
    };
    let mpr = {
        let x_id = blk + 2;
        let y_id = blk + 3;
        let x = kernel.fvar(x_id);
        let y = kernel.fvar(y_id);
        let fwd = iff_mp(kernel, e.logic, a1, a2, ia);
        let in_a2 = kernel.app(fwd, y);
        let in_b2 = kernel.app(x, in_a2);
        let back = iff_mpr(kernel, e.logic, b1, b2, ib);
        let in_b1 = kernel.app(back, in_b2);
        let inner = lam_fv(kernel, y_id, a1, in_b1);
        lam_fv(kernel, x_id, rhs, inner)
    };
    iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
}

/// `FO.sat_congr : Π M S p w1 w2, (Π n, Eq M (w1 n) (w2 n))
/// -> Iff (sat M S p w1) (sat M S p w2)`.
fn declare_sat_congr(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
    eval_congr: NameId,
    val_cons_congr: NameId,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);
    let base = 1_638_300_u64;

    // motive_at p := Π (w1 w2 : Nat -> M) (h : ptwise), Iff (sat p w1) (sat p w2)
    let motive_at = |kernel: &mut crate::Kernel, p: ExprId, blk: u64| -> ExprId {
        let w1_id = blk;
        let w2_id = blk + 1;
        let h_id = blk + 2;
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 3);
        let l = sat_of(kernel, &e, p, w1);
        let r = sat_of(kernel, &e, p, w2);
        let concl = iff_ty(kernel, e.logic, l, r);
        pis(
            kernel,
            &[(w1_id, e.val_ty), (w2_id, e.val_ty), (h_id, hyp)],
            concl,
        )
    };

    let motive = {
        let p_id = base;
        let p = kernel.fvar(p_id);
        let body = motive_at(kernel, p, base + 1);
        lam_fv(kernel, p_id, e.syn.formula_ty, body)
    };

    // `FO.Term.eval_congr M S t w1 w2 h`
    let term_congr =
        |kernel: &mut crate::Kernel, t: ExprId, w1: ExprId, w2: ExprId, h: ExprId| -> ExprId {
            let c = kernel.const_(eval_congr, vec![]);
            apply_all(kernel, c, &[e.m, e.s, t, w1, w2, h])
        };

    // m_bot := fun w1 w2 h => Iff.intro id id
    let m_bot = {
        let blk = base + 10;
        let w1_id = blk;
        let w2_id = blk + 1;
        let h_id = blk + 2;
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 3);
        let false_ = kernel.const_(e.logic.false_, vec![]);
        let body = giff_refl(kernel, e.logic, false_, blk + 4);
        lams(
            kernel,
            &[(w1_id, e.val_ty), (w2_id, e.val_ty), (h_id, hyp)],
            body,
        )
    };

    // m_eqf := fun a b w1 w2 h => ...
    let m_eqf = {
        let blk = base + 20;
        let a_id = blk;
        let b_id = blk + 1;
        let w1_id = blk + 2;
        let w2_id = blk + 3;
        let h_id = blk + 4;
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 5);
        let a1 = ev(kernel, &e, a, w1);
        let a2 = ev(kernel, &e, a, w2);
        let b1 = ev(kernel, &e, b, w1);
        let b2 = ev(kernel, &e, b, w2);
        let ea = term_congr(kernel, a, w1, w2, h);
        let eb = term_congr(kernel, b, w1, w2, h);
        let body = eqf_minor_body(kernel, &e, a1, a2, b1, b2, ea, eb, blk + 6);
        lams(
            kernel,
            &[
                (a_id, e.syn.term_ty),
                (b_id, e.syn.term_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    // m_rel1 := fun k t w1 w2 h => ...
    let m_rel1 = {
        let blk = base + 40;
        let k_id = blk;
        let t_id = blk + 1;
        let w1_id = blk + 2;
        let w2_id = blk + 3;
        let h_id = blk + 4;
        let k = kernel.fvar(k_id);
        let t = kernel.fvar(t_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 5);
        let x1 = ev(kernel, &e, t, w1);
        let x2 = ev(kernel, &e, t, w2);
        let et = term_congr(kernel, t, w1, w2, h);
        let body = rel1_minor_body(kernel, &e, k, x1, x2, et, blk + 6);
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (t_id, e.syn.term_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    // m_rel2 := fun k a b w1 w2 h => ...
    let m_rel2 = {
        let blk = base + 60;
        let k_id = blk;
        let a_id = blk + 1;
        let b_id = blk + 2;
        let w1_id = blk + 3;
        let w2_id = blk + 4;
        let h_id = blk + 5;
        let k = kernel.fvar(k_id);
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 6);
        let a1 = ev(kernel, &e, a, w1);
        let a2 = ev(kernel, &e, a, w2);
        let b1 = ev(kernel, &e, b, w1);
        let b2 = ev(kernel, &e, b, w2);
        let ea = term_congr(kernel, a, w1, w2, h);
        let eb = term_congr(kernel, b, w1, w2, h);
        let body = rel2_minor_body(kernel, &e, k, a1, a2, b1, b2, ea, eb, blk + 7);
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (a_id, e.syn.term_ty),
                (b_id, e.syn.term_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };

    // The three binary connectives share a shape.
    let binary = |kernel: &mut crate::Kernel, which: u8, blk: u64| -> ExprId {
        let p_id = blk;
        let q_id = blk + 1;
        let ip_id = blk + 2;
        let iq_id = blk + 3;
        let w1_id = blk + 4;
        let w2_id = blk + 5;
        let h_id = blk + 6;
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let ip = kernel.fvar(ip_id);
        let iq = kernel.fvar(iq_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 7);
        let ip_ty = motive_at(kernel, p, blk + 8);
        let iq_ty = motive_at(kernel, q, blk + 12);

        let a1 = sat_of(kernel, &e, p, w1);
        let a2 = sat_of(kernel, &e, p, w2);
        let b1 = sat_of(kernel, &e, q, w1);
        let b2 = sat_of(kernel, &e, q, w2);
        let ia = apply_all(kernel, ip, &[w1, w2, h]);
        let ib = apply_all(kernel, iq, &[w1, w2, h]);
        let body = match which {
            0 => and_minor_body(kernel, &e, a1, a2, b1, b2, ia, ib, blk + 16),
            1 => or_minor_body(kernel, &e, a1, a2, b1, b2, ia, ib, blk + 20),
            _ => imp_minor_body(kernel, &e, a1, a2, b1, b2, ia, ib, blk + 24),
        };
        lams(
            kernel,
            &[
                (p_id, e.syn.formula_ty),
                (q_id, e.syn.formula_ty),
                (ip_id, ip_ty),
                (iq_id, iq_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };
    let m_and = binary(kernel, 0, base + 80);
    let m_or = binary(kernel, 1, base + 120);
    let m_imp = binary(kernel, 2, base + 160);

    // The two quantifier minors.
    let quantifier = |kernel: &mut crate::Kernel, universal: bool, blk: u64| -> ExprId {
        let p_id = blk;
        let ip_id = blk + 1;
        let w1_id = blk + 2;
        let w2_id = blk + 3;
        let h_id = blk + 4;
        let p = kernel.fvar(p_id);
        let ip = kernel.fvar(ip_id);
        let w1 = kernel.fvar(w1_id);
        let w2 = kernel.fvar(w2_id);
        let h = kernel.fvar(h_id);
        let hyp = pointwise(kernel, &e, w1, w2, blk + 5);
        let ip_ty = motive_at(kernel, p, blk + 6);

        // key z := FO.Val.cons_congr M z w1 w2 h : Π n, Eq M (cons z w1 n) (cons z w2 n)
        let key_at = |kernel: &mut crate::Kernel, z: ExprId| -> ExprId {
            let c = kernel.const_(val_cons_congr, vec![]);
            apply_all(kernel, c, &[e.m, z, w1, w2, h])
        };

        let body = if universal {
            let all_side = |kernel: &mut crate::Kernel, w: ExprId, fv: u64| -> ExprId {
                let z = kernel.fvar(fv);
                let extended = vcons(kernel, &e, z, w);
                let inner = sat_of(kernel, &e, p, extended);
                pi_fv(kernel, fv, e.m, inner)
            };
            let lhs = all_side(kernel, w1, blk + 10);
            let rhs = all_side(kernel, w2, blk + 10);
            let build = |kernel: &mut crate::Kernel, forward: bool, fv: u64| -> ExprId {
                let (src, _dst) = if forward { (lhs, rhs) } else { (rhs, lhs) };
                let x_id = fv;
                let z_id = fv + 1;
                let x = kernel.fvar(x_id);
                let z = kernel.fvar(z_id);
                let e1 = vcons(kernel, &e, z, w1);
                let e2 = vcons(kernel, &e, z, w2);
                let sub_iff = {
                    let key = key_at(kernel, z);
                    apply_all(kernel, ip, &[e1, e2, key])
                };
                let s1 = sat_of(kernel, &e, p, e1);
                let s2 = sat_of(kernel, &e, p, e2);
                let mover = if forward {
                    iff_mp(kernel, e.logic, s1, s2, sub_iff)
                } else {
                    iff_mpr(kernel, e.logic, s1, s2, sub_iff)
                };
                let applied = kernel.app(x, z);
                let moved = kernel.app(mover, applied);
                let inner = lam_fv(kernel, z_id, e.m, moved);
                lam_fv(kernel, x_id, src, inner)
            };
            let mp = build(kernel, true, blk + 20);
            let mpr = build(kernel, false, blk + 30);
            iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
        } else {
            let pred = |kernel: &mut crate::Kernel, w: ExprId, fv: u64| -> ExprId {
                let z = kernel.fvar(fv);
                let extended = vcons(kernel, &e, z, w);
                let inner = sat_of(kernel, &e, p, extended);
                lam_fv(kernel, fv, e.m, inner)
            };
            let pred1 = pred(kernel, w1, blk + 40);
            let pred2 = pred(kernel, w2, blk + 40);
            let exists_const = kernel.const_(e.logic.exists_, vec![e.one]);
            let lhs = apply_all(kernel, exists_const, &[e.m, pred1]);
            let exists_const = kernel.const_(e.logic.exists_, vec![e.one]);
            let rhs = apply_all(kernel, exists_const, &[e.m, pred2]);
            let build = |kernel: &mut crate::Kernel, forward: bool, fv: u64| -> ExprId {
                let (src, dst, src_pred, dst_pred) = if forward {
                    (lhs, rhs, pred1, pred2)
                } else {
                    (rhs, lhs, pred2, pred1)
                };
                let x_id = fv;
                let z_id = fv + 1;
                let hz_id = fv + 2;
                let x = kernel.fvar(x_id);
                let z = kernel.fvar(z_id);
                let hz = kernel.fvar(hz_id);
                let e1 = vcons(kernel, &e, z, w1);
                let e2 = vcons(kernel, &e, z, w2);
                let sub_iff = {
                    let key = key_at(kernel, z);
                    apply_all(kernel, ip, &[e1, e2, key])
                };
                let s1 = sat_of(kernel, &e, p, e1);
                let s2 = sat_of(kernel, &e, p, e2);
                let mover = if forward {
                    iff_mp(kernel, e.logic, s1, s2, sub_iff)
                } else {
                    iff_mpr(kernel, e.logic, s1, s2, sub_iff)
                };
                let moved = kernel.app(mover, hz);
                let intro = kernel.const_(e.logic.exists_intro, vec![e.one]);
                let injected = apply_all(kernel, intro, &[e.m, dst_pred, z, moved]);
                let hz_ty = kernel.app(src_pred, z);
                let minor = {
                    let inner = lam_fv(kernel, hz_id, hz_ty, injected);
                    lam_fv(kernel, z_id, e.m, inner)
                };
                // The `Exists.rec` motive is constant: `fun (_ : src) => dst`.
                let rec_motive = {
                    let anon = kernel.anon();
                    kernel.lam(anon, src, dst, BinderInfo::Default)
                };
                let rec_const = kernel.const_(e.logic.exists_rec, vec![e.one]);
                let eliminated =
                    apply_all(kernel, rec_const, &[e.m, src_pred, rec_motive, minor, x]);
                lam_fv(kernel, x_id, src, eliminated)
            };
            let mp = build(kernel, true, blk + 50);
            let mpr = build(kernel, false, blk + 60);
            iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
        };

        lams(
            kernel,
            &[
                (p_id, e.syn.formula_ty),
                (ip_id, ip_ty),
                (w1_id, e.val_ty),
                (w2_id, e.val_ty),
                (h_id, hyp),
            ],
            body,
        )
    };
    let m_all = quantifier(kernel, true, base + 200);
    let m_ex = quantifier(kernel, false, base + 300);

    let zero_lvl = kernel.level_zero();
    let rec_const = kernel.const_(e.syn.formula_rec, vec![zero_lvl]);
    let applied = apply_all(
        kernel,
        rec_const,
        &[
            motive, m_bot, m_eqf, m_rel1, m_rel2, m_and, m_or, m_imp, m_all, m_ex,
        ],
    );

    let p_id = base + 400;
    let p = kernel.fvar(p_id);
    let body = kernel.app(applied, p);
    let value = lam_fv(kernel, p_id, e.syn.formula_ty, body);
    let concl = motive_at(kernel, p, base + 401);
    let ty = pi_fv(kernel, p_id, e.syn.formula_ty, concl);

    let name = kernel.name_str(e.syn.fo, "sat_congr");
    declare_ambient(kernel, &e, name, ty, value)
}

/// `FO.sat_subst : Π M S p s w, Iff (sat (Formula.subst p s) w)
/// (sat p (fun n => Term.eval M S (s n) w))` — the substitution lemma.
fn declare_sat_subst(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
    eval_subst: NameId,
    sat_congr: NameId,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);
    let base = 1_639_000_u64;
    let syntax = sem.syntax;

    let fsub = |kernel: &mut crate::Kernel, p: ExprId, s: ExprId| -> ExprId {
        let c = kernel.const_(syntax.formula_subst, vec![]);
        apply_all(kernel, c, &[p, s])
    };
    let tsub = |kernel: &mut crate::Kernel, t: ExprId, s: ExprId| -> ExprId {
        let c = kernel.const_(syntax.term_subst, vec![]);
        apply_all(kernel, c, &[t, s])
    };
    // `FO.Term.eval_subst M S t s w`
    let term_sub_eq = |kernel: &mut crate::Kernel, t: ExprId, s: ExprId, w: ExprId| -> ExprId {
        let c = kernel.const_(eval_subst, vec![]);
        apply_all(kernel, c, &[e.m, e.s, t, s, w])
    };

    // motive_at p := Π (s : Nat -> Term) (w : Nat -> M),
    //   Iff (sat (Formula.subst p s) w) (sat p (fun n => eval (s n) w))
    let motive_at = |kernel: &mut crate::Kernel, p: ExprId, blk: u64| -> ExprId {
        let s_id = blk;
        let w_id = blk + 1;
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let substituted = fsub(kernel, p, s);
        let l = sat_of(kernel, &e, substituted, w);
        let composed = compose(kernel, &e, s, w, blk + 2);
        let r = sat_of(kernel, &e, p, composed);
        let concl = iff_ty(kernel, e.logic, l, r);
        pis(kernel, &[(s_id, e.sub_ty), (w_id, e.val_ty)], concl)
    };

    let motive = {
        let p_id = base;
        let p = kernel.fvar(p_id);
        let body = motive_at(kernel, p, base + 1);
        lam_fv(kernel, p_id, e.syn.formula_ty, body)
    };

    let m_bot = {
        let blk = base + 10;
        let s_id = blk;
        let w_id = blk + 1;
        let false_ = kernel.const_(e.logic.false_, vec![]);
        let body = giff_refl(kernel, e.logic, false_, blk + 2);
        lams(kernel, &[(s_id, e.sub_ty), (w_id, e.val_ty)], body)
    };

    let m_eqf = {
        let blk = base + 20;
        let a_id = blk;
        let b_id = blk + 1;
        let s_id = blk + 2;
        let w_id = blk + 3;
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let a_sub = tsub(kernel, a, s);
        let b_sub = tsub(kernel, b, s);
        let a1 = ev(kernel, &e, a_sub, w);
        let b1 = ev(kernel, &e, b_sub, w);
        let composed = compose(kernel, &e, s, w, blk + 4);
        let a2 = ev(kernel, &e, a, composed);
        let b2 = ev(kernel, &e, b, composed);
        let ea = term_sub_eq(kernel, a, s, w);
        let eb = term_sub_eq(kernel, b, s, w);
        let body = eqf_minor_body(kernel, &e, a1, a2, b1, b2, ea, eb, blk + 5);
        lams(
            kernel,
            &[
                (a_id, e.syn.term_ty),
                (b_id, e.syn.term_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };

    let m_rel1 = {
        let blk = base + 40;
        let k_id = blk;
        let t_id = blk + 1;
        let s_id = blk + 2;
        let w_id = blk + 3;
        let k = kernel.fvar(k_id);
        let t = kernel.fvar(t_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let t_sub = tsub(kernel, t, s);
        let x1 = ev(kernel, &e, t_sub, w);
        let composed = compose(kernel, &e, s, w, blk + 4);
        let x2 = ev(kernel, &e, t, composed);
        let et = term_sub_eq(kernel, t, s, w);
        let body = rel1_minor_body(kernel, &e, k, x1, x2, et, blk + 5);
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (t_id, e.syn.term_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };

    let m_rel2 = {
        let blk = base + 60;
        let k_id = blk;
        let a_id = blk + 1;
        let b_id = blk + 2;
        let s_id = blk + 3;
        let w_id = blk + 4;
        let k = kernel.fvar(k_id);
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let a_sub = tsub(kernel, a, s);
        let b_sub = tsub(kernel, b, s);
        let a1 = ev(kernel, &e, a_sub, w);
        let b1 = ev(kernel, &e, b_sub, w);
        let composed = compose(kernel, &e, s, w, blk + 5);
        let a2 = ev(kernel, &e, a, composed);
        let b2 = ev(kernel, &e, b, composed);
        let ea = term_sub_eq(kernel, a, s, w);
        let eb = term_sub_eq(kernel, b, s, w);
        let body = rel2_minor_body(kernel, &e, k, a1, a2, b1, b2, ea, eb, blk + 6);
        lams(
            kernel,
            &[
                (k_id, e.syn.nat_ty),
                (a_id, e.syn.term_ty),
                (b_id, e.syn.term_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };

    let binary = |kernel: &mut crate::Kernel, which: u8, blk: u64| -> ExprId {
        let p_id = blk;
        let q_id = blk + 1;
        let ip_id = blk + 2;
        let iq_id = blk + 3;
        let s_id = blk + 4;
        let w_id = blk + 5;
        let p = kernel.fvar(p_id);
        let q = kernel.fvar(q_id);
        let ip = kernel.fvar(ip_id);
        let iq = kernel.fvar(iq_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let ip_ty = motive_at(kernel, p, blk + 6);
        let iq_ty = motive_at(kernel, q, blk + 10);

        let p_sub = fsub(kernel, p, s);
        let q_sub = fsub(kernel, q, s);
        let a1 = sat_of(kernel, &e, p_sub, w);
        let b1 = sat_of(kernel, &e, q_sub, w);
        let composed = compose(kernel, &e, s, w, blk + 14);
        let a2 = sat_of(kernel, &e, p, composed);
        let b2 = sat_of(kernel, &e, q, composed);
        let ia = apply_all(kernel, ip, &[s, w]);
        let ib = apply_all(kernel, iq, &[s, w]);
        let body = match which {
            0 => and_minor_body(kernel, &e, a1, a2, b1, b2, ia, ib, blk + 16),
            1 => or_minor_body(kernel, &e, a1, a2, b1, b2, ia, ib, blk + 20),
            _ => imp_minor_body(kernel, &e, a1, a2, b1, b2, ia, ib, blk + 24),
        };
        lams(
            kernel,
            &[
                (p_id, e.syn.formula_ty),
                (q_id, e.syn.formula_ty),
                (ip_id, ip_ty),
                (iq_id, iq_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };
    let m_and = binary(kernel, 0, base + 80);
    let m_or = binary(kernel, 1, base + 120);
    let m_imp = binary(kernel, 2, base + 160);

    let quantifier = |kernel: &mut crate::Kernel, universal: bool, blk: u64| -> ExprId {
        let p_id = blk;
        let ip_id = blk + 1;
        let s_id = blk + 2;
        let w_id = blk + 3;
        let p = kernel.fvar(p_id);
        let ip = kernel.fvar(ip_id);
        let s = kernel.fvar(s_id);
        let w = kernel.fvar(w_id);
        let ip_ty = motive_at(kernel, p, blk + 4);

        let lift_const = kernel.const_(syntax.subst_lift, vec![]);
        let lifted = kernel.app(lift_const, s);
        let composed = compose(kernel, &e, s, w, blk + 8);
        let p_sub = fsub(kernel, p, lifted);

        // key z : Π n, Eq M (eval (lift s n) (Val.cons M z w)) (Val.cons M z w' n)
        //   n = 0      : both sides reduce to z            -> Eq.refl
        //   n = succ k : exactly FO.Term.eval_subst at (s k, Subst.shift)
        let key_at = |kernel: &mut crate::Kernel, z: ExprId, kblk: u64| -> ExprId {
            let extended = vcons(kernel, &e, z, w);
            let goal_at = |kernel: &mut crate::Kernel, idx: ExprId| -> ExprId {
                let lifted_at = kernel.app(lifted, idx);
                let left = ev(kernel, &e, lifted_at, extended);
                let right = vcons(kernel, &e, z, composed);
                let right = kernel.app(right, idx);
                eqm(kernel, &e, left, right)
            };
            let key_motive = {
                let mv_id = kblk;
                let mv = kernel.fvar(mv_id);
                let body = goal_at(kernel, mv);
                lam_fv(kernel, mv_id, e.syn.nat_ty, body)
            };
            let key_base = grefl(kernel, e.logic, e.m, z);
            let key_step = {
                let k_id = kblk + 1;
                let ih_id = kblk + 2;
                let k = kernel.fvar(k_id);
                let ih_ty = goal_at(kernel, k);
                let s_k = kernel.app(s, k);
                let shift_const = kernel.const_(syntax.subst_shift, vec![]);
                let body = term_sub_eq(kernel, s_k, shift_const, extended);
                lams(kernel, &[(k_id, e.syn.nat_ty), (ih_id, ih_ty)], body)
            };
            let n_id = kblk + 3;
            let n = kernel.fvar(n_id);
            let zero_lvl = kernel.level_zero();
            let nat_rec = kernel.const_(e.syn.nat_rec, vec![zero_lvl]);
            let applied = apply_all(kernel, nat_rec, &[key_motive, key_base, key_step, n]);
            lam_fv(kernel, n_id, e.syn.nat_ty, applied)
        };

        // `FO.sat_congr M S p wa wb key : Iff (sat p wa) (sat p wb)`
        let congr_at =
            |kernel: &mut crate::Kernel, wa: ExprId, wb: ExprId, key: ExprId| -> ExprId {
                let c = kernel.const_(sat_congr, vec![]);
                apply_all(kernel, c, &[e.m, e.s, p, wa, wb, key])
            };

        let body = if universal {
            let lhs = {
                let fv = blk + 10;
                let z = kernel.fvar(fv);
                let extended = vcons(kernel, &e, z, w);
                let inner = sat_of(kernel, &e, p_sub, extended);
                pi_fv(kernel, fv, e.m, inner)
            };
            let rhs = {
                let fv = blk + 11;
                let z = kernel.fvar(fv);
                let extended = vcons(kernel, &e, z, composed);
                let inner = sat_of(kernel, &e, p, extended);
                pi_fv(kernel, fv, e.m, inner)
            };
            let build = |kernel: &mut crate::Kernel, forward: bool, fv: u64| -> ExprId {
                let src = if forward { lhs } else { rhs };
                let x_id = fv;
                let z_id = fv + 1;
                let x = kernel.fvar(x_id);
                let z = kernel.fvar(z_id);
                let extended = vcons(kernel, &e, z, w);
                let inner_iff = apply_all(kernel, ip, &[lifted, extended]);
                let mid_val = {
                    let composed_lift = compose(kernel, &e, lifted, extended, fv + 2);
                    composed_lift
                };
                let end_val = vcons(kernel, &e, z, composed);
                let key = key_at(kernel, z, fv + 3);
                let outer_iff = congr_at(kernel, mid_val, end_val, key);

                let s_left = sat_of(kernel, &e, p_sub, extended);
                let s_mid = sat_of(kernel, &e, p, mid_val);
                let s_right = sat_of(kernel, &e, p, end_val);

                let applied = kernel.app(x, z);
                let moved = if forward {
                    let step1 = iff_mp(kernel, e.logic, s_left, s_mid, inner_iff);
                    let v1 = kernel.app(step1, applied);
                    let step2 = iff_mp(kernel, e.logic, s_mid, s_right, outer_iff);
                    kernel.app(step2, v1)
                } else {
                    let step2 = iff_mpr(kernel, e.logic, s_mid, s_right, outer_iff);
                    let v1 = kernel.app(step2, applied);
                    let step1 = iff_mpr(kernel, e.logic, s_left, s_mid, inner_iff);
                    kernel.app(step1, v1)
                };
                let inner = lam_fv(kernel, z_id, e.m, moved);
                lam_fv(kernel, x_id, src, inner)
            };
            let mp = build(kernel, true, blk + 20);
            let mpr = build(kernel, false, blk + 40);
            iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
        } else {
            let pred_left = {
                let fv = blk + 60;
                let z = kernel.fvar(fv);
                let extended = vcons(kernel, &e, z, w);
                let inner = sat_of(kernel, &e, p_sub, extended);
                lam_fv(kernel, fv, e.m, inner)
            };
            let pred_right = {
                let fv = blk + 61;
                let z = kernel.fvar(fv);
                let extended = vcons(kernel, &e, z, composed);
                let inner = sat_of(kernel, &e, p, extended);
                lam_fv(kernel, fv, e.m, inner)
            };
            let exists_const = kernel.const_(e.logic.exists_, vec![e.one]);
            let lhs = apply_all(kernel, exists_const, &[e.m, pred_left]);
            let exists_const = kernel.const_(e.logic.exists_, vec![e.one]);
            let rhs = apply_all(kernel, exists_const, &[e.m, pred_right]);
            let build = |kernel: &mut crate::Kernel, forward: bool, fv: u64| -> ExprId {
                let (src, dst, src_pred, dst_pred) = if forward {
                    (lhs, rhs, pred_left, pred_right)
                } else {
                    (rhs, lhs, pred_right, pred_left)
                };
                let x_id = fv;
                let z_id = fv + 1;
                let hz_id = fv + 2;
                let x = kernel.fvar(x_id);
                let z = kernel.fvar(z_id);
                let hz = kernel.fvar(hz_id);
                let extended = vcons(kernel, &e, z, w);
                let inner_iff = apply_all(kernel, ip, &[lifted, extended]);
                let mid_val = compose(kernel, &e, lifted, extended, fv + 3);
                let end_val = vcons(kernel, &e, z, composed);
                let key = key_at(kernel, z, fv + 4);
                let outer_iff = congr_at(kernel, mid_val, end_val, key);

                let s_left = sat_of(kernel, &e, p_sub, extended);
                let s_mid = sat_of(kernel, &e, p, mid_val);
                let s_right = sat_of(kernel, &e, p, end_val);

                let moved = if forward {
                    let step1 = iff_mp(kernel, e.logic, s_left, s_mid, inner_iff);
                    let v1 = kernel.app(step1, hz);
                    let step2 = iff_mp(kernel, e.logic, s_mid, s_right, outer_iff);
                    kernel.app(step2, v1)
                } else {
                    let step2 = iff_mpr(kernel, e.logic, s_mid, s_right, outer_iff);
                    let v1 = kernel.app(step2, hz);
                    let step1 = iff_mpr(kernel, e.logic, s_left, s_mid, inner_iff);
                    kernel.app(step1, v1)
                };
                let intro = kernel.const_(e.logic.exists_intro, vec![e.one]);
                let injected = apply_all(kernel, intro, &[e.m, dst_pred, z, moved]);
                let hz_ty = kernel.app(src_pred, z);
                let minor = {
                    let inner = lam_fv(kernel, hz_id, hz_ty, injected);
                    lam_fv(kernel, z_id, e.m, inner)
                };
                // The `Exists.rec` motive is constant: `fun (_ : src) => dst`.
                let rec_motive = {
                    let anon = kernel.anon();
                    kernel.lam(anon, src, dst, BinderInfo::Default)
                };
                let rec_const = kernel.const_(e.logic.exists_rec, vec![e.one]);
                let eliminated =
                    apply_all(kernel, rec_const, &[e.m, src_pred, rec_motive, minor, x]);
                lam_fv(kernel, x_id, src, eliminated)
            };
            let mp = build(kernel, true, blk + 70);
            let mpr = build(kernel, false, blk + 90);
            iff_intro(kernel, e.logic, lhs, rhs, mp, mpr)
        };

        lams(
            kernel,
            &[
                (p_id, e.syn.formula_ty),
                (ip_id, ip_ty),
                (s_id, e.sub_ty),
                (w_id, e.val_ty),
            ],
            body,
        )
    };
    let m_all = quantifier(kernel, true, base + 200);
    let m_ex = quantifier(kernel, false, base + 400);

    let zero_lvl = kernel.level_zero();
    let rec_const = kernel.const_(e.syn.formula_rec, vec![zero_lvl]);
    let applied = apply_all(
        kernel,
        rec_const,
        &[
            motive, m_bot, m_eqf, m_rel1, m_rel2, m_and, m_or, m_imp, m_all, m_ex,
        ],
    );

    let p_id = base + 600;
    let p = kernel.fvar(p_id);
    let body = kernel.app(applied, p);
    let value = lam_fv(kernel, p_id, e.syn.formula_ty, body);
    let concl = motive_at(kernel, p, base + 601);
    let ty = pi_fv(kernel, p_id, e.syn.formula_ty, concl);

    let name = kernel.name_str(e.syn.fo, "sat_subst");
    declare_ambient(kernel, &e, name, ty, value)
}

/// `FO.sat_shift : Π M S p w (a : M),
/// Iff (sat (Formula.shift p) (Val.cons M a w)) (sat p w)`.
///
/// The proof term is **`FO.sat_subst M S p FO.Subst.shift (FO.Val.cons M a w)`
/// and nothing else** — the stated type is that term's own type, written in
/// the form the kernel reduces it to. See the module docs for why the
/// right-hand valuation is definitionally `w`.
fn declare_sat_shift(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
    sat_subst: NameId,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);
    let syntax = sem.syntax;

    let p_id = 1_640_001_u64;
    let w_id = 1_640_002_u64;
    let a_id = 1_640_003_u64;
    let p = kernel.fvar(p_id);
    let w = kernel.fvar(w_id);
    let a = kernel.fvar(a_id);

    let shift_const = kernel.const_(syntax.subst_shift, vec![]);
    let extended = vcons(kernel, &e, a, w);
    let c = kernel.const_(sat_subst, vec![]);
    let value_body = apply_all(kernel, c, &[e.m, e.s, p, shift_const, extended]);

    let shifted = {
        let fshift = kernel.const_(syntax.formula_shift, vec![]);
        kernel.app(fshift, p)
    };
    let lhs = sat_of(kernel, &e, shifted, extended);
    let rhs = sat_of(kernel, &e, p, w);
    let concl = iff_ty(kernel, e.logic, lhs, rhs);

    let binders = [(p_id, e.syn.formula_ty), (w_id, e.val_ty), (a_id, e.m)];
    let ty = pis(kernel, &binders, concl);
    let value = lams(kernel, &binders, value_body);

    let name = kernel.name_str(e.syn.fo, "sat_shift");
    declare_ambient(kernel, &e, name, ty, value)
}

/// `FO.sat_inst : Π M S p t w, Iff (sat (Formula.subst p (Subst.cons t Subst.id)) w)
/// (sat p (Val.cons M (Term.eval M S t w) w))` — the `∀`-elimination /
/// `∃`-introduction corollary.
///
/// `sat_subst` at `Subst.cons t Subst.id`, composed with `sat_congr` along a
/// `Nat.rec` key whose **both** cases are `Eq.refl`: at `Nat.zero` the two
/// valuations reduce to `Term.eval M S t w`, and at `Nat.succ k` to `w k`.
fn declare_sat_inst(
    kernel: &mut crate::Kernel,
    sem: &FoSemanticsPrelude,
    sat_subst: NameId,
    sat_congr: NameId,
) -> Result<NameId, KernelError> {
    let e = Env::new(kernel, sem);
    let syntax = sem.syntax;
    let base = 1_640_100_u64;

    let p_id = base;
    let t_id = base + 1;
    let w_id = base + 2;
    let p = kernel.fvar(p_id);
    let t = kernel.fvar(t_id);
    let w = kernel.fvar(w_id);

    // sigma := FO.Subst.cons t FO.Subst.id
    let sigma = {
        let id = kernel.const_(syntax.subst_id, vec![]);
        let cons = kernel.const_(syntax.subst_cons, vec![]);
        apply_all(kernel, cons, &[t, id])
    };
    let substituted = {
        let c = kernel.const_(syntax.formula_subst, vec![]);
        apply_all(kernel, c, &[p, sigma])
    };
    let composed = compose(kernel, &e, sigma, w, base + 3);
    let t_val = ev(kernel, &e, t, w);
    let extended = vcons(kernel, &e, t_val, w);

    let a = sat_of(kernel, &e, substituted, w);
    let b = sat_of(kernel, &e, p, composed);
    let c_ = sat_of(kernel, &e, p, extended);

    let first = {
        let c = kernel.const_(sat_subst, vec![]);
        apply_all(kernel, c, &[e.m, e.s, p, sigma, w])
    };

    // key : Π n, Eq M (eval (sigma n) w) (Val.cons M (eval t w) w n)
    let key = {
        let goal_at = |kernel: &mut crate::Kernel, idx: ExprId| -> ExprId {
            let sigma_at = kernel.app(sigma, idx);
            let left = ev(kernel, &e, sigma_at, w);
            let right = kernel.app(extended, idx);
            eqm(kernel, &e, left, right)
        };
        let key_motive = {
            let mv_id = base + 10;
            let mv = kernel.fvar(mv_id);
            let body = goal_at(kernel, mv);
            lam_fv(kernel, mv_id, e.syn.nat_ty, body)
        };
        let key_base = grefl(kernel, e.logic, e.m, t_val);
        let key_step = {
            let k_id = base + 11;
            let ih_id = base + 12;
            let k = kernel.fvar(k_id);
            let ih_ty = goal_at(kernel, k);
            let w_k = kernel.app(w, k);
            let body = grefl(kernel, e.logic, e.m, w_k);
            lams(kernel, &[(k_id, e.syn.nat_ty), (ih_id, ih_ty)], body)
        };
        let n_id = base + 13;
        let n = kernel.fvar(n_id);
        let zero_lvl = kernel.level_zero();
        let nat_rec = kernel.const_(e.syn.nat_rec, vec![zero_lvl]);
        let applied = apply_all(kernel, nat_rec, &[key_motive, key_base, key_step, n]);
        lam_fv(kernel, n_id, e.syn.nat_ty, applied)
    };

    let second = {
        let c = kernel.const_(sat_congr, vec![]);
        apply_all(kernel, c, &[e.m, e.s, p, composed, extended, key])
    };

    let value_body = giff_trans(kernel, e.logic, a, b, c_, first, second, base + 20);
    let concl = iff_ty(kernel, e.logic, a, c_);

    let binders = [
        (p_id, e.syn.formula_ty),
        (t_id, e.syn.term_ty),
        (w_id, e.val_ty),
    ];
    let ty = pis(kernel, &binders, concl);
    let value = lams(kernel, &binders, value_body);

    let name = kernel.name_str(e.syn.fo, "sat_inst");
    declare_ambient(kernel, &e, name, ty, value)
}

#[cfg(test)]
mod tests;
