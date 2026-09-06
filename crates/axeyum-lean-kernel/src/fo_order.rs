//! **Q with order** (`fo_*.rs`, ADR-1669): Robinson's Q extended by the order
//! axioms that `FO.Q` alone cannot supply, its ℕ model, and its consistency.
//!
//! ```text
//! FO.Qle.axLtZero, FO.Qle.axLtSuccCases, FO.Qle.axLtSuccStep,
//! FO.Qle.axLtSelfSucc, FO.Qle.axLtAddRight, FO.Qle.axLtDest : FO.Formula
//! FO.Qle : FO.Context
//! FO.Qle.natModels : Π (v : Nat -> Nat), FO.ctxSat Nat FO.natStructureQ FO.Qle v
//! FO.Qle.consistency : Not (FO.Provable FO.Qle FO.Formula.bot)
//! ```
//!
//! ## Which axiom set, and why this one
//!
//! `fo_robinson.rs` put `<` in the signature (`FO.Formula.rel2 0`, interpreted
//! as `Nat.lt` in `FO.natStructureQ`) and then constrained it with nothing:
//! Q1–Q7 are the standard seven and none of them mentions the relation. That
//! is Robinson's Q as usually presented, and it is exactly why ADR-1651 could
//! not reach the uniqueness half of representability — **from Q4–Q7 one can
//! compute with numerals and nothing else**, so no statement of the form
//! `∀z (… z …)` with `z` genuinely constrained is derivable.
//!
//! The textbook repair adds the order. There are two usual spellings and this
//! slice takes BOTH halves of each:
//!
//! | | axiom | reading |
//! | --- | --- | --- |
//! | O1 | `∀x, ¬(x < 0)` | nothing is below zero |
//! | O2 | `∀y∀x, x < S y → (x < y ∨ x = y)` | discreteness, downward |
//! | O3 | `∀y∀x, x < y → x < S y` | discreteness, upward (left) |
//! | O4 | `∀x, x < S x` | discreteness, upward (right) |
//! | O5 | `∀y∀x, x < S (x + y)` | `x ≤ x + y`, the `∃`-characterisation ⇐ |
//! | O6 | `∀y∀x, x < S y → ∃z (x + z = y)` | `x ≤ y → ∃z (x+z=y)`, ⇒ |
//!
//! ### The binder order is `∀y∀x`, and that is forced, not cosmetic
//!
//! In every binary row the OUTER quantifier is the *bound* `y` and the inner
//! one is the *subject* `x`. Writing them the other way round would make the
//! axioms unusable at the one instantiation the next slice needs, and the
//! reason is `FO.Provable.all_elim`'s de Bruijn shape. Instantiating
//! `all (all φ)` at `(t₁, t₂)` puts `t₁` under `FO.Subst.lift`, i.e. under
//! `FO.Term.subst t₁ FO.Subst.shift`. That application ι-reduces whenever `t₁`
//! is a `var` or a closed literal term — but `FO.Term.numeral a` at a
//! **symbolic** `a` is a `Nat.rec` stuck on `a`, so it does not, and
//! `FO.Term.subst_numeral` (`fo_robinson.rs`) is the lemma that repairs it.
//! There is no such lemma for a `Π (t : FO.Term)`-bound term: nothing is known
//! about it, so a stuck `FO.Term.subst t FO.Subst.shift` in the OUTER position
//! can never be repaired. Putting the numeral outer and the arbitrary term
//! inner means every instantiation this family needs is
//! `(numeral n, arbitrary term)` — repairable on the left, free on the right.
//!
//! `≤` is not a separate symbol, and it could not be one without a second ℕ
//! structure: `FO.natStructureQ`'s binary relation family is
//! `rel2 k x y := Nat.lt (Nat.add x k) y`, so `rel2 0` is `<` and `rel2 1` is
//! `x + 1 < y` — **no index of that family is `Nat.le`**. Declaring a second
//! structure would force `FO.Q.natModels` to be re-proved at it for no gain,
//! so `x ≤ y` is spelled `x < S y` throughout, which is what it means in ℕ and
//! what O2/O4 make it mean here. O2 together with O3 and O4 is precisely the
//! biconditional `x < S y ↔ (x < y ∨ x = y)`, written as two implications
//! because `FO.Formula` has no `iff` constructor; O5 with O6 is precisely
//! `x < S y ↔ ∃z (x + z = y)`, likewise. So "the order axiom
//! `x ≤ y ↔ ∃z (z + x = y)`" and "the discreteness axiom" are both present in
//! full, and **neither is a schema** — there is one formula per row, not one
//! per numeral.
//!
//! **What is deliberately NOT here is induction.** `Qle` is still a finitely
//! axiomatised theory with no induction axiom and no induction schema. The
//! bounded case split a later slice needs is proved by induction *outside* the
//! calculus, one derivation per numeral, which is what keeps `Qle` weaker than
//! PA and keeps Gödel I applicable to it.
//!
//! ## The context, and why the order axioms come first
//!
//! `FO.Qle` is the six order axioms consed in front of `FO.Q`'s seven, so the
//! tail after the sixth cons is definitionally `FO.Q`. Two things fall out of
//! that ordering: `FO.Qle.natModels` is six `And.intro`s on top of
//! `FO.Q.natModels v` rather than a re-proof of the seven, and every `FO.Q`
//! axiom is reachable in `Qle` by the same `ax_head`-then-`weaken` chain the
//! order axioms use, at a uniform index into the thirteen.
//!
//! ## `ℕ ⊨ Qle`, and consistency
//!
//! Each order obligation is one application of an existing `Nat` order lemma,
//! and the goals arrive *reduced*: `sat (rel2 0 a b)` ι-reduces to
//! `Nat.lt (Nat.add (eval a) 0) (eval b)` and `Nat.add x 0` ι-reduces to `x`
//! (this kernel's `Nat.add` recurses on its right argument), so
//! `Nat.not_succ_le_zero`, `Nat.lt_or_eq_of_le ∘ Nat.le_of_lt_succ`,
//! `Nat.le.step`, `Nat.lt_succ_self`,
//! `Nat.lt_succ_of_le ∘ Nat.le_add_right` and
//! `Nat.le_dest ∘ Nat.le_of_lt_succ` close O1–O6 in that order with no
//! rewriting at all. `FO.Qle.consistency` is then `FO.soundness` at
//! `FO.natStructureQ` with the constant-zero valuation, exactly as
//! `FO.Q.consistency` is.

// Same variable-naming judgement as `fo_robinson.rs` and `fo_soundness.rs`:
// the one-letter names are the ones the literature uses for structures,
// valuations, substitutions, terms, formulas and contexts.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::fo_provable::{cons_app, provable_app};
use crate::fo_robinson::{Fv, Rob};
use crate::fo_syntax::{apply_all, lam_fv, lams, pi_fv};
use crate::{
    Declaration, ExprId, FoRobinsonPrelude, KernelError, NameId, ReducibilityHint,
    build_fo_robinson_prelude,
};

/// Names produced by [`build_fo_order_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoOrderPrelude {
    /// Robinson's Q, its ℕ model and the numeral arithmetic this slice extends.
    pub robinson: FoRobinsonPrelude,

    // --- the six order axioms ------------------------------------------------
    /// `FO.Qle.axLtZero : FO.Formula` — `∀x, ¬(x < 0)`.
    pub ax_lt_zero: NameId,
    /// `FO.Qle.axLtSuccCases : FO.Formula` — `∀x∀y, x < S y → (x < y ∨ x = y)`.
    pub ax_lt_succ_cases: NameId,
    /// `FO.Qle.axLtSuccStep : FO.Formula` — `∀x∀y, x < y → x < S y`.
    pub ax_lt_succ_step: NameId,
    /// `FO.Qle.axLtSelfSucc : FO.Formula` — `∀x, x < S x`.
    pub ax_lt_self_succ: NameId,
    /// `FO.Qle.axLtAddRight : FO.Formula` — `∀x∀y, x < S (x + y)`.
    pub ax_lt_add_right: NameId,
    /// `FO.Qle.axLtDest : FO.Formula` — `∀x∀y, x < S y → ∃z (x + z = y)`.
    pub ax_lt_dest: NameId,

    // --- the theory, its model, its consistency ------------------------------
    /// `FO.Qle : FO.Context` — the six order axioms in front of `FO.Q`.
    pub qle: NameId,
    /// `FO.Qle.natModels : Π v, FO.ctxSat Nat FO.natStructureQ FO.Qle v`.
    pub nat_models: NameId,
    /// `FO.Qle.consistency : Not (FO.Provable FO.Qle FO.Formula.bot)`.
    pub consistency: NameId,
}

/// The thirteen axioms of `FO.Qle`, in the order the context conses them: the
/// six order axioms, then `FO.Q`'s seven.
pub(crate) struct QleAxioms {
    pub(crate) order: [NameId; 6],
    pub(crate) robinson: [NameId; 7],
}

impl QleAxioms {
    /// The thirteen names in context order, so index `i` is the `i`th `cons`.
    pub(crate) fn ordered(&self) -> [NameId; 13] {
        let o = self.order;
        let q = self.robinson;
        [
            o[0], o[1], o[2], o[3], o[4], o[5], q[0], q[1], q[2], q[3], q[4], q[5], q[6],
        ]
    }
}

/// `fo_robinson.rs`'s combinator bundle plus the `FO.Qle` namespace, which is
/// also this context's own name.
pub(crate) struct Qle {
    /// Every combinator `fo_robinson.rs` already threads.
    pub(crate) r: Rob,
    /// `FO.Qle`.
    pub(crate) ns: NameId,
}

impl Qle {
    pub(crate) fn new(kernel: &mut crate::Kernel, r: Rob) -> Self {
        let ns = kernel.name_str(r.syn.fo, "Qle");
        Self { r, ns }
    }

    /// `a < b`, i.e. `FO.Formula.rel2 0 a b`.
    pub(crate) fn f_lt(&self, kernel: &mut crate::Kernel, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.r.nat_lit(kernel, 0);
        let head = kernel.const_(self.r.syn.rel2, vec![]);
        apply_all(kernel, head, &[idx, a, b])
    }

    /// `FO.Provable FO.Qle p`. Used by this module's tests; the lib build has
    /// no other caller until the derivations of the next slice land.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn prov(&self, kernel: &mut crate::Kernel, p: ExprId) -> ExprId {
        let ctx = kernel.const_(self.ns, vec![]);
        provable_app(kernel, &self.r.calc, ctx, p)
    }

    /// The context tail after the first `from` of the thirteen axioms —
    /// `FO.Context.nil` at `from = 13`.
    pub(crate) fn tail(
        &self,
        kernel: &mut crate::Kernel,
        axioms: &QleAxioms,
        from: usize,
    ) -> ExprId {
        let ordered = axioms.ordered();
        let mut acc = kernel.const_(self.r.calc.nil, vec![]);
        for &name in ordered[from..].iter().rev() {
            let head = kernel.const_(name, vec![]);
            acc = cons_app(kernel, &self.r.calc, head, acc);
        }
        acc
    }
}

/// Build `FO.Qle` on top of `FO.Q`: the order axioms, the context, `ℕ ⊨ Qle`
/// and consistency.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_order_prelude(kernel: &mut crate::Kernel) -> Result<FoOrderPrelude, KernelError> {
    let robinson = build_fo_robinson_prelude(kernel)?;
    let semantics = robinson.soundness.calculus.semantics;
    let calculus = robinson.soundness.calculus;
    let r = Rob::new(kernel, robinson.roundtrip, semantics, calculus);
    let q = Qle::new(kernel, r);
    let mut fv = Fv(1_669_000);

    let axioms = declare_order_axioms(kernel, &q, &robinson)?;
    let qle = declare_qle_context(kernel, &q, &axioms)?;
    let nat_models = declare_qle_nat_models(kernel, &q, &robinson, &axioms, qle, &mut fv)?;
    let consistency = declare_qle_consistency(kernel, &q, &robinson, qle, nat_models, &mut fv)?;

    Ok(FoOrderPrelude {
        robinson,
        ax_lt_zero: axioms.order[0],
        ax_lt_succ_cases: axioms.order[1],
        ax_lt_succ_step: axioms.order[2],
        ax_lt_self_succ: axioms.order[3],
        ax_lt_add_right: axioms.order[4],
        ax_lt_dest: axioms.order[5],
        qle,
        nat_models,
        consistency,
    })
}

// ============================================================================
// The six order axioms.
// ============================================================================

fn declare_formula(
    kernel: &mut crate::Kernel,
    q: &Qle,
    label: &str,
    value: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(q.ns, label);
    let ty = q.r.formula_ty;
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

fn declare_order_axioms(
    kernel: &mut crate::Kernel,
    q: &Qle,
    robinson: &FoRobinsonPrelude,
) -> Result<QleAxioms, KernelError> {
    let r = &q.r;

    // O1: all (imp (rel2 0 (var 0) 0) bot)
    let lt_zero = {
        let x = r.tvar(kernel, 0);
        let zero = r.tzero(kernel);
        let atom = q.f_lt(kernel, x, zero);
        let bot = r.f_bot(kernel);
        let body = r.f_imp(kernel, atom, bot);
        let value = r.f_all(kernel, body);
        declare_formula(kernel, q, "axLtZero", value)?
    };
    // O2: all (all (imp (rel2 0 (var 0) (S (var 1)))
    //                   (or_ (rel2 0 (var 0) (var 1)) (eqf (var 0) (var 1)))))
    //     -- OUTER binder is `y`, inner is `x`; see the module docs.
    let lt_succ_cases = {
        let x = r.tvar(kernel, 0);
        let y = r.tvar(kernel, 1);
        let sy = r.tsucc(kernel, y);
        let hyp = q.f_lt(kernel, x, sy);
        let x2 = r.tvar(kernel, 0);
        let y2 = r.tvar(kernel, 1);
        let left = q.f_lt(kernel, x2, y2);
        let x3 = r.tvar(kernel, 0);
        let y3 = r.tvar(kernel, 1);
        let right = r.f_eqf(kernel, x3, y3);
        let concl = r.f_or(kernel, left, right);
        let body = r.f_imp(kernel, hyp, concl);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, q, "axLtSuccCases", value)?
    };
    // O3: all (all (imp (rel2 0 (var 0) (var 1)) (rel2 0 (var 0) (S (var 1)))))
    let lt_succ_step = {
        let x = r.tvar(kernel, 0);
        let y = r.tvar(kernel, 1);
        let hyp = q.f_lt(kernel, x, y);
        let x2 = r.tvar(kernel, 0);
        let y2 = r.tvar(kernel, 1);
        let sy = r.tsucc(kernel, y2);
        let concl = q.f_lt(kernel, x2, sy);
        let body = r.f_imp(kernel, hyp, concl);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, q, "axLtSuccStep", value)?
    };
    // O4: all (rel2 0 (var 0) (S (var 0)))
    let lt_self_succ = {
        let x = r.tvar(kernel, 0);
        let x2 = r.tvar(kernel, 0);
        let sx = r.tsucc(kernel, x2);
        let body = q.f_lt(kernel, x, sx);
        let value = r.f_all(kernel, body);
        declare_formula(kernel, q, "axLtSelfSucc", value)?
    };
    // O5: all (all (rel2 0 (var 0) (S (var 0 + var 1))))
    let lt_add_right = {
        let x = r.tvar(kernel, 0);
        let x2 = r.tvar(kernel, 0);
        let y = r.tvar(kernel, 1);
        let sum = r.tadd(kernel, x2, y);
        let ssum = r.tsucc(kernel, sum);
        let body = q.f_lt(kernel, x, ssum);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, q, "axLtAddRight", value)?
    };
    // O6: all (all (imp (rel2 0 (var 0) (S (var 1)))
    //                   (ex (eqf (var 1 + var 0) (var 2)))))
    let lt_dest = {
        let x = r.tvar(kernel, 0);
        let y = r.tvar(kernel, 1);
        let sy = r.tsucc(kernel, y);
        let hyp = q.f_lt(kernel, x, sy);
        let x_inner = r.tvar(kernel, 1);
        let z = r.tvar(kernel, 0);
        let sum = r.tadd(kernel, x_inner, z);
        let y_inner = r.tvar(kernel, 2);
        let atom = r.f_eqf(kernel, sum, y_inner);
        let concl = r.f_ex(kernel, atom);
        let body = r.f_imp(kernel, hyp, concl);
        let inner = r.f_all(kernel, body);
        let value = r.f_all(kernel, inner);
        declare_formula(kernel, q, "axLtDest", value)?
    };

    Ok(QleAxioms {
        order: [
            lt_zero,
            lt_succ_cases,
            lt_succ_step,
            lt_self_succ,
            lt_add_right,
            lt_dest,
        ],
        robinson: [
            robinson.ax_succ_ne_zero,
            robinson.ax_succ_inj,
            robinson.ax_cases,
            robinson.ax_add_zero,
            robinson.ax_add_succ,
            robinson.ax_mul_zero,
            robinson.ax_mul_succ,
        ],
    })
}

/// `FO.Qle : FO.Context`.
fn declare_qle_context(
    kernel: &mut crate::Kernel,
    q: &Qle,
    axioms: &QleAxioms,
) -> Result<NameId, KernelError> {
    let value = q.tail(kernel, axioms, 0);
    let ty = q.r.calc.context_ty;
    kernel.add_declaration(Declaration::Definition {
        name: q.ns,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(q.ns)
}

// ============================================================================
// ℕ ⊨ Qle, and consistency.
// ============================================================================

/// `FO.Qle.natModels : Π (v : Nat -> Nat), FO.ctxSat Nat FO.natStructureQ FO.Qle v`.
///
/// Six `And.intro`s over `FO.Q.natModels v`: the tail after the six order
/// axioms IS `FO.Q`, so the seven Robinson obligations are not re-proved.
fn declare_qle_nat_models(
    kernel: &mut crate::Kernel,
    q: &Qle,
    robinson: &FoRobinsonPrelude,
    axioms: &QleAxioms,
    qle: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let r = &q.r;
    let s = kernel.const_(robinson.nat_structure_q, vec![]);

    let v_id = fv.next();
    let v = kernel.fvar(v_id);

    let qle_const = kernel.const_(qle, vec![]);
    let goal = r.ctx_sat_of(kernel, s, qle_const, v);
    let ty = pi_fv(kernel, v_id, r.val_ty, goal);

    let proofs = [
        model_lt_zero(kernel, r, fv),
        model_lt_succ_cases(kernel, r, fv),
        model_lt_succ_step(kernel, r, fv),
        model_lt_self_succ(kernel, r, fv),
        model_lt_add_right(kernel, r, fv),
        model_lt_dest(kernel, r, fv),
    ];

    let ordered = axioms.ordered();
    let mut acc = {
        let head = kernel.const_(robinson.nat_models, vec![]);
        kernel.app(head, v)
    };
    for index in (0..6).rev() {
        let head_formula = kernel.const_(ordered[index], vec![]);
        let a = r.sat_of(kernel, s, head_formula, v);
        let tail = q.tail(kernel, axioms, index + 1);
        let b = r.ctx_sat_of(kernel, s, tail, v);
        let intro = kernel.const_(r.logic.and_intro, vec![]);
        acc = apply_all(kernel, intro, &[a, b, proofs[index], acc]);
    }
    let value = lam_fv(kernel, v_id, r.val_ty, acc);

    let name = kernel.name_str(q.ns, "natModels");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `Nat.lt a b`.
fn nlt(kernel: &mut crate::Kernel, r: &Rob, a: ExprId, b: ExprId) -> ExprId {
    let head = kernel.const_(r.nat.lt, vec![]);
    apply_all(kernel, head, &[a, b])
}

/// O1 in ℕ: `fun x h => Nat.not_succ_le_zero x h`.
fn model_lt_zero(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let h_id = fv.next();
    let x = kernel.fvar(x_id);
    let h = kernel.fvar(h_id);
    let zero = kernel.const_(r.nat.zero, vec![]);
    let hyp_ty = nlt(kernel, r, x, zero);
    let head = kernel.const_(r.nat.not_succ_le_zero, vec![]);
    let body = apply_all(kernel, head, &[x, h]);
    let inner = lam_fv(kernel, h_id, hyp_ty, body);
    lam_fv(kernel, x_id, nat_ty, inner)
}

/// O2 in ℕ: `fun y x h => Nat.lt_or_eq_of_le x y (Nat.le_of_lt_succ x y h)` —
/// the binders are `y` then `x`, because the OUTER `all` is the one over `y`.
fn model_lt_succ_cases(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let h_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let h = kernel.fvar(h_id);
    let sy = r.nsucc(kernel, y);
    let hyp_ty = nlt(kernel, r, x, sy);
    let of_lt_succ = kernel.const_(r.nat.le_of_lt_succ, vec![]);
    let le = apply_all(kernel, of_lt_succ, &[x, y, h]);
    let head = kernel.const_(r.nat.lt_or_eq_of_le, vec![]);
    let body = apply_all(kernel, head, &[x, y, le]);
    let inner = lam_fv(kernel, h_id, hyp_ty, body);
    lams(kernel, &[(y_id, nat_ty), (x_id, nat_ty)], inner)
}

/// O3 in ℕ: `fun y x h => Nat.le.step (Nat.succ x) y h`.
fn model_lt_succ_step(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let h_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let h = kernel.fvar(h_id);
    let hyp_ty = nlt(kernel, r, x, y);
    let sx = r.nsucc(kernel, x);
    let head = kernel.const_(r.nat.le_step, vec![]);
    let body = apply_all(kernel, head, &[sx, y, h]);
    let inner = lam_fv(kernel, h_id, hyp_ty, body);
    lams(kernel, &[(y_id, nat_ty), (x_id, nat_ty)], inner)
}

/// O4 in ℕ: `fun x => Nat.lt_succ_self x`.
fn model_lt_self_succ(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let x = kernel.fvar(x_id);
    let head = kernel.const_(r.nat.lt_succ_self, vec![]);
    let body = kernel.app(head, x);
    lam_fv(kernel, x_id, nat_ty, body)
}

/// O5 in ℕ: `fun y x => Nat.lt_succ_of_le x (x + y) (Nat.le_add_right x y)`.
fn model_lt_add_right(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let sum = r.nadd(kernel, x, y);
    let add_right = kernel.const_(r.nat.le_add_right, vec![]);
    let le = apply_all(kernel, add_right, &[x, y]);
    let head = kernel.const_(r.nat.lt_succ_of_le, vec![]);
    let body = apply_all(kernel, head, &[x, sum, le]);
    lams(kernel, &[(y_id, nat_ty), (x_id, nat_ty)], body)
}

/// O6 in ℕ: `fun y x h => Nat.le_dest x y (Nat.le_of_lt_succ x y h)`.
fn model_lt_dest(kernel: &mut crate::Kernel, r: &Rob, fv: &mut Fv) -> ExprId {
    let nat_ty = r.nat_ty;
    let x_id = fv.next();
    let y_id = fv.next();
    let h_id = fv.next();
    let x = kernel.fvar(x_id);
    let y = kernel.fvar(y_id);
    let h = kernel.fvar(h_id);
    let sy = r.nsucc(kernel, y);
    let hyp_ty = nlt(kernel, r, x, sy);
    let of_lt_succ = kernel.const_(r.nat.le_of_lt_succ, vec![]);
    let le = apply_all(kernel, of_lt_succ, &[x, y, h]);
    let head = kernel.const_(r.nat.le_dest, vec![]);
    let body = apply_all(kernel, head, &[x, y, le]);
    let inner = lam_fv(kernel, h_id, hyp_ty, body);
    lams(kernel, &[(y_id, nat_ty), (x_id, nat_ty)], inner)
}

/// `FO.Qle.consistency : Not (FO.Provable FO.Qle FO.Formula.bot)`.
fn declare_qle_consistency(
    kernel: &mut crate::Kernel,
    q: &Qle,
    robinson: &FoRobinsonPrelude,
    qle: NameId,
    nat_models: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let r = &q.r;
    let nat_ty = r.nat_ty;
    let s = kernel.const_(robinson.nat_structure_q, vec![]);
    let qle_const = kernel.const_(qle, vec![]);
    let bot = r.f_bot(kernel);

    let d_id = fv.next();
    let junk_id = fv.next();
    let d = kernel.fvar(d_id);

    let valuation = {
        let zero = kernel.const_(r.nat.zero, vec![]);
        lam_fv(kernel, junk_id, nat_ty, zero)
    };
    let hypothesis = {
        let head = kernel.const_(nat_models, vec![]);
        kernel.app(head, valuation)
    };

    let head = kernel.const_(robinson.soundness.soundness, vec![]);
    let body = apply_all(
        kernel,
        head,
        &[nat_ty, s, qle_const, bot, d, valuation, hypothesis],
    );

    let deriv_ty = provable_app(kernel, &r.calc, qle_const, bot);
    let value = lam_fv(kernel, d_id, deriv_ty, body);
    let ty = {
        let not_const = kernel.const_(r.logic.not, vec![]);
        kernel.app(not_const, deriv_ty)
    };

    let name = kernel.name_str(q.ns, "consistency");
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
