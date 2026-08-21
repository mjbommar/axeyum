//! The proof-construction layer the characterization theorems are built with.
//!
//! [`NatOps`] already supplies every `Nat`-specific combinator, but a
//! *characterization* is by definition a statement about an **arbitrary**
//! carrier — `∀ (N : Sort u) (z : N) (s : N → N), …` — so the `Eq` combinators
//! have to be parametric in `(level, type)` rather than fixed at `Eq.{1} Nat`.
//! [`CharDev`] is `NatOps` plus exactly that: `eq_at`, `refl_at`,
//! `transport_at`, `symm_at`, `trans_at`, `congr_at`, the propositional
//! plumbing, and heterogeneous binder telescopes.

// The `Eq` combinators take a `(level, type)` pair in front of the arguments
// their `NatOps` counterparts take, which pushes several of them past the
// argument-count lint; splitting the pair into a struct would obscure the
// correspondence. `IntPrelude` is a large `Copy` handle bundle, passed by value
// here for the same reason `IntDev` does.
#![allow(
    clippy::too_many_arguments,
    clippy::large_types_passed_by_value,
    clippy::similar_names
)]

use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::IntPrelude;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::{NatOps, NatState};

/// A development that can build terms over an arbitrary carrier, on top of the
/// constructed `Int` (and hence `Nat` and logic) preludes.
pub(super) struct CharDev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
    int: IntPrelude,
}

impl<'k> CharDev<'k> {
    /// A development over `kernel` using the already-built integer prelude.
    pub(super) fn new(kernel: &'k mut Kernel, int: IntPrelude) -> Self {
        let state = NatState::new(kernel, int.nat);
        Self { kernel, state, int }
    }

    /// The interned integer/natural/logic names (a `Copy` snapshot).
    pub(super) fn int_prelude(&self) -> IntPrelude {
        self.int
    }

    /// The expression `Int`.
    pub(super) fn int_ty(&mut self) -> ExprId {
        let n = self.int.z;
        self.kernel.const_(n, vec![])
    }

    /// `Prop`, i.e. `Sort 0`.
    pub(super) fn prop_ty(&mut self) -> ExprId {
        self.kernel.sort_zero()
    }

    /// `Sort level`.
    pub(super) fn sort_at(&mut self, level: LevelId) -> ExprId {
        self.kernel.sort(level)
    }

    /// The universe level `0`.
    pub(super) fn level_zero(&mut self) -> LevelId {
        self.kernel.level_zero()
    }

    /// A level parameter reference.
    pub(super) fn level_of(&mut self, param: NameId) -> LevelId {
        self.kernel.level_param(param)
    }

    /// `fun (_ : dom) => body`, where `body` mentions no bound variable of the
    /// new binder (a constant function).
    pub(super) fn lam_const(&mut self, dom: ExprId, body: ExprId) -> ExprId {
        let anon = self.state.anon();
        self.kernel.lam(anon, dom, body, BinderInfo::Default)
    }

    // --- generic equality ----------------------------------------------------

    /// `Eq.{level} ty a b`.
    pub(super) fn eq_at(&mut self, level: LevelId, ty: ExprId, a: ExprId, b: ExprId) -> ExprId {
        let name = self.int.logic.eq;
        let eq = self.kernel.const_(name, vec![level]);
        self.apply(eq, &[ty, a, b])
    }

    /// `Eq.refl.{level} ty a : Eq ty a a`.
    pub(super) fn refl_at(&mut self, level: LevelId, ty: ExprId, a: ExprId) -> ExprId {
        let name = self.int.logic.eq_refl;
        let refl = self.kernel.const_(name, vec![level]);
        self.apply(refl, &[ty, a])
    }

    /// `Eq.rec.{0,level} ty p motive refl_case q h : motive q h` — the
    /// `Prop`-valued transport along an equation at `ty : Sort level`.
    pub(super) fn transport_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let zero = self.kernel.level_zero();
        let name = self.int.logic.eq_rec;
        let rec = self.kernel.const_(name, vec![zero, level]);
        self.apply(rec, &[ty, p, motive, refl_case, q, h])
    }

    /// `fun (x : ty) (_ : Eq ty a x) => body x`, the `Eq.rec` motive.
    pub(super) fn eq_motive_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        a: ExprId,
        body: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let x_fv = self.fresh_fvar();
        let x = self.kernel.fvar(x_fv);
        let conclusion = body(self, x);
        let hypothesis = self.eq_at(level, ty, a, x);
        let anon = self.state.anon();
        let inner = self
            .kernel
            .lam(anon, hypothesis, conclusion, BinderInfo::Default);
        self.lam_fv(x_fv, ty, inner)
    }

    /// `h : Eq ty a b ⊢ Eq ty b a`.
    pub(super) fn symm_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        a: ExprId,
        b: ExprId,
        h: ExprId,
    ) -> ExprId {
        let motive = self.eq_motive_at(level, ty, a, &|dev, x| dev.eq_at(level, ty, x, a));
        let refl_case = self.refl_at(level, ty, a);
        self.transport_at(level, ty, a, motive, refl_case, b, h)
    }

    /// `h1 : Eq ty a b`, `h2 : Eq ty b c ⊢ Eq ty a c`.
    pub(super) fn trans_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let motive = self.eq_motive_at(level, ty, b, &|dev, x| dev.eq_at(level, ty, a, x));
        self.transport_at(level, ty, b, motive, h1, c, h2)
    }

    /// `h : Eq dom a b ⊢ Eq cod (f a) (f b)`, for an arbitrary one-hole context
    /// `f` from `dom : Sort dom_level` to `cod : Sort cod_level`.
    pub(super) fn congr_at(
        &mut self,
        dom_level: LevelId,
        dom: ExprId,
        cod_level: LevelId,
        cod: ExprId,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let fa = f(self, a);
        let motive = self.eq_motive_at(dom_level, dom, a, &|dev, x| {
            let fx = f(dev, x);
            dev.eq_at(cod_level, cod, fa, fx)
        });
        let refl_case = self.refl_at(cod_level, cod, fa);
        self.transport_at(dom_level, dom, a, motive, refl_case, b, h)
    }

    // --- propositional plumbing ---------------------------------------------

    /// `True`.
    pub(super) fn true_ty(&mut self) -> ExprId {
        let n = self.int.logic.true_;
        self.kernel.const_(n, vec![])
    }

    /// `True.intro`.
    pub(super) fn true_intro(&mut self) -> ExprId {
        let n = self.int.logic.true_intro;
        self.kernel.const_(n, vec![])
    }

    /// `False`.
    pub(super) fn false_ty(&mut self) -> ExprId {
        let n = self.int.logic.false_;
        self.kernel.const_(n, vec![])
    }

    /// `Not p`.
    pub(super) fn not_of(&mut self, p: ExprId) -> ExprId {
        let n = self.int.logic.not;
        self.const_app(n, &[p])
    }

    /// `And p q`.
    pub(super) fn and_of(&mut self, p: ExprId, q: ExprId) -> ExprId {
        let n = self.int.logic.and;
        self.const_app(n, &[p, q])
    }

    /// `And.intro p q proof_p proof_q : And p q`.
    pub(super) fn and_intro(
        &mut self,
        p: ExprId,
        q: ExprId,
        proof_p: ExprId,
        proof_q: ExprId,
    ) -> ExprId {
        let n = self.int.logic.and_intro;
        self.const_app(n, &[p, q, proof_p, proof_q])
    }

    /// The left projection of `proof : And left right`.
    pub(super) fn and_left(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let and_ty = self.and_of(left, right);
        let motive = {
            let pair_fv = self.fresh_fvar();
            self.lam_fv(pair_fv, and_ty, left)
        };
        let minor = {
            let left_fv = self.fresh_fvar();
            let left_proof = self.kernel.fvar(left_fv);
            let right_fv = self.fresh_fvar();
            let with_right = self.lam_fv(right_fv, right, left_proof);
            self.lam_fv(left_fv, left, with_right)
        };
        let zero = self.kernel.level_zero();
        let name = self.int.logic.and_rec;
        let rec = self.kernel.const_(name, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }

    /// The right projection of `proof : And left right`.
    pub(super) fn and_right(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let and_ty = self.and_of(left, right);
        let motive = {
            let pair_fv = self.fresh_fvar();
            self.lam_fv(pair_fv, and_ty, right)
        };
        let minor = {
            let left_fv = self.fresh_fvar();
            let right_fv = self.fresh_fvar();
            let right_proof = self.kernel.fvar(right_fv);
            let with_right = self.lam_fv(right_fv, right, right_proof);
            self.lam_fv(left_fv, left, with_right)
        };
        let zero = self.kernel.level_zero();
        let name = self.int.logic.and_rec;
        let rec = self.kernel.const_(name, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }

    /// `Or p q`.
    pub(super) fn or_of(&mut self, p: ExprId, q: ExprId) -> ExprId {
        let n = self.int.logic.or;
        self.const_app(n, &[p, q])
    }

    /// `Or.inl p q proof : Or p q`.
    pub(super) fn or_inl(&mut self, p: ExprId, q: ExprId, proof: ExprId) -> ExprId {
        let n = self.int.logic.or_inl;
        self.const_app(n, &[p, q, proof])
    }

    /// `Or.inr p q proof : Or p q`.
    pub(super) fn or_inr(&mut self, p: ExprId, q: ExprId, proof: ExprId) -> ExprId {
        let n = self.int.logic.or_inr;
        self.const_app(n, &[p, q, proof])
    }

    /// `False.rec.{0} (fun _ => target) proof : target`, for a `Prop` target.
    pub(super) fn absurd(&mut self, target: ExprId, proof: ExprId) -> ExprId {
        let zero = self.kernel.level_zero();
        let name = self.int.logic.false_rec;
        let rec = self.kernel.const_(name, vec![zero]);
        let false_ty = self.false_ty();
        let motive = self.lam_const(false_ty, target);
        self.apply(rec, &[motive, proof])
    }

    /// `Exists.{level} ty predicate`.
    pub(super) fn exists_at(&mut self, level: LevelId, ty: ExprId, predicate: ExprId) -> ExprId {
        let n = self.int.logic.exists_;
        let e = self.kernel.const_(n, vec![level]);
        self.apply(e, &[ty, predicate])
    }

    /// `Exists.intro.{level} ty predicate witness proof`.
    pub(super) fn exists_intro_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        predicate: ExprId,
        witness: ExprId,
        proof: ExprId,
    ) -> ExprId {
        let n = self.int.logic.exists_intro;
        let e = self.kernel.const_(n, vec![level]);
        self.apply(e, &[ty, predicate, witness, proof])
    }

    /// `Exists.rec.{level} ty predicate (fun _ => target) minor witness`.
    pub(super) fn exists_elim_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        predicate: ExprId,
        target: ExprId,
        minor: ExprId,
        witness: ExprId,
    ) -> ExprId {
        let exists_ty = self.exists_at(level, ty, predicate);
        let motive = self.lam_const(exists_ty, target);
        let n = self.int.logic.exists_rec;
        let rec = self.kernel.const_(n, vec![level]);
        self.apply(rec, &[ty, predicate, motive, minor, witness])
    }

    // --- binder telescopes ---------------------------------------------------

    /// `∀ (x0 : t0) … (xn : tn), body`, closing the free variables in order.
    /// A later binder's type may mention an earlier binder.
    pub(super) fn close_pi(&mut self, binders: &[(u64, ExprId)], body: ExprId) -> ExprId {
        let mut e = body;
        for &(fv, ty) in binders.iter().rev() {
            e = self.pi_fv(fv, ty, e);
        }
        e
    }

    /// `fun (x0 : t0) … (xn : tn) => body`, the [`close_pi`](Self::close_pi)
    /// companion.
    pub(super) fn close_lam(&mut self, binders: &[(u64, ExprId)], body: ExprId) -> ExprId {
        let mut e = body;
        for &(fv, ty) in binders.iter().rev() {
            e = self.lam_fv(fv, ty, e);
        }
        e
    }

    // --- declarations --------------------------------------------------------

    /// Admit `theorem name.{uparams} : ty := value` through the trusted gate.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection — i.e. the kernel **refused** the proof.
    pub(super) fn declare_theorem_u(
        &mut self,
        name: NameId,
        uparams: Vec<NameId>,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.kernel.add_declaration(Declaration::Theorem {
            name,
            uparams,
            ty,
            value,
        })
    }

    /// Admit `def name.{uparams} : ty := value` through the trusted gate.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection.
    pub(super) fn declare_definition_u(
        &mut self,
        name: NameId,
        uparams: Vec<NameId>,
        ty: ExprId,
        value: ExprId,
        height: u16,
    ) -> Result<(), KernelError> {
        self.kernel.add_declaration(Declaration::Definition {
            name,
            uparams,
            ty,
            value,
            hint: ReducibilityHint::Regular(height),
        })
    }
}

impl NatOps for CharDev<'_> {
    fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}
