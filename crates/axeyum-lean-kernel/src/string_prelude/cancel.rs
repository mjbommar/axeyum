//! Left cancellation for `append`: `append_left_cancel : ∀ a t u,
//! append a t = append a u → t = u`.
//!
//! # The proof
//!
//! Induction on `a`, with `t`/`u` fixed (exactly the `append_assoc` shape):
//!
//! - **base** (`a = nil`): `append nil t ≡ t` and `append nil u ≡ u`
//!   (ι), so the hypothesis type is **already** the conclusion type up to
//!   `def_eq` — the identity function `λ h, h` closes it, the same trick
//!   `monoid::prove_nil_append` uses.
//! - **step** (`a = cons h a'`): the hypothesis has type (up to ι)
//!   `Eq Str (cons h (append a' t)) (cons h (append a' u))`. Applying the
//!   `tail` selector's congruence strips the shared `cons h ·` to recover
//!   `Eq Str (append a' t) (append a' u)`, which the induction hypothesis
//!   (itself a *function* `Eq Str (append a' t) (append a' u) → Eq Str t u`,
//!   since the motive here is an arrow, not a bare equation) turns into
//!   `Eq Str t u`.
//!
//! Right cancellation (`append t a = append u a → t = u`) is harder — the
//! symmetric argument needs induction on the SHARED SUFFIX, which `Str.rec`
//! does not give directly (it recurses on the head, not the tail) — and is
//! not attempted here; `reverse_append` (`reverse.rs`) would be the way in
//! (conjugate through `reverse`, cancel on the left, `reverse` back), left for
//! a follow-up slice.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_append_left_cancel`] declares into, plus the
/// already-admitted `Str`/`Char`/`append` handles its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct CancelNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub append_left_cancel: NameId,
}

/// Declare and prove `append_left_cancel`.
pub(super) fn declare_append_left_cancel(
    kernel: &mut Kernel,
    names: &CancelNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.prove_append_left_cancel()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 4_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: CancelNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &CancelNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            str_ty,
            char_ty,
            next_fvar: FVAR_BASE,
        }
    }

    // --- small builders -----------------------------------------------------

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn fvar(&mut self) -> (u64, ExprId) {
        let id = self.fresh();
        let e = self.k.fvar(id);
        (id, e)
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.k.app(e, a);
        }
        e
    }

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        self.k.lam(self.anon, ty, b, BinderInfo::Default)
    }

    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        self.k.pi(self.anon, ty, b, BinderInfo::Default)
    }

    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        self.k.pi(self.anon, dom, cod, BinderInfo::Default)
    }

    fn nil(&mut self) -> ExprId {
        self.k.const_(self.n.str_nil, vec![])
    }

    fn cons(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        let c = self.k.const_(self.n.str_cons, vec![]);
        self.apply(c, &[head, tail])
    }

    /// `append a b` — the already-declared constant applied, not inlined.
    fn append(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.append, vec![]);
        self.apply(f, &[a, b])
    }

    /// `Eq.{1} Str x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(eq, &[str_ty, x, y])
    }

    /// `Eq.refl.{1} Str x : Eq Str x x`.
    fn refl(&mut self, x: ExprId) -> ExprId {
        let refl = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(refl, &[str_ty, x])
    }

    /// The `tail : Str → Str` selector, a closed `Str.rec` application —
    /// duplicated from `StringPrelude::tail_fn` because this module runs
    /// during `StringPrelude`'s own construction, before that struct exists.
    /// `tail (cons h r) ↝ r`; `tail nil ↝ nil`.
    fn tail_fn(&mut self) -> ExprId {
        let str_ty = self.str_ty;
        let motive = self.k.lam(self.anon, str_ty, str_ty, BinderInfo::Default);
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let nil = self.nil();
        let cons_minor = {
            let body = self.k.bvar(1);
            let char_ty = self.char_ty;
            let m = self.k.lam(self.anon, str_ty, body, BinderInfo::Default); // ih
            let m = self.k.lam(self.anon, str_ty, m, BinderInfo::Default); // tail
            self.k.lam(self.anon, char_ty, m, BinderInfo::Default) // head
        };
        let e = self.apply(rec, &[motive, nil, cons_minor]);
        let t = self.k.bvar(0);
        let body = self.k.app(e, t);
        self.k.lam(self.anon, str_ty, body, BinderInfo::Default)
    }

    /// Congruence for an arbitrary unary `Str → Str` function `f`: from
    /// `proof : Eq Str x y` build `Eq Str (f x) (f y)`.
    fn congr_arg_str(&mut self, f: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let fx = self.k.app(f, x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let fz = self.k.app(f, z);
            let conclusion = self.eq(fx, fz);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(fx);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// `Str.rec.{0} motive minor_nil minor_cons target` — a `Prop`-motive
    /// induction over the free monoid. Mirrors `monoid::Dev::induct`; here
    /// `motive` may itself build an arrow type (the induction hypothesis is
    /// then a function, not a bare proof).
    fn induct(
        &mut self,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
        minor_nil: &dyn Fn(&mut Self) -> ExprId,
        minor_cons: &dyn Fn(&mut Self, ExprId, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let motive_term = {
            let (s_fv, s) = self.fvar();
            let body = motive(self, s);
            let str_ty = self.str_ty;
            self.lam_fv(s_fv, str_ty, body)
        };
        let nil_term = minor_nil(self);
        let cons_term = {
            let (h_fv, h) = self.fvar();
            let (t_fv, t) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let ih_ty = motive(self, t);
            let body = minor_cons(self, h, t, ih);
            let inner = self.lam_fv(ih_fv, ih_ty, body);
            let str_ty = self.str_ty;
            let mid = self.lam_fv(t_fv, str_ty, inner);
            let char_ty = self.char_ty;
            self.lam_fv(h_fv, char_ty, mid)
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.zero]);
        self.apply(rec, &[motive_term, nil_term, cons_term, target])
    }

    fn declare_theorem(
        &mut self,
        name: NameId,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    }

    // --- the theorem ---------------------------------------------------------

    /// `append_left_cancel : ∀ (a t u : Str),
    ///     Eq Str (append a t) (append a u) → Eq Str t u`.
    fn prove_append_left_cancel(&mut self) -> Result<(), KernelError> {
        let (a_fv, a) = self.fvar();
        let (t_fv, t) = self.fvar();
        let (u_fv, u) = self.fvar();
        let tail = self.tail_fn();

        let goal = |d: &mut Self, x: ExprId| {
            let lhs = d.append(x, t);
            let rhs = d.append(x, u);
            let hyp_ty = d.eq(lhs, rhs);
            let concl_ty = d.eq(t, u);
            d.arrow(hyp_ty, concl_ty)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                // base: append nil t ≡ t, append nil u ≡ u (ι), so the
                // hypothesis type is already the conclusion up to def_eq.
                let nil = d.nil();
                let lhs = d.append(nil, t);
                let rhs = d.append(nil, u);
                let hyp_ty = d.eq(lhs, rhs);
                let (hyp_fv, hyp) = d.fvar();
                d.lam_fv(hyp_fv, hyp_ty, hyp)
            },
            &|d, h, ap, ih| {
                // hyp : Eq Str (append (cons h ap) t) (append (cons h ap) u),
                // defeq Eq Str (cons h (append ap t)) (cons h (append ap u)).
                // Strip the shared `cons h ·` via the `tail` selector's
                // congruence, then hand the result to `ih` (itself a
                // function, since the motive is an arrow).
                let x = {
                    let consed = d.cons(h, ap);
                    d.append(consed, t)
                };
                let y = {
                    let consed = d.cons(h, ap);
                    d.append(consed, u)
                };
                let hyp_ty = d.eq(x, y);
                let (hyp_fv, hyp) = d.fvar();
                let stripped = d.congr_arg_str(tail, x, y, hyp);
                let concl = d.k.app(ih, stripped);
                d.lam_fv(hyp_fv, hyp_ty, concl)
            },
            a,
        );

        let stmt = goal(self, a);
        let str_ty = self.str_ty;
        let ty = {
            let over_u = self.pi_fv(u_fv, str_ty, stmt);
            let over_t = self.pi_fv(t_fv, str_ty, over_u);
            self.pi_fv(a_fv, str_ty, over_t)
        };
        let value = {
            let over_u = self.lam_fv(u_fv, str_ty, proof);
            let over_t = self.lam_fv(t_fv, str_ty, over_u);
            self.lam_fv(a_fv, str_ty, over_t)
        };
        let name = self.n.append_left_cancel;
        self.declare_theorem(name, ty, value)
    }
}
