//! `String.reverse : Str → Str`, plus `reverse_nil`, `reverse_append` (the
//! order-flipping anti-homomorphism law), and `reverse_reverse` (involution),
//! admitted through the trusted declaration gate exactly like `append`'s laws
//! in the `monoid` submodule.
//!
//! # The definition
//!
//! `reverse` is a checked structural recursion over `Str.rec`, expressed with
//! `append` (already a checked definition, not an axiom — see `monoid.rs`):
//!
//! ```text
//! reverse ≔ λ (s : Str),
//!   Str.rec.{1} (motive := λ _ => Str) nil (λ h t ih => append ih (cons h nil)) s
//! ```
//!
//! so `reverse nil ≡ nil` and `reverse (cons h t) ≡ append (reverse t) (cons h nil)`
//! hold definitionally (β/δ/ι).
//!
//! # What is proved
//!
//! | law              | statement                                             | route |
//! |------------------|--------------------------------------------------------|-------|
//! | `reverse_nil`    | `reverse nil = nil`                                    | ι, `Eq.refl` |
//! | `reverse_append` | `reverse (append s t) = append (reverse t) (reverse s)` | `Str.rec` induction on `s`, using `append_assoc` |
//! | `reverse_reverse`| `reverse (reverse s) = s`                              | `Str.rec` induction on `s`, using `reverse_append` |
//!
//! `reverse_append`'s order flip is the content: appending reverses the
//! *order* of concatenation, not just each piece. The induction step needs
//! `append_assoc` (re-associating three pieces) and a one-hole `append · c`
//! congruence; `reverse_reverse`'s step needs `reverse_append` itself plus the
//! `cons ·`-congruence already used by `monoid::prove_append_nil`.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_reverse_and_laws`] declares into, plus the
/// already-admitted `Str`/`Char`/`append` handles its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct ReverseNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub append_nil: NameId,
    pub append_assoc: NameId,
    pub reverse: NameId,
    pub reverse_nil: NameId,
    pub reverse_append: NameId,
    pub reverse_reverse: NameId,
}

/// Declare `reverse` as a checked structural recursion and prove its three
/// laws, in dependency order.
pub(super) fn declare_reverse_and_laws(
    kernel: &mut Kernel,
    names: &ReverseNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_reverse()?;
    dev.prove_reverse_nil()?;
    dev.prove_reverse_append()?;
    dev.prove_reverse_reverse()?;
    Ok(())
}

/// Offset clear of `monoid.rs`'s and `length.rs`'s bases purely for
/// readability; ids never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 3_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: ReverseNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &ReverseNames, one: LevelId) -> Self {
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

    /// `reverse a` — the declared constant applied, not inlined.
    fn reverse_of(&mut self, a: ExprId) -> ExprId {
        let f = self.k.const_(self.n.reverse, vec![]);
        self.k.app(f, a)
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

    /// `Eq.symm`-style transport: from `proof : Eq Str a b` build
    /// `Eq Str b a`.
    fn eq_symm(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        // motive := λ (x : Str) (_ : Eq Str a x), Eq Str x a.
        let motive = {
            let (x_fv, x) = self.fvar();
            let eq_x_a = self.eq(x, a);
            let eq_a_x = self.eq(a, x);
            let inner = self.k.lam(self.anon, eq_a_x, eq_x_a, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(x_fv, str_ty, inner)
        };
        let base = self.refl(a);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, a, motive, base, b, proof])
    }

    /// `Eq.trans`-style transport: from `h1 : Eq Str a b` and
    /// `h2 : Eq Str b c` build `Eq Str a c`.
    fn eq_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        // motive := λ (z : Str) (_ : Eq Str b z), Eq Str a z.
        let motive = {
            let (z_fv, z) = self.fvar();
            let eq_a_z = self.eq(a, z);
            let eq_b_z = self.eq(b, z);
            let inner = self.k.lam(self.anon, eq_b_z, eq_a_z, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        // base case at z = b: h1 : Eq Str a b.
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, b, motive, h1, c, h2])
    }

    /// Congruence in the one-hole context `Str.cons head ·`: from
    /// `proof : Eq Str x y` build `Eq Str (cons head x) (cons head y)`.
    fn cons_congr(&mut self, head: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(head, x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let cons_z = self.cons(head, z);
            let conclusion = self.eq(cons_x, cons_z);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(cons_x);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// Congruence in the one-hole context `append · c` (the tail `c` fixed,
    /// the head argument varying): from `proof : Eq Str x y` build
    /// `Eq Str (append x c) (append y c)`.
    fn congr_append_left(&mut self, x: ExprId, y: ExprId, c: ExprId, proof: ExprId) -> ExprId {
        let ax = self.append(x, c);
        let motive = {
            let (z_fv, z) = self.fvar();
            let az = self.append(z, c);
            let conclusion = self.eq(ax, az);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(ax);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// `Str.rec.{0} motive minor_nil minor_cons target` — a `Prop`-motive
    /// induction over the free monoid. Mirrors `monoid::Dev::induct`.
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

    // --- the definition -----------------------------------------------------

    /// `reverse : Str → Str`:
    ///
    /// ```text
    /// reverse ≔ λ (s : Str),
    ///   Str.rec.{1} (motive := λ _ => Str) nil (λ h t ih => append ih (cons h nil)) s
    /// ```
    fn define_reverse(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        // motive := λ (_ : Str), Str.
        let motive = self.k.lam(self.anon, str_ty, str_ty, BinderInfo::Default);
        let nil_minor = self.nil();
        // minor for cons := λ (h : Char) (t : Str) (ih : Str), append ih (cons h nil).
        let cons_minor = {
            let h = self.k.bvar(2);
            let ih = self.k.bvar(0);
            let nil = self.nil();
            let singleton = self.cons(h, nil);
            let body = self.append(ih, singleton);
            let inner = self.k.lam(self.anon, str_ty, body, BinderInfo::Default); // ih : Str
            let mid = self.k.lam(self.anon, str_ty, inner, BinderInfo::Default); // t : Str
            self.k.lam(self.anon, char_ty, mid, BinderInfo::Default) // h : Char
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let value = {
            let e = self.apply(rec, &[motive, nil_minor, cons_minor]);
            let s = self.k.bvar(0);
            let applied = self.k.app(e, s);
            self.k.lam(self.anon, str_ty, applied, BinderInfo::Default)
        };
        let ty = self.arrow(str_ty, str_ty);
        self.k.add_declaration(Declaration::Definition {
            name: self.n.reverse,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the laws -----------------------------------------------------------

    /// `reverse_nil : Eq Str (reverse nil) nil`. One ι-step.
    fn prove_reverse_nil(&mut self) -> Result<(), KernelError> {
        let nil = self.nil();
        let lhs = self.reverse_of(nil);
        let nil2 = self.nil();
        let ty = self.eq(lhs, nil2);
        let value = self.refl(nil2);
        let name = self.n.reverse_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `reverse_append : ∀ (s t : Str),
    ///     Eq Str (reverse (append s t)) (append (reverse t) (reverse s))`.
    ///
    /// Induction on `s` with `t` fixed. The base uses `append_nil`; the step
    /// re-associates via `append_assoc` after congruence on `ih`.
    fn prove_reverse_append(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let lhs = {
                let inner = d.append(x, t);
                d.reverse_of(inner)
            };
            let rhs = {
                let rt = d.reverse_of(t);
                let rx = d.reverse_of(x);
                d.append(rt, rx)
            };
            d.eq(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                // base: Eq Str (reverse t) (append (reverse t) nil), via
                // Eq.symm (append_nil (reverse t)).
                let rt = d.reverse_of(t);
                let nil = d.nil();
                let appealed = {
                    let lemma = d.k.const_(d.n.append_nil, vec![]);
                    d.k.app(lemma, rt)
                }; // : Eq Str (append (reverse t) nil) (reverse t)
                let append_rt_nil = d.append(rt, nil);
                d.eq_symm(append_rt_nil, rt, appealed)
            },
            &|d, h, sp, ih| {
                // ih : Eq Str (reverse (append sp t)) (append (reverse t) (reverse sp))
                // step1 : Eq Str (append (reverse (append sp t)) (cons h nil))
                //                (append (append (reverse t) (reverse sp)) (cons h nil))
                let nil = d.nil();
                let singleton = d.cons(h, nil);
                let lhs_inner = {
                    let a = d.append(sp, t);
                    d.reverse_of(a)
                };
                let rhs_inner = {
                    let rt = d.reverse_of(t);
                    let rsp = d.reverse_of(sp);
                    d.append(rt, rsp)
                };
                let step1 = d.congr_append_left(lhs_inner, rhs_inner, singleton, ih);
                // step2 : append_assoc (reverse t) (reverse sp) (cons h nil)
                //   : Eq Str (append (append (reverse t) (reverse sp)) (cons h nil))
                //            (append (reverse t) (append (reverse sp) (cons h nil)))
                let rt = d.reverse_of(t);
                let rsp = d.reverse_of(sp);
                let step2 = {
                    let lemma = d.k.const_(d.n.append_assoc, vec![]);
                    let e = d.k.app(lemma, rt);
                    let e = d.k.app(e, rsp);
                    d.k.app(e, singleton)
                };
                let a = d.append(lhs_inner, singleton);
                let b = d.append(rhs_inner, singleton);
                let c = {
                    let inner = d.append(rsp, singleton);
                    d.append(rt, inner)
                };
                d.eq_trans(a, b, c, step1, step2)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            self.pi_fv(s_fv, str_ty, over_t)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            self.lam_fv(s_fv, str_ty, over_t)
        };
        let name = self.n.reverse_append;
        self.declare_theorem(name, ty, value)
    }

    /// `reverse_reverse : ∀ (s : Str), Eq Str (reverse (reverse s)) s`.
    ///
    /// Induction on `s`. The base is `Eq.refl` (double ι). The step chains
    /// `reverse_append (reverse s') (cons h nil)` with a `cons ·`-congruence
    /// on the induction hypothesis.
    fn prove_reverse_reverse(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let lhs = {
                let rx = d.reverse_of(x);
                d.reverse_of(rx)
            };
            d.eq(lhs, x)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let nil = d.nil();
                d.refl(nil)
            },
            &|d, h, sp, ih| {
                // step1 : reverse_append (reverse sp) (cons h nil)
                //   : Eq Str (reverse (append (reverse sp) (cons h nil)))
                //            (append (reverse (cons h nil)) (reverse (reverse sp)))
                // which is defeq to
                //   Eq Str (reverse (reverse (cons h sp))) (cons h (reverse (reverse sp)))
                let nil = d.nil();
                let singleton = d.cons(h, nil);
                let rsp = d.reverse_of(sp);
                let step1 = {
                    let lemma = d.k.const_(d.n.reverse_append, vec![]);
                    let e = d.k.app(lemma, rsp);
                    d.k.app(e, singleton)
                };
                // step2 : cons_congr h (reverse (reverse sp)) sp ih
                //   : Eq Str (cons h (reverse (reverse sp))) (cons h sp)
                let rrsp = d.reverse_of(rsp);
                let step2 = d.cons_congr(h, rrsp, sp, ih);
                let a = {
                    let inner = d.append(rsp, singleton);
                    d.reverse_of(inner)
                };
                let b = d.cons(h, rrsp);
                let c = d.cons(h, sp);
                d.eq_trans(a, b, c, step1, step2)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.reverse_reverse;
        self.declare_theorem(name, ty, value)
    }
}
