//! `append` as a **checked structural recursion**, plus the four free-monoid
//! laws, admitted through the kernel's trusted declaration gate.
//!
//! # Why this module exists
//!
//! `axeyum.string.<n>.append` used to be the last `Declaration::Axiom` in any
//! reconstruction prelude other than `real`: `logic`, `nat` and `integer` are
//! constructed with an empty trusted surface, and `string` carried exactly one
//! assumed constant of type `Str → Str → Str`. Nothing forced that. `Str` is the
//! recursive inductive `Str.nil | Str.cons (Char) (Str)` declared through
//! [`Kernel::add_recursive_datatype_family`], whose generated `Str.rec` carries an
//! induction hypothesis per recursive field — exactly the shape `Nat.add` is
//! defined by in [`crate::nat_prelude`]. So `append` is a one-liner over that
//! recursor:
//!
//! ```text
//! append a b ≔ Str.rec.{1} (motive := λ _ => Str) b (λ h t ih => Str.cons h ih) a
//! ```
//!
//! and the kernel ι-computes `append Str.nil b ↝ b` and
//! `append (Str.cons h t) b ↝ Str.cons h (append t b)`.
//!
//! # What is proved here, and what that buys
//!
//! Being *definable* is not the same as being *usable*: a `def` the kernel cannot
//! reason about propositionally would only move the assumption. So the four
//! monoid laws are declared as `Declaration::Theorem`s with checked proof terms —
//! the kernel re-type-checks each one inside `add_declaration`, so an `Ok` here is
//! the kernel accepting the proof, not this module asserting it:
//!
//! | law            | statement                                        | route |
//! |----------------|--------------------------------------------------|-------|
//! | `nil_append`   | `∀ b, append nil b = b`                          | ι, `Eq.refl` |
//! | `cons_append`  | `∀ h t b, append (cons h t) b = cons h (append t b)` | ι, `Eq.refl` |
//! | `append_nil`   | `∀ a, append a nil = a`                          | `Str.rec` induction |
//! | `append_assoc` | `∀ a b c, append (append a b) c = append a (append b c)` | `Str.rec` induction |
//!
//! Together with `Str.nil` these say `(Str, append, nil)` is a monoid — the
//! *free* monoid on `Char`, which is what a word-level (string/sequence)
//! refutation actually reasons in. The word-clash route only needed `append` to be
//! a binary function symbol, which is why the axiom survived; length and
//! cancellation reasoning needs the equations, and they are now available by name
//! rather than by assumption.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_append_and_laws`] declares into, plus the
/// already-admitted `Str`/`Char` handles its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct MonoidNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub nil_append: NameId,
    pub cons_append: NameId,
    pub append_nil: NameId,
    pub append_assoc: NameId,
}

/// The first free-variable id this development mints. Every term it declares is
/// closed (each free variable is abstracted before the declaration is pushed), so
/// this only has to be internally distinct; the offset keeps it clear of the ids
/// the type-checker's own local context mints while descending closed terms.
const FVAR_BASE: u64 = 1_000;

/// Declare `append` as a checked structural recursion and prove the four
/// free-monoid laws, in dependency order.
///
/// Every declaration goes through [`Kernel::add_declaration`], which re-checks
/// the value against the stated type; a `Err` therefore means the **kernel
/// rejected** the definition or a proof.
pub(super) fn declare_append_and_laws(
    kernel: &mut Kernel,
    names: MonoidNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_append()?;
    dev.prove_nil_append()?;
    dev.prove_cons_append()?;
    dev.prove_append_nil()?;
    dev.prove_append_assoc()?;
    Ok(())
}

struct Dev<'k> {
    k: &'k mut Kernel,
    n: MonoidNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: MonoidNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        Self {
            k,
            n,
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

    /// `append a b` — the declared constant applied, *not* inlined.
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

    /// Congruence in the one-hole context `Str.cons head ·`: from
    /// `proof : Eq Str x y` build `Eq Str (cons head x) (cons head y)` by
    /// transporting the reflexivity proof of `cons head x` along `proof`.
    fn cons_congr(&mut self, head: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(head, x);
        // motive := λ (z : Str) (_ : Eq Str x z), Eq Str (cons head x) (cons head z)
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

    /// `Str.rec.{0} motive minor_nil minor_cons target` — a `Prop`-motive
    /// induction over the free monoid.
    ///
    /// `motive` builds the goal at a `Str`, `minor_cons` receives the head, the
    /// tail, and the induction hypothesis (the goal at the tail).
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
        // λ (h : Char) (t : Str) (ih : motive t), …
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

    /// `append : Str → Str → Str`, structural recursion on the **first**
    /// argument:
    ///
    /// ```text
    /// append ≔ λ (a b : Str),
    ///            Str.rec.{1} (motive := λ _ => Str) b (λ h t ih => Str.cons h ih) a
    /// ```
    ///
    /// so `append nil b ≡ b` and `append (cons h t) b ≡ cons h (append t b)` hold
    /// definitionally (β/δ/ι) — no defining-equation axioms are needed, and the
    /// two `Eq.refl` laws below are exactly that fact made citable by name.
    fn define_append(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (a_fv, a) = self.fvar();
        let (b_fv, b) = self.fvar();
        // motive := λ (_ : Str), Str (a non-dependent result).
        let motive = self.k.lam(self.anon, str_ty, str_ty, BinderInfo::Default);
        // minor for cons := λ (h : Char) (t : Str) (ih : Str), Str.cons h ih.
        let cons_minor = {
            let h = self.k.bvar(2);
            let ih = self.k.bvar(0);
            let body = self.cons(h, ih);
            let inner = self.k.lam(self.anon, str_ty, body, BinderInfo::Default); // ih : Str
            let mid = self.k.lam(self.anon, str_ty, inner, BinderInfo::Default); // t : Str
            let char_ty = self.char_ty;
            self.k.lam(self.anon, char_ty, mid, BinderInfo::Default) // h : Char
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let body = self.apply(rec, &[motive, b, cons_minor, a]);
        let value = {
            let inner = self.lam_fv(b_fv, str_ty, body);
            self.lam_fv(a_fv, str_ty, inner)
        };
        let ty = {
            let inner = self.arrow(str_ty, str_ty);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.append,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the laws -----------------------------------------------------------

    /// `nil_append : ∀ (b : Str), Eq Str (append nil b) b`.
    ///
    /// One ι-step: the recursor's `nil` minor *is* `b`. The proof is `Eq.refl`,
    /// and the kernel accepting it is the check that `append` really computes.
    fn prove_nil_append(&mut self) -> Result<(), KernelError> {
        let (b_fv, b) = self.fvar();
        let nil = self.nil();
        let lhs = self.append(nil, b);
        let stmt = self.eq(lhs, b);
        let proof = self.refl(b);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(b_fv, str_ty, stmt);
        let value = self.lam_fv(b_fv, str_ty, proof);
        let name = self.n.nil_append;
        self.declare_theorem(name, ty, value)
    }

    /// `cons_append : ∀ (h : Char) (t b : Str),
    ///     Eq Str (append (cons h t) b) (cons h (append t b))`.
    ///
    /// The recursion's step equation, again by ι and `Eq.refl`.
    fn prove_cons_append(&mut self) -> Result<(), KernelError> {
        let (h_fv, h) = self.fvar();
        let (t_fv, t) = self.fvar();
        let (b_fv, b) = self.fvar();
        let consed = self.cons(h, t);
        let lhs = self.append(consed, b);
        let tail_append = self.append(t, b);
        let rhs = self.cons(h, tail_append);
        let stmt = self.eq(lhs, rhs);
        let proof = self.refl(rhs);
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let ty = {
            let over_b = self.pi_fv(b_fv, str_ty, stmt);
            let over_t = self.pi_fv(t_fv, str_ty, over_b);
            self.pi_fv(h_fv, char_ty, over_t)
        };
        let value = {
            let over_b = self.lam_fv(b_fv, str_ty, proof);
            let over_t = self.lam_fv(t_fv, str_ty, over_b);
            self.lam_fv(h_fv, char_ty, over_t)
        };
        let name = self.n.cons_append;
        self.declare_theorem(name, ty, value)
    }

    /// `append_nil : ∀ (a : Str), Eq Str (append a nil) a` — the **right**
    /// identity, the half that is not definitional. Induction on `a`: the base is
    /// `append nil nil ≡ nil`, and the step transports the induction hypothesis
    /// through `Str.cons h ·`.
    fn prove_append_nil(&mut self) -> Result<(), KernelError> {
        let (a_fv, a) = self.fvar();
        let goal = |d: &mut Self, s: ExprId| {
            let nil = d.nil();
            let lhs = d.append(s, nil);
            d.eq(lhs, s)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let nil = d.nil();
                d.refl(nil)
            },
            &|d, h, t, ih| {
                // ih : Eq Str (append t nil) t, goal : Eq Str (append (cons h t) nil) (cons h t),
                // and `append (cons h t) nil ≡ cons h (append t nil)` by ι.
                let nil = d.nil();
                let tail_append = d.append(t, nil);
                d.cons_congr(h, tail_append, t, ih)
            },
            a,
        );
        let stmt = goal(self, a);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(a_fv, str_ty, stmt);
        let value = self.lam_fv(a_fv, str_ty, proof);
        let name = self.n.append_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `append_assoc : ∀ (a b c : Str),
    ///     Eq Str (append (append a b) c) (append a (append b c))`.
    ///
    /// Induction on `a` with `b`, `c` fixed: the base is `append b c` on both
    /// sides by ι, and the step is the same `Str.cons h ·` congruence.
    fn prove_append_assoc(&mut self) -> Result<(), KernelError> {
        let (a_fv, a) = self.fvar();
        let (b_fv, b) = self.fvar();
        let (c_fv, c) = self.fvar();
        let goal = |d: &mut Self, s: ExprId| {
            let left = {
                let inner = d.append(s, b);
                d.append(inner, c)
            };
            let right = {
                let inner = d.append(b, c);
                d.append(s, inner)
            };
            d.eq(left, right)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let joined = d.append(b, c);
                d.refl(joined)
            },
            &|d, h, t, ih| {
                let left_tail = {
                    let inner = d.append(t, b);
                    d.append(inner, c)
                };
                let right_tail = {
                    let inner = d.append(b, c);
                    d.append(t, inner)
                };
                d.cons_congr(h, left_tail, right_tail, ih)
            },
            a,
        );
        let stmt = goal(self, a);
        let str_ty = self.str_ty;
        // Binders innermost-first, so the declared telescope reads `∀ a b c`.
        let ty = {
            let over_c = self.pi_fv(c_fv, str_ty, stmt);
            let over_b = self.pi_fv(b_fv, str_ty, over_c);
            self.pi_fv(a_fv, str_ty, over_b)
        };
        let value = {
            let over_c = self.lam_fv(c_fv, str_ty, proof);
            let over_b = self.lam_fv(b_fv, str_ty, over_c);
            self.lam_fv(a_fv, str_ty, over_b)
        };
        let name = self.n.append_assoc;
        self.declare_theorem(name, ty, value)
    }
}
