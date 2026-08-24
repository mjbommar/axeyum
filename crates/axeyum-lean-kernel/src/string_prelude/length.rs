//! `String.length : Str → Nat` — the size measure over the free monoid — plus
//! `length_nil` and `length_cons`, its defining equations made citable by
//! name.
//!
//! # Why this is a one-liner over `Str.rec`
//!
//! `Nat : Type` (`Sort 1`) with its `zero`/`succ`/`rec` is part of the
//! [`LogicPrelude`] itself (it is not `nat_prelude`'s arithmetic, which builds
//! `Nat.add` etc. *on top of* this inductive), so `length` needs nothing this
//! module does not already have in scope:
//!
//! ```text
//! length ≔ λ (s : Str), Str.rec.{1} (motive := λ _ => Nat) zero (λ h t ih => succ ih) s
//! ```
//!
//! and the kernel ι-computes `length nil ↝ zero` and
//! `length (cons h t) ↝ succ (length t)` — exactly the `Nat.add`/`Nat.mul`
//! convention in `nat_prelude`, where the defining-equation theorems below
//! close by `Eq.refl` alone because the definition already reduces.
//!
//! `length_append` (the homomorphism into `(ℕ, +)`) needs `Nat.add` and its
//! `zero_add`/`succ_add` lemmas, which live one prelude up in `nat_prelude`;
//! composing the two preludes to state and prove it is a separate, opt-in
//! step (`super::length_append::build_string_length_append`) so that ordinary
//! callers of [`crate::build_string_prelude`] — none of which need `Nat`
//! arithmetic today — do not pay for building it.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_length`] declares into, plus the
/// already-admitted `Str`/`Char`/`Nat` handles its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct LengthNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub length: NameId,
    pub length_nil: NameId,
    pub length_cons: NameId,
}

/// Declare `length` as a checked structural recursion and prove its two
/// defining equations, in dependency order.
pub(super) fn declare_length(
    kernel: &mut Kernel,
    names: &LengthNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_length()?;
    dev.prove_length_nil()?;
    dev.prove_length_cons()?;
    Ok(())
}

/// The first free-variable id this development mints — offset clear of
/// `monoid.rs`'s `FVAR_BASE` purely for readability when the two proof
/// scripts are debugged side by side; ids never leak past `abstract_fvars`,
/// so the two modules could safely share a base.
const FVAR_BASE: u64 = 2_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: LengthNames,
    anon: NameId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &LengthNames, one: LevelId) -> Self {
        let anon = k.anon();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let nat_ty = k.const_(n.logic.nat, vec![]);
        Self {
            k,
            n: *n,
            anon,
            one,
            str_ty,
            char_ty,
            nat_ty,
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

    /// `length s` — the declared constant applied, *not* inlined.
    fn length_of(&mut self, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.length, vec![]);
        self.k.app(f, s)
    }

    fn nat_zero(&mut self) -> ExprId {
        self.k.const_(self.n.logic.nat_zero, vec![])
    }

    fn nat_succ(&mut self, n: ExprId) -> ExprId {
        let s = self.k.const_(self.n.logic.nat_succ, vec![]);
        self.k.app(s, n)
    }

    /// `Eq.{1} Nat x y`.
    fn eq_nat(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let nat_ty = self.nat_ty;
        self.apply(eq, &[nat_ty, x, y])
    }

    /// `Eq.refl.{1} Nat x : Eq Nat x x`.
    fn refl_nat(&mut self, x: ExprId) -> ExprId {
        let refl = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let nat_ty = self.nat_ty;
        self.apply(refl, &[nat_ty, x])
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

    /// `length : Str → Nat`, structural recursion:
    ///
    /// ```text
    /// length ≔ λ (s : Str),
    ///            Str.rec.{1} (motive := λ _ => Nat) zero (λ h t ih => succ ih) s
    /// ```
    ///
    /// so `length nil ≡ zero` and `length (cons h t) ≡ succ (length t)` hold
    /// definitionally (β/δ/ι) — the two theorems below are that fact made
    /// citable by name.
    fn define_length(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let nat_ty = self.nat_ty;
        // motive := λ (_ : Str), Nat (a non-dependent result).
        let motive = self.k.lam(self.anon, str_ty, nat_ty, BinderInfo::Default);
        let nil_minor = self.nat_zero();
        // minor for cons := λ (h : Char) (t : Str) (ih : Nat), Nat.succ ih.
        let cons_minor = {
            let ih = self.k.bvar(0);
            let body = self.nat_succ(ih);
            let inner = self.k.lam(self.anon, nat_ty, body, BinderInfo::Default); // ih : Nat
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
        let ty = self.arrow(str_ty, nat_ty);
        self.k.add_declaration(Declaration::Definition {
            name: self.n.length,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the defining equations, by name ------------------------------------

    /// `length_nil : Eq Nat (length nil) zero`.
    ///
    /// One ι-step: the recursor's `nil` minor *is* `zero`. `Eq.refl` proves
    /// it, and the kernel accepting it is the check that `length` computes.
    fn prove_length_nil(&mut self) -> Result<(), KernelError> {
        let nil = self.nil();
        let lhs = self.length_of(nil);
        let zero = self.nat_zero();
        let ty = self.eq_nat(lhs, zero);
        let value = self.refl_nat(zero);
        let name = self.n.length_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `length_cons : ∀ (h : Char) (t : Str),
    ///     Eq Nat (length (cons h t)) (succ (length t))`.
    ///
    /// The recursion's step equation, again by ι and `Eq.refl`.
    fn prove_length_cons(&mut self) -> Result<(), KernelError> {
        let (h_fv, h) = self.fvar();
        let (t_fv, t) = self.fvar();
        let consed = self.cons(h, t);
        let lhs = self.length_of(consed);
        let len_t = self.length_of(t);
        let rhs = self.nat_succ(len_t);
        let stmt = self.eq_nat(lhs, rhs);
        let proof = self.refl_nat(rhs);
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            self.pi_fv(h_fv, char_ty, over_t)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            self.lam_fv(h_fv, char_ty, over_t)
        };
        let name = self.n.length_cons;
        self.declare_theorem(name, ty, value)
    }
}
