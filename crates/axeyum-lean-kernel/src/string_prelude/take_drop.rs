//! `Str.take : Nat → Str → Str` and `Str.drop : Nat → Str → Str` — bounded
//! prefix/suffix extraction over the free monoid — plus `take_append_drop`,
//! the splitting law tying them to `append`. This is what a `QF_SLIA`
//! reconstruction actually needs: every `str.substr`/`str.at` argument the
//! shipped string solver reasons about is a rearrangement of this law.
//!
//! # The definitions — structural recursion on the `Nat` count
//!
//! Both must terminate when the count runs out **or** the string does, but
//! `Nat` is the argument that is always well-founded here (the alphabet-free
//! `Str.rec` motive this module needs is `Nat → Sort 1`, one level up from
//! `length`'s `Str → Nat`), so both recurse on their **first** (`Nat`)
//! argument via the bare `Nat.rec` already sitting in [`LogicPrelude`] — not
//! `nat_prelude`'s arithmetic, exactly like `length.rs`. Each `Nat`-recursion
//! step case-splits on the `Str` argument with one level of `Str.rec` (a
//! `cases`, not a further recursion — the inner induction hypothesis is
//! unused and discarded):
//!
//! ```text
//! take ≔ λ (n s : Str),
//!   Nat.rec.{1} (motive := λ _ => Str → Str)
//!     (λ s => nil)
//!     (λ n' ih => λ s => Str.rec.{1} (motive := λ _ => Str)
//!                   nil (λ h t _ => cons h (ih t)) s)
//!     n s
//!
//! drop ≔ λ (n s : Str),
//!   Nat.rec.{1} (motive := λ _ => Str → Str)
//!     (λ s => s)
//!     (λ n' ih => λ s => Str.rec.{1} (motive := λ _ => Str)
//!                   nil (λ h t _ => ih t) s)
//!     n s
//! ```
//!
//! so the four defining equations all hold by ι-computation alone (no
//! defining-equation axioms, exactly the `append`/`length`/`reverse`
//! pattern):
//!
//! - `take 0 s ≡ nil`, `drop 0 s ≡ s` — the `Nat.rec` zero minor applied to
//!   `s`.
//! - `take (n+1) nil ≡ nil`, `drop (n+1) nil ≡ nil` — the succ minor's inner
//!   `Str.rec` nil branch.
//! - `take (n+1) (cons h t) ≡ cons h (take n t)`,
//!   `drop (n+1) (cons h t) ≡ drop n t` — the succ minor's inner `Str.rec`
//!   cons branch, where `ih t` is definitionally `take n t` / `drop n t`
//!   (the same "the recursor's own `ih` unfolds back to a call of the
//!   function under construction" fact `monoid::define_append`'s `cons_minor`
//!   already relies on).
//!
//! # `take_append_drop` — the headline
//!
//! `∀ n s, append (take n s) (drop n s) = s`: induction on `n` (`Prop`-motive
//! `Nat.rec.{0}`), and within the successor step, a `Prop`-motive
//! `Str.rec.{0}` case split on `s` (again discarding its own induction
//! hypothesis — only the OUTER `Nat` induction hypothesis, applied at the
//! tail, is used):
//!
//! - **base** (`n = 0`): `take 0 s ≡ nil`, `drop 0 s ≡ s`, so the goal is
//!   `append nil s = s` — exactly `nil_append s`.
//! - **step, `s = nil`**: both `take (n'+1) nil` and `drop (n'+1) nil` ι to
//!   `nil`, so the goal is `append nil nil = nil` — `nil_append nil`.
//! - **step, `s = cons h t`**: `take (n'+1) (cons h t) ≡ cons h (take n' t)`
//!   and `drop (n'+1) (cons h t) ≡ drop n' t`, so `append (take (n'+1) (cons h
//!   t)) (drop (n'+1) (cons h t))` is defeq (one more `append`-ι) to
//!   `cons h (append (take n' t) (drop n' t))`. The (outer) induction
//!   hypothesis `ih : ∀ s, append (take n' s) (drop n' s) = s` applied at `t`
//!   gives exactly the equation `cons_congr` needs to close the goal against
//!   `cons h t`.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_take_drop_and_laws`] declares into, plus the
/// already-admitted `Str`/`Char`/`append`/`nil_append` handles its terms are
/// built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct TakeDropNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub nil_append: NameId,
    pub take: NameId,
    pub drop: NameId,
    pub take_zero: NameId,
    pub take_succ_nil: NameId,
    pub take_succ_cons: NameId,
    pub drop_zero: NameId,
    pub drop_succ_nil: NameId,
    pub drop_succ_cons: NameId,
    pub take_append_drop: NameId,
}

/// Declare `take` and `drop` as checked structural recursions, name their six
/// defining equations (each closes by `Eq.refl` alone — the signal the
/// definitions reduce rather than merely typecheck), and prove
/// `take_append_drop`, in dependency order.
pub(super) fn declare_take_drop_and_laws(
    kernel: &mut Kernel,
    // By reference: `TakeDropNames` embeds `LogicPrelude` and so exceeds
    // clippy's 256-byte `large_types_passed_by_value` limit, exactly the trap
    // `MonoidNames`/`NatPrelude` already hit.
    names: &TakeDropNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_take()?;
    dev.define_drop()?;
    dev.prove_take_zero()?;
    dev.prove_take_succ_nil()?;
    dev.prove_take_succ_cons()?;
    dev.prove_drop_zero()?;
    dev.prove_drop_succ_nil()?;
    dev.prove_drop_succ_cons()?;
    dev.prove_take_append_drop()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 6_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: TakeDropNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &TakeDropNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let nat_ty = k.const_(n.logic.nat, vec![]);
        Self {
            k,
            n: *n,
            anon,
            zero,
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

    /// `append a b` — the already-declared constant applied, not inlined.
    fn append(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.append, vec![]);
        self.apply(f, &[a, b])
    }

    /// `take n s` — the declared constant applied, not inlined.
    fn take_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.take, vec![]);
        self.apply(f, &[count, s])
    }

    /// `drop n s` — the declared constant applied, not inlined.
    fn drop_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.drop, vec![]);
        self.apply(f, &[count, s])
    }

    fn nat_zero(&mut self) -> ExprId {
        self.k.const_(self.n.logic.nat_zero, vec![])
    }

    fn nat_succ(&mut self, n: ExprId) -> ExprId {
        let s = self.k.const_(self.n.logic.nat_succ, vec![]);
        self.k.app(s, n)
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
    /// `proof : Eq Str x y` build `Eq Str (cons head x) (cons head y)`.
    /// Mirrors `monoid::Dev::cons_congr`.
    fn cons_congr(&mut self, head: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(head, x);
        let base = self.refl(cons_x);
        let str_ty = self.str_ty;
        let motive = {
            let (z_fv, z) = self.fvar();
            let cons_z = self.cons(head, z);
            let conclusion = self.eq(cons_x, cons_z);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            self.lam_fv(z_fv, str_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// `Str.rec.{0} motive minor_nil minor_cons target` — a `Prop`-motive
    /// case split / induction over the free monoid. Mirrors
    /// `monoid::Dev::induct`; callers that only need a `cases` (not a full
    /// induction) simply ignore the `ih` argument `minor_cons` receives.
    fn induct_str(
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

    /// `Nat.rec.{0} motive minor_zero minor_succ target` — a `Prop`-motive
    /// induction over `Nat`, over the bare `Nat` in [`LogicPrelude`] (not
    /// `nat_prelude`'s arithmetic).
    fn induct_nat(
        &mut self,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
        minor_zero: &dyn Fn(&mut Self) -> ExprId,
        minor_succ: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let motive_term = {
            let (n_fv, n) = self.fvar();
            let body = motive(self, n);
            let nat_ty = self.nat_ty;
            self.lam_fv(n_fv, nat_ty, body)
        };
        let zero_term = minor_zero(self);
        let succ_term = {
            let (np_fv, np) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let ih_ty = motive(self, np);
            let body = minor_succ(self, np, ih);
            let inner = self.lam_fv(ih_fv, ih_ty, body);
            let nat_ty = self.nat_ty;
            self.lam_fv(np_fv, nat_ty, inner)
        };
        let rec = self.k.const_(self.n.logic.nat_rec, vec![self.zero]);
        self.apply(rec, &[motive_term, zero_term, succ_term, target])
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

    // --- the definitions -----------------------------------------------------

    /// `take : Nat → Str → Str`, structural recursion on the `Nat` count with
    /// a one-level `Str.rec` case split in the successor branch. See the
    /// module doc for the ι-computation this buys.
    fn define_take(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let nat_ty = self.nat_ty;
        let str_to_str = self.arrow(str_ty, str_ty);

        // motive := λ (_ : Nat), Str → Str.
        let motive = self
            .k
            .lam(self.anon, nat_ty, str_to_str, BinderInfo::Default);

        // zero minor : Str → Str := λ s, nil.
        let nil0 = self.nil();
        let zero_minor = self.k.lam(self.anon, str_ty, nil0, BinderInfo::Default);

        // succ minor : ∀ (n' : Nat) (ih : Str → Str), Str → Str
        //   := λ n' ih s, Str.rec (motive := λ _ => Str) nil
        //                    (λ h t _ => cons h (ih t)) s.
        let succ_minor = {
            let (np_fv, _np) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let (s_fv, s) = self.fvar();

            let inner_motive = self.k.lam(self.anon, str_ty, str_ty, BinderInfo::Default);
            let inner_nil = self.nil();
            let inner_cons_minor = {
                let (h_fv, h) = self.fvar();
                let (t_fv, t) = self.fvar();
                let (ih2_fv, _ih2) = self.fvar(); // discarded: `take` needs the outer `ih`.
                let ih_t = self.k.app(ih, t);
                let body = self.cons(h, ih_t);
                let with_ih2 = self.lam_fv(ih2_fv, str_ty, body);
                let with_t = self.lam_fv(t_fv, str_ty, with_ih2);
                self.lam_fv(h_fv, char_ty, with_t)
            };
            let inner_rec = self.k.const_(self.n.str_rec, vec![self.one]);
            let applied = self.apply(inner_rec, &[inner_motive, inner_nil, inner_cons_minor, s]);

            let with_s = self.lam_fv(s_fv, str_ty, applied);
            let with_ih = self.lam_fv(ih_fv, str_to_str, with_s);
            self.lam_fv(np_fv, nat_ty, with_ih)
        };

        let (n_fv, n) = self.fvar();
        let (s_fv, s) = self.fvar();
        let rec = self.k.const_(self.n.logic.nat_rec, vec![self.one]);
        let inner = self.apply(rec, &[motive, zero_minor, succ_minor, n]);
        let applied_s = self.k.app(inner, s);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied_s);
            self.lam_fv(n_fv, nat_ty, with_s)
        };
        let ty = {
            let inner_ty = self.arrow(str_ty, str_ty);
            self.arrow(nat_ty, inner_ty)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.take,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `drop : Nat → Str → Str`, the mirror recursion: the successor branch
    /// recurses without re-`cons`ing the discarded head.
    fn define_drop(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let nat_ty = self.nat_ty;
        let str_to_str = self.arrow(str_ty, str_ty);

        let motive = self
            .k
            .lam(self.anon, nat_ty, str_to_str, BinderInfo::Default);

        // zero minor : Str → Str := λ s, s (identity).
        let zero_minor = {
            let s = self.k.bvar(0);
            self.k.lam(self.anon, str_ty, s, BinderInfo::Default)
        };

        // succ minor := λ n' ih s, Str.rec (motive := λ _ => Str) nil
        //                  (λ h t _ => ih t) s.
        let succ_minor = {
            let (np_fv, _np) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let (s_fv, s) = self.fvar();

            let inner_motive = self.k.lam(self.anon, str_ty, str_ty, BinderInfo::Default);
            let inner_nil = self.nil();
            let inner_cons_minor = {
                let (h_fv, _h) = self.fvar();
                let (t_fv, t) = self.fvar();
                let (ih2_fv, _ih2) = self.fvar();
                let body = self.k.app(ih, t);
                let with_ih2 = self.lam_fv(ih2_fv, str_ty, body);
                let with_t = self.lam_fv(t_fv, str_ty, with_ih2);
                self.lam_fv(h_fv, char_ty, with_t)
            };
            let inner_rec = self.k.const_(self.n.str_rec, vec![self.one]);
            let applied = self.apply(inner_rec, &[inner_motive, inner_nil, inner_cons_minor, s]);

            let with_s = self.lam_fv(s_fv, str_ty, applied);
            let with_ih = self.lam_fv(ih_fv, str_to_str, with_s);
            self.lam_fv(np_fv, nat_ty, with_ih)
        };

        let (n_fv, n) = self.fvar();
        let (s_fv, s) = self.fvar();
        let rec = self.k.const_(self.n.logic.nat_rec, vec![self.one]);
        let inner = self.apply(rec, &[motive, zero_minor, succ_minor, n]);
        let applied_s = self.k.app(inner, s);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied_s);
            self.lam_fv(n_fv, nat_ty, with_s)
        };
        let ty = {
            let inner_ty = self.arrow(str_ty, str_ty);
            self.arrow(nat_ty, inner_ty)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.drop,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the defining equations, by name --------------------------------------
    //
    // All six close by `Eq.refl` alone (no induction): the signal that `take`
    // and `drop` genuinely reduce rather than merely typecheck, exactly the
    // `nil_append`/`cons_append` and `length_nil`/`length_cons` pattern.

    /// `take_zero : ∀ (s : Str), Eq Str (take zero s) nil`.
    fn prove_take_zero(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let zero = self.nat_zero();
        let lhs = self.take_of(zero, s);
        let nil = self.nil();
        let stmt = self.eq(lhs, nil);
        let proof = self.refl(nil);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.take_zero;
        self.declare_theorem(name, ty, value)
    }

    /// `take_succ_nil : ∀ (n : Nat), Eq Str (take (succ n) nil) nil`.
    fn prove_take_succ_nil(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let succ_n = self.nat_succ(n);
        let nil = self.nil();
        let lhs = self.take_of(succ_n, nil);
        let nil2 = self.nil();
        let stmt = self.eq(lhs, nil2);
        let proof = self.refl(nil2);
        let nat_ty = self.nat_ty;
        let ty = self.pi_fv(n_fv, nat_ty, stmt);
        let value = self.lam_fv(n_fv, nat_ty, proof);
        let name = self.n.take_succ_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `take_succ_cons : ∀ (n : Nat) (h : Char) (t : Str),
    ///     Eq Str (take (succ n) (cons h t)) (cons h (take n t))`.
    fn prove_take_succ_cons(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let (h_fv, h) = self.fvar();
        let (t_fv, t) = self.fvar();
        let succ_n = self.nat_succ(n);
        let consed = self.cons(h, t);
        let lhs = self.take_of(succ_n, consed);
        let take_n_t = self.take_of(n, t);
        let rhs = self.cons(h, take_n_t);
        let stmt = self.eq(lhs, rhs);
        let proof = self.refl(rhs);
        let nat_ty = self.nat_ty;
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            let over_h = self.pi_fv(h_fv, char_ty, over_t);
            self.pi_fv(n_fv, nat_ty, over_h)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            let over_h = self.lam_fv(h_fv, char_ty, over_t);
            self.lam_fv(n_fv, nat_ty, over_h)
        };
        let name = self.n.take_succ_cons;
        self.declare_theorem(name, ty, value)
    }

    /// `drop_zero : ∀ (s : Str), Eq Str (drop zero s) s`.
    fn prove_drop_zero(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let zero = self.nat_zero();
        let lhs = self.drop_of(zero, s);
        let stmt = self.eq(lhs, s);
        let proof = self.refl(s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.drop_zero;
        self.declare_theorem(name, ty, value)
    }

    /// `drop_succ_nil : ∀ (n : Nat), Eq Str (drop (succ n) nil) nil`.
    fn prove_drop_succ_nil(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let succ_n = self.nat_succ(n);
        let nil = self.nil();
        let lhs = self.drop_of(succ_n, nil);
        let nil2 = self.nil();
        let stmt = self.eq(lhs, nil2);
        let proof = self.refl(nil2);
        let nat_ty = self.nat_ty;
        let ty = self.pi_fv(n_fv, nat_ty, stmt);
        let value = self.lam_fv(n_fv, nat_ty, proof);
        let name = self.n.drop_succ_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `drop_succ_cons : ∀ (n : Nat) (h : Char) (t : Str),
    ///     Eq Str (drop (succ n) (cons h t)) (drop n t)`.
    fn prove_drop_succ_cons(&mut self) -> Result<(), KernelError> {
        let (n_fv, n) = self.fvar();
        let (h_fv, h) = self.fvar();
        let (t_fv, t) = self.fvar();
        let succ_n = self.nat_succ(n);
        let consed = self.cons(h, t);
        let lhs = self.drop_of(succ_n, consed);
        let rhs = self.drop_of(n, t);
        let stmt = self.eq(lhs, rhs);
        let proof = self.refl(rhs);
        let nat_ty = self.nat_ty;
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            let over_h = self.pi_fv(h_fv, char_ty, over_t);
            self.pi_fv(n_fv, nat_ty, over_h)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            let over_h = self.lam_fv(h_fv, char_ty, over_t);
            self.lam_fv(n_fv, nat_ty, over_h)
        };
        let name = self.n.drop_succ_cons;
        self.declare_theorem(name, ty, value)
    }

    // --- the splitting law -----------------------------------------------------

    /// `take_append_drop : ∀ (n : Nat) (s : Str),
    ///     Eq Str (append (take n s) (drop n s)) s`.
    ///
    /// Induction on `n`; the successor step case-splits on `s`. See the
    /// module doc for the full derivation.
    fn prove_take_append_drop(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let nat_ty = self.nat_ty;

        // G(x) := ∀ (s : Str), Eq Str (append (take x s) (drop x s)) s.
        let goal = |d: &mut Self, x: ExprId| {
            let (s_fv, s) = d.fvar();
            let lhs = {
                let t = d.take_of(x, s);
                let dr = d.drop_of(x, s);
                d.append(t, dr)
            };
            let stmt = d.eq(lhs, s);
            let str_ty = d.str_ty;
            d.pi_fv(s_fv, str_ty, stmt)
        };

        let (n_fv, n) = self.fvar();
        let proof = self.induct_nat(
            &goal,
            &|d| {
                // ∀ s, Eq Str (append (take 0 s) (drop 0 s)) s
                //   ≡defeq ∀ s, Eq Str (append nil s) s  =  nil_append.
                d.k.const_(d.n.nil_append, vec![])
            },
            &|d, np, ih| {
                // λ s, <case split on s> : G(succ np).
                let (s_fv, s) = d.fvar();
                let succ_np = d.nat_succ(np);
                let inner_goal = |d: &mut Self, y: ExprId| {
                    let lhs = {
                        let t = d.take_of(succ_np, y);
                        let dr = d.drop_of(succ_np, y);
                        d.append(t, dr)
                    };
                    d.eq(lhs, y)
                };
                let case_split = d.induct_str(
                    &inner_goal,
                    &|d| {
                        // append nil nil = nil.
                        let nil = d.nil();
                        let lemma = d.k.const_(d.n.nil_append, vec![]);
                        d.k.app(lemma, nil)
                    },
                    &|d, h, t, _ih2| {
                        // ih_t : Eq Str (append (take np t) (drop np t)) t.
                        let ih_t = d.k.app(ih, t);
                        let inner = {
                            let tt = d.take_of(np, t);
                            let dt = d.drop_of(np, t);
                            d.append(tt, dt)
                        };
                        d.cons_congr(h, inner, t, ih_t)
                    },
                    s,
                );
                d.lam_fv(s_fv, str_ty, case_split)
            },
            n,
        );

        let stmt = goal(self, n);
        let ty = self.pi_fv(n_fv, nat_ty, stmt);
        let value = self.lam_fv(n_fv, nat_ty, proof);
        let name = self.n.take_append_drop;
        self.declare_theorem(name, ty, value)
    }
}
