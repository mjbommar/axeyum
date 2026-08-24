//! `Str.map : (Char → Char) → Str → Str` — the structural-recursion
//! combinator that lifts a character transformation over a whole word — plus
//! `map_nil`/`map_cons` (its defining equations), the three fusion laws
//! `map_append`/`map_reverse`/`map_id`, the free `map_map` composition law,
//! and `length_map` (`map` preserves length).
//!
//! # The definition
//!
//! A checked structural recursion over `Str.rec`, exactly the `append`/
//! `length`/`reverse` pattern (`monoid.rs`/`length.rs`/`reverse.rs`):
//!
//! ```text
//! map ≔ λ (f : Char → Char) (s : Str),
//!   Str.rec.{1} (motive := λ _ => Str) nil (λ h t ih => cons (f h) ih) s
//! ```
//!
//! so `map f nil ≡ nil` and `map f (cons h t) ≡ cons (f h) (map f t)` hold by
//! ι-computation alone — `map_nil`/`map_cons` are that fact made citable by
//! name, both closing by `Eq.refl` alone.
//!
//! # What is proved, and how
//!
//! | law           | statement                                              | route |
//! |----------------|--------------------------------------------------------|-------|
//! | `map_nil`      | `∀ f, map f nil = nil`                                  | ι, `Eq.refl` |
//! | `map_cons`     | `∀ f h t, map f (cons h t) = cons (f h) (map f t)`      | ι, `Eq.refl` |
//! | `map_append`   | `∀ f s t, map f (append s t) = append (map f s) (map f t)` | `Str.rec` induction on `s` |
//! | `map_reverse`  | `∀ f s, map f (reverse s) = reverse (map f s)`          | `Str.rec` induction on `s`, using `map_append` |
//! | `map_id`       | `∀ s, map (fun c => c) s = s`                           | `Str.rec` induction on `s` |
//! | `map_map`      | `∀ f g s, map f (map g s) = map (fun c => f (g c)) s`   | `Str.rec` induction on `s` |
//! | `length_map`   | `∀ f s, length (map f s) = length s`                    | `Str.rec` induction on `s`, `Nat.succ` congruence |
//!
//! `map_id` and `map_map` are stated over **applied** forms (`map f s`, not
//! `map f` as a function), so neither needs `funext` — "two functions
//! agreeing pointwise are equal" is never claimed, only "mapping this
//! particular string with this particular function gives this particular
//! string". `map_map`'s witness composition `fun c => f (g c)` is a single
//! concrete lambda term, not an appeal to function extensionality.
//!
//! `map_reverse`'s step case needs `map_append` (a *propositional* rewrite,
//! not a further ι-step: `map f (append (reverse t) (cons h nil))` does not
//! reduce further on its own, since `append`'s own recursion is stuck on the
//! opaque `reverse t`) chained with a congruence on the induction hypothesis
//! via `Eq.trans`, mirroring `reverse::prove_reverse_append`'s use of
//! `append_assoc`. So `map` is declared **after** `reverse` in
//! [`super::build_string_prelude`].

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_map_and_laws`] declares into, plus the
/// already-admitted `Str`/`Char`/`append`/`reverse`/`length` handles its
/// terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct MapNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub reverse: NameId,
    pub length: NameId,
    pub map: NameId,
    pub map_nil: NameId,
    pub map_cons: NameId,
    pub map_append: NameId,
    pub map_reverse: NameId,
    pub map_id: NameId,
    pub map_map: NameId,
    pub length_map: NameId,
}

/// Declare `map` as a checked structural recursion and prove its laws, in
/// dependency order.
#[allow(clippy::too_many_lines)] // straight-line declaration sequence; see monoid.rs's same allow.
pub(super) fn declare_map_and_laws(
    kernel: &mut Kernel,
    // By reference: `MapNames` embeds `LogicPrelude` and so exceeds clippy's
    // 256-byte `large_types_passed_by_value` limit, exactly the trap
    // `MonoidNames`/`TakeDropNames`/`PredicateNames` already hit.
    names: &MapNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_map()?;
    dev.prove_map_nil()?;
    dev.prove_map_cons()?;
    dev.prove_map_append()?;
    dev.prove_map_reverse()?;
    dev.prove_map_id()?;
    dev.prove_map_map()?;
    dev.prove_length_map()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 14_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: MapNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    nat_ty: ExprId,
    char_to_char: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &MapNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let nat_ty = k.const_(n.logic.nat, vec![]);
        let char_to_char = k.pi(anon, char_ty, char_ty, BinderInfo::Default);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            str_ty,
            char_ty,
            nat_ty,
            char_to_char,
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

    /// `reverse a` — the already-declared constant applied, not inlined.
    fn reverse_of(&mut self, a: ExprId) -> ExprId {
        let f = self.k.const_(self.n.reverse, vec![]);
        self.k.app(f, a)
    }

    /// `length s` — the already-declared constant applied, not inlined.
    fn length_of(&mut self, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.length, vec![]);
        self.k.app(f, s)
    }

    /// `map f s` — the declared constant applied, not inlined.
    fn map_of(&mut self, f: ExprId, s: ExprId) -> ExprId {
        let m = self.k.const_(self.n.map, vec![]);
        self.apply(m, &[f, s])
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

    /// `Eq.trans`-style transport: from `h1 : Eq Str a b` and
    /// `h2 : Eq Str b c` build `Eq Str a c`. Mirrors `reverse::Dev::eq_trans`.
    fn eq_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let (z_fv, z) = self.fvar();
            let eq_a_z = self.eq(a, z);
            let eq_b_z = self.eq(b, z);
            let inner = self.k.lam(self.anon, eq_b_z, eq_a_z, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, b, motive, h1, c, h2])
    }

    /// Congruence in the one-hole context `Str.cons head ·`: from
    /// `proof : Eq Str x y` build `Eq Str (cons head x) (cons head y)`.
    /// Mirrors `monoid::Dev::cons_congr`.
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

    /// Congruence in the one-hole context `append · c` (`c` fixed, the head
    /// argument varying): from `proof : Eq Str x y` build
    /// `Eq Str (append x c) (append y c)`. Mirrors
    /// `reverse::Dev::congr_append_left`.
    fn congr_append_left(&mut self, x: ExprId, y: ExprId, c: ExprId, proof: ExprId) -> ExprId {
        let xc = self.append(x, c);
        let motive = {
            let (z_fv, z) = self.fvar();
            let zc = self.append(z, c);
            let conclusion = self.eq(xc, zc);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(xc);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// Congruence in the one-hole context `Nat.succ ·`: from
    /// `proof : Eq Nat x y` build `Eq Nat (succ x) (succ y)`.
    fn succ_congr(&mut self, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let succ_x = self.nat_succ(x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let succ_z = self.nat_succ(z);
            let conclusion = self.eq_nat(succ_x, succ_z);
            let hypothesis = self.eq_nat(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            let nat_ty = self.nat_ty;
            self.lam_fv(z_fv, nat_ty, inner)
        };
        let base = self.refl_nat(succ_x);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let nat_ty = self.nat_ty;
        self.apply(rec, &[nat_ty, x, motive, base, y, proof])
    }

    /// `λ (c : Char), c` — the identity character function `map_id` maps
    /// with.
    fn identity_char(&mut self) -> ExprId {
        let char_ty = self.char_ty;
        let body = self.k.bvar(0);
        self.k.lam(self.anon, char_ty, body, BinderInfo::Default)
    }

    /// `λ (c : Char), f (g c)` — the pointwise composition `map_map` maps
    /// with. `f`/`g` are outer `FVar`s, so this needs no `funext`: it is one
    /// concrete closed term, not a claim about function equality.
    fn compose_char(&mut self, f: ExprId, g: ExprId) -> ExprId {
        let char_ty = self.char_ty;
        let c = self.k.bvar(0);
        let gc = self.k.app(g, c);
        let fgc = self.k.app(f, gc);
        self.k.lam(self.anon, char_ty, fgc, BinderInfo::Default)
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

    /// `map : (Char → Char) → Str → Str`:
    ///
    /// ```text
    /// map ≔ λ (f : Char → Char) (s : Str),
    ///   Str.rec.{1} (motive := λ _ => Str) nil (λ h t ih => cons (f h) ih) s
    /// ```
    fn define_map(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let char_to_char = self.char_to_char;

        let (f_fv, f) = self.fvar();
        let (s_fv, s) = self.fvar();

        // motive := λ (_ : Str), Str.
        let motive = self.k.lam(self.anon, str_ty, str_ty, BinderInfo::Default);
        let nil_minor = self.nil();
        // minor for cons := λ (h : Char) (t : Str) (ih : Str), cons (f h) ih.
        let cons_minor = {
            let (h_fv, h) = self.fvar();
            let (t_fv, _t) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let fh = self.k.app(f, h);
            let body = self.cons(fh, ih);
            let with_ih = self.lam_fv(ih_fv, str_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_ih);
            self.lam_fv(h_fv, char_ty, with_t)
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let applied = self.apply(rec, &[motive, nil_minor, cons_minor, s]);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied);
            self.lam_fv(f_fv, char_to_char, with_s)
        };
        let ty = {
            let inner = self.arrow(str_ty, str_ty);
            self.arrow(char_to_char, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.map,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the defining equations, by name ------------------------------------

    /// `map_nil : ∀ (f : Char → Char), Eq Str (map f nil) nil`.
    fn prove_map_nil(&mut self) -> Result<(), KernelError> {
        let (f_fv, f) = self.fvar();
        let nil = self.nil();
        let lhs = self.map_of(f, nil);
        let nil2 = self.nil();
        let stmt = self.eq(lhs, nil2);
        let proof = self.refl(nil2);
        let char_to_char = self.char_to_char;
        let ty = self.pi_fv(f_fv, char_to_char, stmt);
        let value = self.lam_fv(f_fv, char_to_char, proof);
        let name = self.n.map_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `map_cons : ∀ (f : Char → Char) (h : Char) (t : Str),
    ///     Eq Str (map f (cons h t)) (cons (f h) (map f t))`.
    fn prove_map_cons(&mut self) -> Result<(), KernelError> {
        let (f_fv, f) = self.fvar();
        let (h_fv, h) = self.fvar();
        let (t_fv, t) = self.fvar();
        let consed = self.cons(h, t);
        let lhs = self.map_of(f, consed);
        let fh = self.k.app(f, h);
        let map_t = self.map_of(f, t);
        let rhs = self.cons(fh, map_t);
        let stmt = self.eq(lhs, rhs);
        let proof = self.refl(rhs);
        let char_to_char = self.char_to_char;
        let char_ty = self.char_ty;
        let str_ty = self.str_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            let over_h = self.pi_fv(h_fv, char_ty, over_t);
            self.pi_fv(f_fv, char_to_char, over_h)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            let over_h = self.lam_fv(h_fv, char_ty, over_t);
            self.lam_fv(f_fv, char_to_char, over_h)
        };
        let name = self.n.map_cons;
        self.declare_theorem(name, ty, value)
    }

    // --- the fusion laws -----------------------------------------------------

    /// `map_append : ∀ (f : Char → Char) (s t : Str),
    ///     Eq Str (map f (append s t)) (append (map f s) (map f t))`.
    ///
    /// Induction on `s`, `f`/`t` fixed. Base: both sides ι-reduce to `map f t`
    /// (`append nil t ≡ t` on the left, `map f nil ≡ nil` then
    /// `append nil (map f t) ≡ map f t` on the right). Step: both sides
    /// ι-reduce to `cons (f h) ·`-wrapped forms and `cons_congr` closes the
    /// gap via the induction hypothesis.
    fn prove_map_append(&mut self) -> Result<(), KernelError> {
        let (f_fv, f) = self.fvar();
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let lhs = {
                let a = d.append(x, t);
                d.map_of(f, a)
            };
            let rhs = {
                let mx = d.map_of(f, x);
                let mt = d.map_of(f, t);
                d.append(mx, mt)
            };
            d.eq(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let ft = d.map_of(f, t);
                d.refl(ft)
            },
            &|d, h, sp, ih| {
                let fh = d.k.app(f, h);
                let lhs_inner = {
                    let a = d.append(sp, t);
                    d.map_of(f, a)
                };
                let rhs_inner = {
                    let ms = d.map_of(f, sp);
                    let mt = d.map_of(f, t);
                    d.append(ms, mt)
                };
                d.cons_congr(fh, lhs_inner, rhs_inner, ih)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let char_to_char = self.char_to_char;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            let over_s = self.pi_fv(s_fv, str_ty, over_t);
            self.pi_fv(f_fv, char_to_char, over_s)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            let over_s = self.lam_fv(s_fv, str_ty, over_t);
            self.lam_fv(f_fv, char_to_char, over_s)
        };
        let name = self.n.map_append;
        self.declare_theorem(name, ty, value)
    }

    /// `map_reverse : ∀ (f : Char → Char) (s : Str),
    ///     Eq Str (map f (reverse s)) (reverse (map f s))`.
    ///
    /// Induction on `s`, `f` fixed. The step chains `map_append` (a
    /// propositional rewrite: `map f (append (reverse t) (cons h nil))` does
    /// not ι-reduce further on its own) with a congruence on the induction
    /// hypothesis, exactly as `reverse::prove_reverse_append` chains
    /// `append_assoc` with a congruence.
    fn prove_map_reverse(&mut self) -> Result<(), KernelError> {
        let (f_fv, f) = self.fvar();
        let (s_fv, s) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let lhs = {
                let rx = d.reverse_of(x);
                d.map_of(f, rx)
            };
            let rhs = {
                let mx = d.map_of(f, x);
                d.reverse_of(mx)
            };
            d.eq(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let nil = d.nil();
                d.refl(nil)
            },
            &|d, h, sp, ih| {
                // step1 : map_append f (reverse sp) (cons h nil)
                //   : Eq Str (map f (append (reverse sp) (cons h nil)))
                //            (append (map f (reverse sp)) (map f (cons h nil)))
                let nil = d.nil();
                let singleton = d.cons(h, nil);
                let rsp = d.reverse_of(sp);
                let step1 = {
                    let lemma = d.k.const_(d.n.map_append, vec![]);
                    let e = d.k.app(lemma, f);
                    let e = d.k.app(e, rsp);
                    d.k.app(e, singleton)
                };
                let m_rsp = d.map_of(f, rsp);
                let m_singleton = d.map_of(f, singleton);
                let m_sp = d.map_of(f, sp);
                let r_m_sp = d.reverse_of(m_sp);
                // step2 : congruence in `append · (map f (cons h nil))`, head
                // varying via `ih : Eq Str (map f (reverse sp)) (reverse (map f sp))`.
                let step2 = d.congr_append_left(m_rsp, r_m_sp, m_singleton, ih);
                let a = {
                    let a0 = d.append(rsp, singleton);
                    d.map_of(f, a0)
                };
                let b = d.append(m_rsp, m_singleton);
                let c = d.append(r_m_sp, m_singleton);
                d.eq_trans(a, b, c, step1, step2)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let char_to_char = self.char_to_char;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            self.pi_fv(f_fv, char_to_char, over_s)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            self.lam_fv(f_fv, char_to_char, over_s)
        };
        let name = self.n.map_reverse;
        self.declare_theorem(name, ty, value)
    }

    /// `map_id : ∀ (s : Str), Eq Str (map (fun c => c) s) s`.
    ///
    /// Induction on `s`. Stated over the applied form, so no `funext` is
    /// needed: this is a fact about `map id` at each concrete `s`, not a
    /// claim that `map id` and the identity function are equal.
    fn prove_map_id(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let id_fn = self.identity_char();
        let goal = move |d: &mut Self, x: ExprId| {
            let lhs = d.map_of(id_fn, x);
            d.eq(lhs, x)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let nil = d.nil();
                d.refl(nil)
            },
            &move |d, h, sp, ih| {
                let map_id_sp = d.map_of(id_fn, sp);
                d.cons_congr(h, map_id_sp, sp, ih)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.map_id;
        self.declare_theorem(name, ty, value)
    }

    /// `map_map : ∀ (f g : Char → Char) (s : Str),
    ///     Eq Str (map f (map g s)) (map (fun c => f (g c)) s)`.
    ///
    /// Induction on `s`, `f`/`g` fixed. Stated over the applied form (no
    /// `funext`): the witness composition `fun c => f (g c)` is one closed
    /// term built from the two outer `FVar`s `f`/`g`.
    fn prove_map_map(&mut self) -> Result<(), KernelError> {
        let (f_fv, f) = self.fvar();
        let (g_fv, g) = self.fvar();
        let (s_fv, s) = self.fvar();
        let comp = self.compose_char(f, g);
        let goal = move |d: &mut Self, x: ExprId| {
            let lhs = {
                let mg = d.map_of(g, x);
                d.map_of(f, mg)
            };
            let rhs = d.map_of(comp, x);
            d.eq(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let nil = d.nil();
                d.refl(nil)
            },
            &move |d, h, sp, ih| {
                let fgh = {
                    let gh = d.k.app(g, h);
                    d.k.app(f, gh)
                };
                let lhs_inner = {
                    let mg = d.map_of(g, sp);
                    d.map_of(f, mg)
                };
                let rhs_inner = d.map_of(comp, sp);
                d.cons_congr(fgh, lhs_inner, rhs_inner, ih)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let char_to_char = self.char_to_char;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            let over_g = self.pi_fv(g_fv, char_to_char, over_s);
            self.pi_fv(f_fv, char_to_char, over_g)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            let over_g = self.lam_fv(g_fv, char_to_char, over_s);
            self.lam_fv(f_fv, char_to_char, over_g)
        };
        let name = self.n.map_map;
        self.declare_theorem(name, ty, value)
    }

    /// `length_map : ∀ (f : Char → Char) (s : Str),
    ///     Eq Nat (length (map f s)) (length s)`.
    ///
    /// Induction on `s`, `f` fixed; the step is a `Nat.succ` congruence, not
    /// arithmetic — so this needs nothing from `nat_prelude` and belongs in
    /// the base prelude, like `length`/`take`/`drop` themselves.
    fn prove_length_map(&mut self) -> Result<(), KernelError> {
        let (f_fv, f) = self.fvar();
        let (s_fv, s) = self.fvar();
        let goal = move |d: &mut Self, x: ExprId| {
            let lhs = {
                let mx = d.map_of(f, x);
                d.length_of(mx)
            };
            let rhs = d.length_of(x);
            d.eq_nat(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let zero = d.k.const_(d.n.logic.nat_zero, vec![]);
                d.refl_nat(zero)
            },
            &move |d, _h, sp, ih| {
                let lhs_inner = {
                    let mx = d.map_of(f, sp);
                    d.length_of(mx)
                };
                let rhs_inner = d.length_of(sp);
                d.succ_congr(lhs_inner, rhs_inner, ih)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let char_to_char = self.char_to_char;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            self.pi_fv(f_fv, char_to_char, over_s)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            self.lam_fv(f_fv, char_to_char, over_s)
        };
        let name = self.n.length_map;
        self.declare_theorem(name, ty, value)
    }
}
