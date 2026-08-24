//! `Str.isPrefixBool`, `Str.isSuffixBool`, `Str.containsBool : Str → Str →
//! Bool` — the short-circuit **decision procedures** a string-solver
//! reconstruction actually calls, plus both propositional spec directions
//! against the existing `Prop`-valued existentials from `predicates.rs`
//! (`isPrefix`/`isSuffix`/`contains`). A `Bool`-valued function without both
//! directions is a function, not a decision — the same standard `char_beq.rs`
//! and `str_beq.rs` already hold to.
//!
//! # Design — `isPrefixBool` is the base case, the other two ride on it
//!
//! ```text
//! isPrefixBool nil          u            = true
//! isPrefixBool (cons h1 t1) nil          = false
//! isPrefixBool (cons h1 t1) (cons h2 t2) = cond (char_beq h1 h2) (isPrefixBool t1 t2) false
//!
//! isSuffixBool s t  ≔ isPrefixBool (reverse s) (reverse t)
//!
//! containsBool nil        u = isPrefixBool u nil
//! containsBool (cons h t) u = cond (isPrefixBool u (cons h t)) true (containsBool t u)
//! ```
//!
//! `isPrefixBool` is a double `Str.rec` exactly like [`super::str_beq`]'s
//! `Str.beq` (same "outer `Str.rec` picks a row, inner `Str.rec` picks the
//! cell" shape, `bool_cond` reused via this module's own duplicate — see
//! `str_beq.rs`'s doc for why duplication, not cross-import, is this
//! development's rule). `isSuffixBool` is **not** a fresh recursion: it is
//! `isPrefixBool` composed with `reverse`, so both its spec directions are
//! four-line compositions of `is_suffix_reverse_mp`/`_mpr`
//! (`predicates.rs`) with `isPrefixBool`'s own two directions — no new
//! induction. `containsBool` is a single `Str.rec` on its **first** argument
//! (the haystack): at each `cons` node it tests whether the needle is a
//! prefix of the *current* suffix (`isPrefixBool u (cons h t)` — `cons h t`
//! is exactly the node being destructured, the same "the recursor's own
//! fields reconstruct the original node" fact `take_drop.rs`'s `ih` already
//! relies on) and otherwise recurses into the tail.
//!
//! # What is proved, and how
//!
//! | law                                      | statement                                                    | route |
//! |--------------------------------------------|-----------------------------------------------------------------|-------|
//! | `isPrefixBool_nil`                         | `∀ s, Eq Bool (isPrefixBool nil s) Bool.true`                    | definitional (`Eq.refl` alone) |
//! | `isPrefixBool_eq_true_of_isPrefix`          | `∀ p s, isPrefix p s → Eq Bool (isPrefixBool p s) Bool.true`     | induction on `p` ONLY; the `cons` step needs no case split on `s` — `Eq.rec` transports the goal along the existential's witness equation, and `char_beq_refl h` (not ι-reduction — `h` is opaque) supplies the diagonal |
//! | `isPrefix_of_isPrefixBool_eq_true`          | `∀ p s, Eq Bool (isPrefixBool p s) Bool.true → isPrefix p s`     | DOUBLE `Str.rec` (outer `p`, inner `s`), `bool_cases_remember` on the opaque `char_beq h h2` in the `cons`/`cons` cell, mirroring `str_eq_of_beq_eq_true`'s harder direction |
//! | `isSuffixBool_eq_true_of_isSuffix`          | `∀ s t, isSuffix s t → Eq Bool (isSuffixBool s t) Bool.true`     | `is_suffix_reverse_mp` then `isPrefixBool_eq_true_of_isPrefix` |
//! | `isSuffix_of_isSuffixBool_eq_true`          | `∀ s t, Eq Bool (isSuffixBool s t) Bool.true → isSuffix s t`     | `isPrefix_of_isPrefixBool_eq_true` then `is_suffix_reverse_mpr` |
//! | `contains_of_containsBool_eq_true`          | `∀ s u, Eq Bool (containsBool s u) Bool.true → contains s u`     | induction on `s`; `cons` step case-splits (`bool_cases_remember`) on the opaque `isPrefixBool u (cons h t)`, routing through `is_prefix_of_isPrefixBool_eq_true` and `contains_of_isPrefix` on the `true` branch, and unpacking the doubly-nested `contains` existential on the `false`/recursive branch |
//!
//! `containsBool`'s CONVERSE (`contains s u → containsBool s u = true`) is
//! **not attempted in this slice** — per this file's own design note, the
//! direction that must *produce* a scan position from an existential witness
//! needs an induction that tracks the outer witness `p`'s own shape (how many
//! `cons` steps separate the found occurrence from the start of `s`), which
//! is materially more work than the three directions above; landing the four
//! above and reporting this one unattempted is the standard this development
//! already sets for a partial result (`str_eq_of_beq_eq_true`'s module doc).
//!
//! Every direction here is proved without `Classical.em`, `propext`,
//! `funext`, or `Quot.sound` — the same discipline as every sibling module in
//! this slice.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_bool_predicates_and_laws`] declares into,
/// plus the already-admitted `Char`/`Str`/`char_beq`/`append`/`reverse`/
/// `isPrefix`/`isSuffix`/`contains` handles its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct BoolPredicateNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub reverse: NameId,
    pub char_beq: NameId,
    pub char_beq_refl: NameId,
    pub char_eq_of_beq_eq_true: NameId,
    pub is_prefix: NameId,
    pub is_prefix_nil: NameId,
    pub is_suffix: NameId,
    pub is_suffix_reverse_mp: NameId,
    pub is_suffix_reverse_mpr: NameId,
    pub contains: NameId,
    pub contains_of_is_prefix: NameId,

    pub is_prefix_bool: NameId,
    pub is_prefix_bool_nil: NameId,
    pub is_prefix_bool_eq_true_of_is_prefix: NameId,
    pub is_prefix_of_is_prefix_bool_eq_true: NameId,

    pub is_suffix_bool: NameId,
    pub is_suffix_bool_eq_true_of_is_suffix: NameId,
    pub is_suffix_of_is_suffix_bool_eq_true: NameId,

    pub contains_bool: NameId,
    pub contains_of_contains_bool_eq_true: NameId,
}

/// Declare `isPrefixBool`/`isSuffixBool`/`containsBool` as checked `Str.rec`
/// definitions and prove their laws, in dependency order.
#[allow(clippy::too_many_lines)] // straight-line declaration sequence; see monoid.rs's same allow.
pub(super) fn declare_bool_predicates_and_laws(
    kernel: &mut Kernel,
    names: &BoolPredicateNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_is_prefix_bool()?;
    dev.prove_is_prefix_bool_nil()?;
    dev.prove_is_prefix_bool_eq_true_of_is_prefix()?;
    dev.prove_is_prefix_of_is_prefix_bool_eq_true()?;
    dev.define_is_suffix_bool()?;
    dev.prove_is_suffix_bool_eq_true_of_is_suffix()?;
    dev.prove_is_suffix_of_is_suffix_bool_eq_true()?;
    dev.define_contains_bool()?;
    dev.prove_contains_of_contains_bool_eq_true()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 45_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: BoolPredicateNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    bool_ty: ExprId,
    prop: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &BoolPredicateNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let bool_ty = k.const_(n.logic.bool_, vec![]);
        let prop = k.sort_zero();
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            str_ty,
            char_ty,
            bool_ty,
            prop,
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

    fn bool_true_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_true, vec![])
    }

    fn bool_false_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_false, vec![])
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

    /// `char_beq a b` — the already-declared constant applied, not inlined.
    fn char_beq_of(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.char_beq, vec![]);
        self.apply(f, &[a, b])
    }

    /// `isPrefixBool p s` — the declared constant applied, not inlined.
    fn is_prefix_bool_of(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_prefix_bool, vec![]);
        self.apply(f, &[p, s])
    }

    /// `isSuffixBool s t` — the declared constant applied, not inlined.
    fn is_suffix_bool_of(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_suffix_bool, vec![]);
        self.apply(f, &[s, t])
    }

    /// `containsBool s u` — the declared constant applied, not inlined.
    fn contains_bool_of(&mut self, s: ExprId, u: ExprId) -> ExprId {
        let f = self.k.const_(self.n.contains_bool, vec![]);
        self.apply(f, &[s, u])
    }

    /// `isPrefix p s` — the already-declared constant applied, not inlined.
    fn is_prefix_of(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_prefix, vec![]);
        self.apply(f, &[p, s])
    }

    /// `isSuffix s t` — the already-declared constant applied, not inlined.
    fn is_suffix_of(&mut self, s: ExprId, t: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_suffix, vec![]);
        self.apply(f, &[s, t])
    }

    /// `contains s u` — the already-declared constant applied, not inlined.
    fn contains_of(&mut self, s: ExprId, u: ExprId) -> ExprId {
        let f = self.k.const_(self.n.contains, vec![]);
        self.apply(f, &[s, u])
    }

    /// `λ (t : Str), Eq Str (append p t) s` — the predicate `isPrefix p s`
    /// existentially quantifies. Duplicated from `predicates::Dev` (see this
    /// module's doc for why).
    fn is_prefix_pred(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let (t_fv, t) = self.fvar();
        let apt = self.append(p, t);
        let body = self.eq(apt, s);
        let str_ty = self.str_ty;
        self.lam_fv(t_fv, str_ty, body)
    }

    /// `λ (t : Str), Eq Str (append (append p u) t) s` — the INNER predicate
    /// `contains s u` existentially quantifies (over `t`, for a fixed outer
    /// witness `p`). Duplicated from `predicates::Dev` (see this module's
    /// doc for why).
    fn contains_inner_pred(&mut self, p: ExprId, u: ExprId, s: ExprId) -> ExprId {
        let (t_fv, t) = self.fvar();
        let pu = self.append(p, u);
        let put = self.append(pu, t);
        let body = self.eq(put, s);
        let str_ty = self.str_ty;
        self.lam_fv(t_fv, str_ty, body)
    }

    /// `λ (p : Str), Exists Str (contains_inner_pred p u s)` — the OUTER
    /// predicate `contains s u` existentially quantifies.
    fn contains_outer_pred(&mut self, s: ExprId, u: ExprId) -> ExprId {
        let (p_fv, p) = self.fvar();
        let inner_pred = self.contains_inner_pred(p, u, s);
        let body = self.exists_str(inner_pred);
        let str_ty = self.str_ty;
        self.lam_fv(p_fv, str_ty, body)
    }

    /// `cond c t e : Bool` — the `Bool` if-then-else via `Bool.rec`.
    /// Duplicated from `str_beq::Dev::bool_cond` (see that module's doc).
    fn bool_cond(&mut self, c: ExprId, t: ExprId, e: ExprId) -> ExprId {
        let bool_ty = self.bool_ty;
        let motive = self.k.lam(self.anon, bool_ty, bool_ty, BinderInfo::Default);
        let rec = self.k.const_(self.n.logic.bool_rec, vec![self.one]);
        let e0 = self.k.app(rec, motive);
        let e0 = self.k.app(e0, e); // minor for Bool.false
        let e0 = self.k.app(e0, t); // minor for Bool.true
        self.k.app(e0, c)
    }

    /// `Eq.{1} Bool x y`.
    fn eq_bool(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let bt = self.bool_ty;
        self.apply(eq, &[bt, x, y])
    }

    /// `Eq.refl.{1} Bool x : Eq Bool x x`.
    fn refl_bool(&mut self, x: ExprId) -> ExprId {
        let r = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let bt = self.bool_ty;
        self.apply(r, &[bt, x])
    }

    /// `Eq.{1} Str x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let st = self.str_ty;
        self.apply(eq, &[st, x, y])
    }

    /// `Eq.refl.{1} Str x : Eq Str x x`.
    fn refl(&mut self, x: ExprId) -> ExprId {
        let r = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let st = self.str_ty;
        self.apply(r, &[st, x])
    }

    /// `Eq.trans`-style transport for `Bool`: from `h1 : Eq Bool a b` and
    /// `h2 : Eq Bool b c` build `Eq Bool a c`. Duplicated from
    /// `str_beq::Dev::bool_trans`.
    fn bool_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let (z_fv, z) = self.fvar();
            let eq_a_z = self.eq_bool(a, z);
            let eq_b_z = self.eq_bool(b, z);
            let inner = self.k.lam(self.anon, eq_b_z, eq_a_z, BinderInfo::Default);
            let bool_ty = self.bool_ty;
            self.lam_fv(z_fv, bool_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let bool_ty = self.bool_ty;
        self.apply(rec, &[bool_ty, b, motive, h1, c, h2])
    }

    /// `Eq.trans`-style transport for `Str`: from `h1 : Eq Str a b` and
    /// `h2 : Eq Str b c` build `Eq Str a c`.
    fn str_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
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

    /// Transport `proof_at_a : goal_at(a)` along `heq : Eq Str a b` to
    /// `goal_at(b)`, where `goal_at` is any `Str`-indexed family of `Prop`s
    /// (here always the `Eq Bool (…) Bool.true` shape a decision-procedure
    /// direction needs). The general `Eq.rec`-transport pattern `bool_trans`/
    /// `str_trans` specialize; kept separate because the motive here varies
    /// in a caller-supplied family rather than a fixed `Eq _ _ z` shape.
    fn transport_str_indexed(
        &mut self,
        a: ExprId,
        b: ExprId,
        goal_at: &dyn Fn(&mut Self, ExprId) -> ExprId,
        proof_at_a: ExprId,
        heq: ExprId,
    ) -> ExprId {
        // `Eq.rec`'s motive is `Π (z : Str), Eq Str a z → Sort u` — the
        // equality-proof parameter is MANDATORY even when the body ignores
        // it (every other `eq_rec` use in this slice, e.g. `bool_trans`/
        // `cons_congr_tail`, takes this same 2-argument shape). A bare
        // `λ z, goal_at(z)` motive is a `Str → Prop`, one argument short,
        // and `add_declaration` rejects it with `TypeMismatch`.
        let motive = {
            let (z_fv, z) = self.fvar();
            let body = goal_at(self, z);
            let eq_a_z = self.eq(a, z);
            let inner = self.k.lam(self.anon, eq_a_z, body, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, a, motive, proof_at_a, b, heq])
    }

    /// Congruence in `Str.cons · tail` (the HEAD argument varying, `tail`
    /// fixed): from `proof : Eq Char x y` build
    /// `Eq Str (cons x tail) (cons y tail)`. Duplicated from
    /// `str_beq::Dev::cons_congr_head`.
    fn cons_congr_head(&mut self, tail: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(x, tail);
        let motive = {
            let (z_fv, z) = self.fvar();
            let cons_z = self.cons(z, tail);
            let concl = self.eq(cons_x, cons_z);
            let hyp = self.eq_char(x, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
            let char_ty = self.char_ty;
            self.lam_fv(z_fv, char_ty, inner)
        };
        let base = self.refl(cons_x);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let char_ty = self.char_ty;
        self.apply(rec, &[char_ty, x, motive, base, y, proof])
    }

    /// Congruence in `Str.cons head ·` (the TAIL argument varying, `head`
    /// fixed): from `proof : Eq Str x y` build
    /// `Eq Str (cons head x) (cons head y)`. Duplicated from
    /// `str_beq::Dev::cons_congr_tail`.
    fn cons_congr_tail(&mut self, head: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(head, x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let cons_z = self.cons(head, z);
            let concl = self.eq(cons_x, cons_z);
            let hyp = self.eq(x, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
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

    /// `Eq.{1} Char x y`.
    fn eq_char(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let ct = self.char_ty;
        self.apply(eq, &[ct, x, y])
    }

    /// Congruence in `bool_cond · t e` (the CONDITION argument varying, `t`
    /// and `e` fixed): from `proof : Eq Bool c c'` build
    /// `Eq Bool (bool_cond c t e) (bool_cond c' t e)`. Duplicated from
    /// `str_beq::Dev::bool_cond_congr_c`.
    fn bool_cond_congr_c(
        &mut self,
        c: ExprId,
        cp: ExprId,
        t: ExprId,
        e: ExprId,
        proof: ExprId,
    ) -> ExprId {
        let cond_c = self.bool_cond(c, t, e);
        let motive = {
            let (z_fv, z) = self.fvar();
            let cond_z = self.bool_cond(z, t, e);
            let concl = self.eq_bool(cond_c, cond_z);
            let hyp = self.eq_bool(c, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
            let bool_ty = self.bool_ty;
            self.lam_fv(z_fv, bool_ty, inner)
        };
        let base = self.refl_bool(cond_c);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let bool_ty = self.bool_ty;
        self.apply(rec, &[bool_ty, c, motive, base, cp, proof])
    }

    /// Eliminate an impossible `Eq Bool Bool.false Bool.true` into
    /// `target : Prop`. Duplicated from `char_beq::Dev::false_bool_elim` /
    /// `str_beq::Dev::false_bool_elim` (see those modules' docs for why).
    fn false_bool_elim(&mut self, target: ExprId, equality: ExprId) -> ExprId {
        let bool_ty = self.bool_ty;
        let false_v = self.bool_false_val();
        let true_v = self.bool_true_val();
        let prop = self.prop;
        let discriminator = {
            let motive = self.k.lam(self.anon, bool_ty, prop, BinderInfo::Default);
            let rec = self.k.const_(self.n.logic.bool_rec, vec![self.one]);
            let true_prop = self.k.const_(self.n.logic.true_, vec![]);
            let false_prop = self.k.const_(self.n.logic.false_, vec![]);
            self.apply(rec, &[motive, true_prop, false_prop])
        };
        let motive = {
            let (v_fv, v) = self.fvar();
            let eq_ty = self.eq_bool(false_v, v);
            let body = self.k.app(discriminator, v);
            let inner = self.k.lam(self.anon, eq_ty, body, BinderInfo::Default);
            self.lam_fv(v_fv, bool_ty, inner)
        };
        let true_intro = self.k.const_(self.n.logic.true_intro, vec![]);
        let eq_rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let impossible = self.apply(
            eq_rec,
            &[bool_ty, false_v, motive, true_intro, true_v, equality],
        );
        let false_rec = self.k.const_(self.n.logic.false_rec, vec![self.zero]);
        let false_ty = self.k.const_(self.n.logic.false_, vec![]);
        let false_motive = self.k.lam(self.anon, false_ty, target, BinderInfo::Default);
        self.apply(false_rec, &[false_motive, impossible])
    }

    /// Case-split on an opaque `Bool` term `v0` while KEEPING its identity
    /// available in each branch (`Eq Bool v0 Bool.false` /
    /// `Eq Bool v0 Bool.true`) — Lean's `cases h : e` idiom. Duplicated from
    /// `str_beq::Dev::bool_cases_remember` (see that module's doc for the
    /// construction and why it is needed).
    fn bool_cases_remember(
        &mut self,
        v0: ExprId,
        result_ty: &dyn Fn(&mut Self, ExprId) -> ExprId,
        minor_false: &dyn Fn(&mut Self, ExprId) -> ExprId,
        minor_true: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let bool_ty = self.bool_ty;
        let motive = {
            let (v_fv, v) = self.fvar();
            let hyp_ty = self.eq_bool(v0, v);
            let concl_ty = result_ty(self, v);
            let body = self.arrow(hyp_ty, concl_ty);
            self.lam_fv(v_fv, bool_ty, body)
        };
        let minor_false_term = {
            let false_v = self.bool_false_val();
            let (h_fv, h) = self.fvar();
            let hyp_ty = self.eq_bool(v0, false_v);
            let body = minor_false(self, h);
            self.lam_fv(h_fv, hyp_ty, body)
        };
        let minor_true_term = {
            let true_v = self.bool_true_val();
            let (h_fv, h) = self.fvar();
            let hyp_ty = self.eq_bool(v0, true_v);
            let body = minor_true(self, h);
            self.lam_fv(h_fv, hyp_ty, body)
        };
        let rec = self.k.const_(self.n.logic.bool_rec, vec![self.zero]);
        let applied = self.apply(rec, &[motive, minor_false_term, minor_true_term, v0]);
        let refl_v0 = self.refl_bool(v0);
        self.k.app(applied, refl_v0)
    }

    // --- `Exists` builders ----------------------------------------------------

    /// `Exists.{1} Str pred`.
    fn exists_str(&mut self, pred: ExprId) -> ExprId {
        let ex = self.k.const_(self.n.logic.exists_, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(ex, &[str_ty, pred])
    }

    /// `Exists.intro.{1} Str pred witness proof : Exists Str pred`.
    fn exists_intro_str(&mut self, pred: ExprId, witness: ExprId, proof: ExprId) -> ExprId {
        let intro = self.k.const_(self.n.logic.exists_intro, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(intro, &[str_ty, pred, witness, proof])
    }

    /// `Exists.rec.{1} Str pred motive minor major`, with the
    /// **non-dependent** motive `λ _ : Exists Str pred, result`. Duplicated
    /// from `predicates::Dev::exists_elim_str`.
    fn exists_elim_str(
        &mut self,
        pred: ExprId,
        result: ExprId,
        minor: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        major: ExprId,
    ) -> ExprId {
        let str_ty = self.str_ty;
        let ex_ty = self.exists_str(pred);
        let motive = self.k.lam(self.anon, ex_ty, result, BinderInfo::Default);
        let minor_term = {
            let (w_fv, w) = self.fvar();
            let pred_w = self.k.app(pred, w);
            let (h_fv, h) = self.fvar();
            let body = minor(self, w, h);
            let inner = self.lam_fv(h_fv, pred_w, body);
            self.lam_fv(w_fv, str_ty, inner)
        };
        let rec = self.k.const_(self.n.logic.exists_rec, vec![self.one]);
        self.apply(rec, &[str_ty, pred, motive, minor_term, major])
    }

    /// `Str.rec.{0} motive minor_nil minor_cons target` — a `Prop`-motive
    /// induction over the free monoid. Duplicated from `str_beq::Dev::induct`.
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

    // --- the definition: isPrefixBool ----------------------------------------

    /// `isPrefixBool : Str → Str → Bool`, a double `Str.rec`:
    ///
    /// ```text
    /// isPrefixBool nil        u            ≔ Bool.true
    /// isPrefixBool (cons h t) u            ≔ Str.rec (λ_.Bool) false
    ///                                          (λ h2 t2 _ => cond (char_beq h h2) (isPrefixBool t t2) false) u
    /// ```
    fn define_is_prefix_bool(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let bool_ty = self.bool_ty;
        let str_to_bool = self.arrow(str_ty, bool_ty);

        let outer_motive = self
            .k
            .lam(self.anon, str_ty, str_to_bool, BinderInfo::Default);

        // Outer `nil` minor: `λ (u : Str), Bool.true` — unconditionally.
        let outer_nil_minor = {
            let true_ = self.bool_true_val();
            self.k.lam(self.anon, str_ty, true_, BinderInfo::Default)
        };

        // Outer `cons` minor:
        // `λ (h : Char)(t : Str)(ih : Str → Bool)(u : Str), <compare u>`.
        let outer_cons_minor = {
            let (h_fv, h) = self.fvar();
            let (t_fv, _t) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let (u_fv, u) = self.fvar();
            let inner_motive = self.k.lam(self.anon, str_ty, bool_ty, BinderInfo::Default);
            let inner_rec = self.k.const_(self.n.str_rec, vec![self.one]);
            let false_ = self.bool_false_val();
            let cons_minor = {
                let (h2_fv, h2) = self.fvar();
                let (t2_fv, t2) = self.fvar();
                let (ih2_fv, _ih2) = self.fvar();
                let cb = self.char_beq_of(h, h2);
                let ih_t2 = self.k.app(ih, t2);
                let false2 = self.bool_false_val();
                let cnd = self.bool_cond(cb, ih_t2, false2);
                let with_ih2 = self.lam_fv(ih2_fv, bool_ty, cnd);
                let with_t2 = self.lam_fv(t2_fv, str_ty, with_ih2);
                self.lam_fv(h2_fv, char_ty, with_t2)
            };
            let e0 = self.k.app(inner_rec, inner_motive);
            let e0 = self.k.app(e0, false_);
            let e0 = self.k.app(e0, cons_minor);
            let applied = self.k.app(e0, u);
            let with_u = self.lam_fv(u_fv, str_ty, applied);
            let with_ih = self.lam_fv(ih_fv, str_to_bool, with_u);
            let with_t = self.lam_fv(t_fv, str_ty, with_ih);
            self.lam_fv(h_fv, char_ty, with_t)
        };

        let outer_rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let outer = self.k.app(outer_rec, outer_motive);
        let outer = self.k.app(outer, outer_nil_minor);
        let outer = self.k.app(outer, outer_cons_minor);

        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();
        let row = self.k.app(outer, p);
        let applied = self.k.app(row, s);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied);
            self.lam_fv(p_fv, str_ty, with_s)
        };
        let ty = {
            let inner = self.arrow(str_ty, bool_ty);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.is_prefix_bool,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `isPrefixBool_nil : ∀ (s : Str), Eq Bool (isPrefixBool nil s) Bool.true`
    /// — definitional (`isPrefixBool nil s` ι-reduces to `Bool.true`
    /// regardless of `s`), so this closes by `Eq.refl` alone.
    fn prove_is_prefix_bool_nil(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let nil = self.nil();
        let ipb = self.is_prefix_bool_of(nil, s);
        let t = self.bool_true_val();
        let stmt = self.eq_bool(ipb, t);
        let proof = self.refl_bool(t);
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.is_prefix_bool_nil;
        self.declare_theorem(name, ty, value)
    }

    // --- isPrefixBool_eq_true_of_isPrefix (the "converse" — eliminates the existential) ---

    /// `Π s, isPrefix x s → Eq Bool (isPrefixBool x s) Bool.true`.
    fn row_type_eq_true(&mut self, x: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let hyp_ty = self.is_prefix_of(x, s);
        let ipb = self.is_prefix_bool_of(x, s);
        let t = self.bool_true_val();
        let concl = self.eq_bool(ipb, t);
        let imp = self.arrow(hyp_ty, concl);
        self.pi_fv(s_fv, str_ty, imp)
    }

    /// Outer `nil` case: `isPrefixBool nil s = true` holds unconditionally
    /// (definitionally), so the hypothesis is discarded.
    fn nil_row_proof_eq_true(&mut self) -> ExprId {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let (hp_fv, _hp) = self.fvar();
        let nil = self.nil();
        let hyp_ty = self.is_prefix_of(nil, s);
        let t = self.bool_true_val();
        let proof = self.refl_bool(t);
        let with_hp = self.lam_fv(hp_fv, hyp_ty, proof);
        self.lam_fv(s_fv, str_ty, with_hp)
    }

    /// Outer `cons(h, t_, ih_a)` case. No case split on `s` is needed: the
    /// existential hypothesis is eliminated to a witness `w` with
    /// `append (cons h t_) w = s`, and the goal is transported (via
    /// [`Self::transport_str_indexed`]) from `s` back to the DEFEQ-reachable
    /// point `append (cons h t_) w`, where `isPrefixBool` ι-reduces on the
    /// concrete `cons` shape.
    fn cons_row_proof_eq_true(&mut self, h: ExprId, t_: ExprId, ih_a: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let consed = self.cons(h, t_);
        let goal_at = move |d: &mut Self, z: ExprId| {
            let ipb = d.is_prefix_bool_of(consed, z);
            let t = d.bool_true_val();
            d.eq_bool(ipb, t)
        };
        let stmt_ty = goal_at(self, s);
        let hyp_ty = self.is_prefix_of(consed, s);
        let pred = self.is_prefix_pred(consed, s);

        let (hyp_fv, hyp) = self.fvar();
        let body = self.exists_elim_str(
            pred,
            stmt_ty,
            &move |d, w, hw| {
                let awp = d.append(consed, w);
                let base_proof = {
                    let cb_hh = d.char_beq_of(h, h);
                    let true_ = d.bool_true_val();
                    let false_ = d.bool_false_val();
                    let tw = d.append(t_, w);
                    let ipb_inner = d.is_prefix_bool_of(t_, tw);
                    let cnd = d.bool_cond(cb_hh, ipb_inner, false_);
                    let refl_h = {
                        let l = d.k.const_(d.n.char_beq_refl, vec![]);
                        d.k.app(l, h)
                    };
                    let step1 = d.bool_cond_congr_c(cb_hh, true_, ipb_inner, false_, refl_h);
                    let pref_tw = {
                        let pred2 = d.is_prefix_pred(t_, tw);
                        let refl_tw = d.refl(tw);
                        d.exists_intro_str(pred2, w, refl_tw)
                    };
                    let ih_res = {
                        let e = d.k.app(ih_a, tw);
                        d.k.app(e, pref_tw)
                    };
                    d.bool_trans(cnd, ipb_inner, true_, step1, ih_res)
                };
                d.transport_str_indexed(awp, s, &goal_at, base_proof, hw)
            },
            hyp,
        );
        let with_hyp = self.lam_fv(hyp_fv, hyp_ty, body);
        self.lam_fv(s_fv, str_ty, with_hyp)
    }

    /// `isPrefixBool_eq_true_of_isPrefix : ∀ (p s : Str),
    ///     isPrefix p s → Eq Bool (isPrefixBool p s) Bool.true`.
    fn prove_is_prefix_bool_eq_true_of_is_prefix(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (p_fv, p) = self.fvar();
        let stmt = self.row_type_eq_true(p);
        let proof = self.induct(
            &|d, x| d.row_type_eq_true(x),
            &|d| d.nil_row_proof_eq_true(),
            &|d, h, t_, ih_a| d.cons_row_proof_eq_true(h, t_, ih_a),
            p,
        );
        let ty = self.pi_fv(p_fv, str_ty, stmt);
        let value = self.lam_fv(p_fv, str_ty, proof);
        let name = self.n.is_prefix_bool_eq_true_of_is_prefix;
        self.declare_theorem(name, ty, value)
    }

    // --- isPrefix_of_isPrefixBool_eq_true (constructs the witness) ---------

    /// `Π s, Eq Bool (isPrefixBool x s) Bool.true → isPrefix x s`.
    fn row_type_construct(&mut self, x: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let ipb = self.is_prefix_bool_of(x, s);
        let t = self.bool_true_val();
        let premise = self.eq_bool(ipb, t);
        let concl = self.is_prefix_of(x, s);
        let imp = self.arrow(premise, concl);
        self.pi_fv(s_fv, str_ty, imp)
    }

    /// Outer `nil` case: `isPrefix nil s` always holds, via `isPrefix_nil`;
    /// the premise is discarded.
    fn nil_row_proof_construct(&mut self) -> ExprId {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let (hp_fv, _hp) = self.fvar();
        let nil = self.nil();
        let ipb = self.is_prefix_bool_of(nil, s);
        let t = self.bool_true_val();
        let premise = self.eq_bool(ipb, t);
        let proof = {
            let lemma = self.k.const_(self.n.is_prefix_nil, vec![]);
            self.k.app(lemma, s)
        };
        let with_hp = self.lam_fv(hp_fv, premise, proof);
        self.lam_fv(s_fv, str_ty, with_hp)
    }

    /// The `cons h t_` / `cons h2 t2` cell: `bool_cases_remember` on
    /// `char_beq h h2`.
    fn cons_cons_case_construct(
        &mut self,
        h: ExprId,
        t_: ExprId,
        ih_a: ExprId,
        h2: ExprId,
        t2: ExprId,
    ) -> ExprId {
        let v0 = self.char_beq_of(h, h2);
        self.bool_cases_remember(
            v0,
            &move |d, v| {
                let false_ = d.bool_false_val();
                let ipb_t = d.is_prefix_bool_of(t_, t2);
                let cnd = d.bool_cond(v, ipb_t, false_);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let cl = d.cons(h, t_);
                let cr = d.cons(h2, t2);
                let tgt = d.is_prefix_of(cl, cr);
                d.arrow(prem2, tgt)
            },
            &move |d, _h_eq_false| {
                let (hp2_fv, hp2) = d.fvar();
                let false_ = d.bool_false_val();
                let ipb_t = d.is_prefix_bool_of(t_, t2);
                let cnd = d.bool_cond(false_, ipb_t, false_);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let cl = d.cons(h, t_);
                let cr = d.cons(h2, t2);
                let tgt = d.is_prefix_of(cl, cr);
                let body2 = d.false_bool_elim(tgt, hp2);
                d.lam_fv(hp2_fv, prem2, body2)
            },
            &move |d, h_eq_true| {
                let (hp2_fv, hp2) = d.fvar();
                let true_ = d.bool_true_val();
                let false_ = d.bool_false_val();
                let ipb_t = d.is_prefix_bool_of(t_, t2);
                let cnd = d.bool_cond(true_, ipb_t, false_);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let cl = d.cons(h, t_);
                let cr = d.cons(h2, t2);
                let tgt = d.is_prefix_of(cl, cr);

                let char_eq = {
                    let lemma = d.k.const_(d.n.char_eq_of_beq_eq_true, vec![]);
                    let e = d.k.app(lemma, h);
                    let e = d.k.app(e, h2);
                    d.k.app(e, h_eq_true)
                };
                let pred_t_t2 = d.is_prefix_pred(t_, t2);
                let body2 = {
                    // `hp2` (the premise, already reduced to `isPrefixBool t_ t2 = true`
                    // in this branch) IS the argument `ih_a` needs.
                    let pref_t_t2 = {
                        let e = d.k.app(ih_a, t2);
                        d.k.app(e, hp2)
                    };
                    d.exists_elim_str(
                        pred_t_t2,
                        tgt,
                        &move |d, w, hw| {
                            let tw = d.append(t_, w);
                            let step1 = d.cons_congr_tail(h, tw, t2, hw);
                            let char_step = d.cons_congr_head(t2, h, h2, char_eq);
                            let consed_ht = d.cons(h, t_);
                            let a = d.append(consed_ht, w);
                            let mid = d.cons(h, t2);
                            let cr2 = d.cons(h2, t2);
                            let chain = d.str_trans(a, mid, cr2, step1, char_step);
                            let pred_final = d.is_prefix_pred(consed_ht, cr2);
                            d.exists_intro_str(pred_final, w, chain)
                        },
                        pref_t_t2,
                    )
                };
                d.lam_fv(hp2_fv, prem2, body2)
            },
        )
    }

    /// Outer `cons(h, t_, ih_a)` case: inner `Str.rec` case split on `s`.
    fn cons_row_proof_construct(&mut self, h: ExprId, t_: ExprId, ih_a: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let inner = self.induct(
            &move |d, x| {
                let consed = d.cons(h, t_);
                let ipb = d.is_prefix_bool_of(consed, x);
                let t = d.bool_true_val();
                let premise = d.eq_bool(ipb, t);
                let concl = d.is_prefix_of(consed, x);
                d.arrow(premise, concl)
            },
            &move |d| {
                let (hp_fv, hp) = d.fvar();
                let consed = d.cons(h, t_);
                let nil = d.nil();
                let ipb = d.is_prefix_bool_of(consed, nil);
                let t = d.bool_true_val();
                let premise = d.eq_bool(ipb, t);
                let target = d.is_prefix_of(consed, nil);
                let body = d.false_bool_elim(target, hp);
                d.lam_fv(hp_fv, premise, body)
            },
            &move |d, h2, t2, _ih2| d.cons_cons_case_construct(h, t_, ih_a, h2, t2),
            s,
        );
        self.lam_fv(s_fv, str_ty, inner)
    }

    /// `isPrefix_of_isPrefixBool_eq_true : ∀ (p s : Str),
    ///     Eq Bool (isPrefixBool p s) Bool.true → isPrefix p s`.
    fn prove_is_prefix_of_is_prefix_bool_eq_true(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (p_fv, p) = self.fvar();
        let stmt = self.row_type_construct(p);
        let proof = self.induct(
            &|d, x| d.row_type_construct(x),
            &|d| d.nil_row_proof_construct(),
            &|d, h, t_, ih_a| d.cons_row_proof_construct(h, t_, ih_a),
            p,
        );
        let ty = self.pi_fv(p_fv, str_ty, stmt);
        let value = self.lam_fv(p_fv, str_ty, proof);
        let name = self.n.is_prefix_of_is_prefix_bool_eq_true;
        self.declare_theorem(name, ty, value)
    }

    // --- isSuffixBool: a composition, not a fresh recursion -----------------

    /// `isSuffixBool : Str → Str → Bool := λ s t, isPrefixBool (reverse s) (reverse t)`.
    fn define_is_suffix_bool(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let bool_ty = self.bool_ty;
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let rs = self.reverse_of(s);
        let rt = self.reverse_of(t);
        let body = self.is_prefix_bool_of(rs, rt);
        let value = {
            let with_t = self.lam_fv(t_fv, str_ty, body);
            self.lam_fv(s_fv, str_ty, with_t)
        };
        let ty = {
            let inner = self.arrow(str_ty, bool_ty);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.is_suffix_bool,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `isSuffixBool_eq_true_of_isSuffix : ∀ s t,
    ///     isSuffix s t → Eq Bool (isSuffixBool s t) Bool.true`.
    fn prove_is_suffix_bool_eq_true_of_is_suffix(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let hyp_ty = self.is_suffix_of(s, t);
        let isb = self.is_suffix_bool_of(s, t);
        let bt = self.bool_true_val();
        let target = self.eq_bool(isb, bt);

        let (h_fv, h) = self.fvar();
        let rs = self.reverse_of(s);
        let rt = self.reverse_of(t);
        let ip_rs_rt = {
            let lemma = self.k.const_(self.n.is_suffix_reverse_mp, vec![]);
            let e = self.k.app(lemma, s);
            let e = self.k.app(e, t);
            self.k.app(e, h)
        };
        let body = {
            let lemma = self
                .k
                .const_(self.n.is_prefix_bool_eq_true_of_is_prefix, vec![]);
            let e = self.k.app(lemma, rs);
            let e = self.k.app(e, rt);
            self.k.app(e, ip_rs_rt)
        };
        let value = {
            let with_h = self.lam_fv(h_fv, hyp_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_h);
            self.lam_fv(s_fv, str_ty, with_t)
        };
        let ty = {
            let inner = self.arrow(hyp_ty, target);
            let with_t = self.pi_fv(t_fv, str_ty, inner);
            self.pi_fv(s_fv, str_ty, with_t)
        };
        let name = self.n.is_suffix_bool_eq_true_of_is_suffix;
        self.declare_theorem(name, ty, value)
    }

    /// `isSuffix_of_isSuffixBool_eq_true : ∀ s t,
    ///     Eq Bool (isSuffixBool s t) Bool.true → isSuffix s t`.
    fn prove_is_suffix_of_is_suffix_bool_eq_true(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let isb = self.is_suffix_bool_of(s, t);
        let bt = self.bool_true_val();
        let hyp_ty = self.eq_bool(isb, bt);
        let target = self.is_suffix_of(s, t);

        let (h_fv, h) = self.fvar();
        let rs = self.reverse_of(s);
        let rt = self.reverse_of(t);
        let ip_rs_rt = {
            let lemma = self
                .k
                .const_(self.n.is_prefix_of_is_prefix_bool_eq_true, vec![]);
            let e = self.k.app(lemma, rs);
            let e = self.k.app(e, rt);
            self.k.app(e, h)
        };
        let body = {
            let lemma = self.k.const_(self.n.is_suffix_reverse_mpr, vec![]);
            let e = self.k.app(lemma, s);
            let e = self.k.app(e, t);
            self.k.app(e, ip_rs_rt)
        };
        let value = {
            let with_h = self.lam_fv(h_fv, hyp_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_h);
            self.lam_fv(s_fv, str_ty, with_t)
        };
        let ty = {
            let inner = self.arrow(hyp_ty, target);
            let with_t = self.pi_fv(t_fv, str_ty, inner);
            self.pi_fv(s_fv, str_ty, with_t)
        };
        let name = self.n.is_suffix_of_is_suffix_bool_eq_true;
        self.declare_theorem(name, ty, value)
    }

    // --- containsBool ---------------------------------------------------------

    /// `containsBool : Str → Str → Bool`, a single `Str.rec` on the
    /// haystack:
    ///
    /// ```text
    /// containsBool nil        u ≔ isPrefixBool u nil
    /// containsBool (cons h t) u ≔ cond (isPrefixBool u (cons h t)) Bool.true (containsBool t u)
    /// ```
    fn define_contains_bool(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let bool_ty = self.bool_ty;

        let (s_fv, s) = self.fvar();
        let (u_fv, u) = self.fvar();

        let motive = self.k.lam(self.anon, str_ty, bool_ty, BinderInfo::Default);
        let nil_minor = {
            let nil = self.nil();
            self.is_prefix_bool_of(u, nil)
        };
        let cons_minor = {
            let (h_fv, h) = self.fvar();
            let (t_fv, t_) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let consed = self.cons(h, t_);
            let ipb = self.is_prefix_bool_of(u, consed);
            let true_ = self.bool_true_val();
            let body = self.bool_cond(ipb, true_, ih);
            let with_ih = self.lam_fv(ih_fv, bool_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_ih);
            self.lam_fv(h_fv, char_ty, with_t)
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let applied = self.apply(rec, &[motive, nil_minor, cons_minor, s]);
        let with_u = self.lam_fv(u_fv, str_ty, applied);
        let value = self.lam_fv(s_fv, str_ty, with_u);
        let ty = {
            let inner = self.arrow(str_ty, bool_ty);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.contains_bool,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `Π u, Eq Bool (containsBool x u) Bool.true → contains x u`.
    fn row_type_contains(&mut self, x: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (u_fv, u) = self.fvar();
        let cb = self.contains_bool_of(x, u);
        let t = self.bool_true_val();
        let premise = self.eq_bool(cb, t);
        let concl = self.contains_of(x, u);
        let imp = self.arrow(premise, concl);
        self.pi_fv(u_fv, str_ty, imp)
    }

    /// `s = nil` case: `containsBool nil u` ι-reduces directly to
    /// `isPrefixBool u nil` (no case split needed), so the premise already
    /// has exactly the shape `isPrefix_of_isPrefixBool_eq_true` needs.
    fn nil_row_proof_contains(&mut self) -> ExprId {
        let str_ty = self.str_ty;
        let (u_fv, u) = self.fvar();
        let (hp_fv, hp) = self.fvar();
        let nil = self.nil();
        let cb = self.contains_bool_of(nil, u);
        let t = self.bool_true_val();
        let premise = self.eq_bool(cb, t);
        let body = {
            let ip = {
                let lemma = self
                    .k
                    .const_(self.n.is_prefix_of_is_prefix_bool_eq_true, vec![]);
                let e = self.k.app(lemma, u);
                let e = self.k.app(e, nil);
                self.k.app(e, hp)
            };
            let lemma = self.k.const_(self.n.contains_of_is_prefix, vec![]);
            let e = self.k.app(lemma, u);
            let e = self.k.app(e, nil);
            self.k.app(e, ip)
        };
        let with_hp = self.lam_fv(hp_fv, premise, body);
        self.lam_fv(u_fv, str_ty, with_hp)
    }

    /// `s = cons h t` case: case-split (`bool_cases_remember`) on the opaque
    /// `isPrefixBool u (cons h t)`.
    fn cons_row_proof_contains(&mut self, h: ExprId, t_: ExprId, ih_s: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (u_fv, u) = self.fvar();
        let consed = self.cons(h, t_);
        let v0 = self.is_prefix_bool_of(u, consed);
        let inner = self.bool_cases_remember(
            v0,
            &move |d, v| {
                let true_ = d.bool_true_val();
                let cb_t = d.contains_bool_of(t_, u);
                let cnd = d.bool_cond(v, true_, cb_t);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let tgt = d.contains_of(consed, u);
                d.arrow(prem2, tgt)
            },
            &move |d, _v_eq_false| {
                let (hp2_fv, hp2) = d.fvar();
                let true_ = d.bool_true_val();
                let cb_t = d.contains_bool_of(t_, u);
                let false_ = d.bool_false_val();
                let cnd = d.bool_cond(false_, true_, cb_t);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let tgt = d.contains_of(consed, u);
                // `hp2` (already reduced to `containsBool t_ u = true` in
                // this branch) is exactly `ih_s`'s premise, once `ih_s`
                // (`Π u, containsBool t_ u = true → contains t_ u`) is
                // applied at THIS `u`.
                let contains_t_u = {
                    let ih_at_u = d.k.app(ih_s, u);
                    d.k.app(ih_at_u, hp2)
                };
                // `contains t_ u = ∃ p0, ∃ t0, append (append p0 u) t0 = t_`
                // — unpack both existentials, then rebuild the witness at
                // `cons h t_` with outer witness `cons h p0`.
                let pred_outer_t = d.contains_outer_pred(t_, u);
                let body = d.exists_elim_str(
                    pred_outer_t,
                    tgt,
                    &move |d, p0, inner_ex| {
                        let pred_inner_t = d.contains_inner_pred(p0, u, t_);
                        d.exists_elim_str(
                            pred_inner_t,
                            tgt,
                            &move |d, t0, e0| {
                                let hp0 = d.cons(h, p0);
                                let p0_u = d.append(p0, u);
                                let p0_u_t0 = d.append(p0_u, t0);
                                let step1 = d.cons_congr_tail(h, p0_u_t0, t_, e0);
                                let target_c = d.cons(h, t_);
                                let pred_final = d.contains_inner_pred(hp0, u, target_c);
                                let outer_pred_final = d.contains_outer_pred(target_c, u);
                                let inner_ex_final = d.exists_intro_str(pred_final, t0, step1);
                                d.exists_intro_str(outer_pred_final, hp0, inner_ex_final)
                            },
                            inner_ex,
                        )
                    },
                    contains_t_u,
                );
                d.lam_fv(hp2_fv, prem2, body)
            },
            &move |d, v_eq_true| {
                let (hp2_fv, _hp2) = d.fvar();
                let true_ = d.bool_true_val();
                let cb_t = d.contains_bool_of(t_, u);
                let cnd = d.bool_cond(true_, true_, cb_t);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let ip = {
                    let lemma = d.k.const_(d.n.is_prefix_of_is_prefix_bool_eq_true, vec![]);
                    let e = d.k.app(lemma, u);
                    let e = d.k.app(e, consed);
                    d.k.app(e, v_eq_true)
                };
                let body = {
                    let lemma = d.k.const_(d.n.contains_of_is_prefix, vec![]);
                    let e = d.k.app(lemma, u);
                    let e = d.k.app(e, consed);
                    d.k.app(e, ip)
                };
                d.lam_fv(hp2_fv, prem2, body)
            },
        );
        self.lam_fv(u_fv, str_ty, inner)
    }

    /// `contains_of_containsBool_eq_true : ∀ (s u : Str),
    ///     Eq Bool (containsBool s u) Bool.true → contains s u`.
    fn prove_contains_of_contains_bool_eq_true(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let stmt = self.row_type_contains(s);
        let proof = self.induct(
            &|d, x| d.row_type_contains(x),
            &|d| d.nil_row_proof_contains(),
            &|d, h, t_, ih_s| d.cons_row_proof_contains(h, t_, ih_s),
            s,
        );
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.contains_of_contains_bool_eq_true;
        self.declare_theorem(name, ty, value)
    }
}
