//! `Str.beq : Str → Str → Bool` — structural decidable equality on words —
//! plus `str_beq_refl` and both propositional spec directions
//! (`str_eq_of_beq_eq_true`, `str_beq_eq_true_of_eq`): a genuine decision
//! procedure over the free monoid, built from [`super::char_beq`]'s
//! decidable equality on the alphabet.
//!
//! # Design — a double `Str.rec`, head compared via `char_beq`
//!
//! ```text
//! str_beq nil          u            = Str.rec (λ_.Bool) true  (λ _ _ _ => false) u
//! str_beq (cons h t)   nil          = false
//! str_beq (cons h t)   (cons h2 t2) = if char_beq h h2 then str_beq t t2 else false
//! ```
//!
//! — the same "outer `Str.rec` picks a row, inner `Str.rec` picks the cell"
//! shape [`super::StringPrelude::lex_cmp_fn`] already uses for lexicographic
//! comparison, with the row/cell combinator swapped from `char_eq`/`char_lt`
//! to `char_beq` plus the tail's own recursive call. `bool_cond`
//! (`Bool.rec`-based if-then-else) is duplicated here from
//! [`super::StringPrelude::bool_cond`] for the same "no stable name existed
//! yet at the point this needs it" reason `char_beq.rs` duplicates
//! `char_eq_fn`'s shape — see that module's doc.
//!
//! # What is proved, and how
//!
//! | law                     | statement                                             | route |
//! |---------------------------|--------------------------------------------------------|-------|
//! | `str_beq_refl`           | `∀ s, Eq Bool (str_beq s s) Bool.true`                 | `Str.rec` induction; the step needs `char_beq_refl h` (an opaque `h` does not make `char_beq h h` ι-reduce) transported into `bool_cond`'s condition via congruence, then `Eq.trans`ed with the induction hypothesis |
//! | `str_eq_of_beq_eq_true`  | `∀ a b, Eq Bool (str_beq a b) Bool.true → Eq Str a b`   | double `Str.rec` induction (outer `a`, inner `b`); the `cons`/`cons` cell case-splits on the opaque `char_beq h h2` via the "remembering" `Bool.rec` idiom ([`Dev::bool_cases_remember`]) so each branch keeps the propositional link between the split and the real discriminee |
//! | `str_beq_eq_true_of_eq`  | `∀ a b, Eq Str a b → Eq Bool (str_beq a b) Bool.true`   | `Eq.rec` transport of `str_beq_refl a` along the hypothesis — no induction needed |
//!
//! `str_eq_of_beq_eq_true`'s `cons`/`cons` case is the one place this module
//! needs more than a direct congruence: from a hypothesis
//! `Eq Bool (bool_cond (char_beq h h2) (str_beq t t2) Bool.false) Bool.true`
//! alone, `Bool.rec`'s ordinary elimination rule does **not** hand a branch
//! any fact connecting the case it is building to `char_beq h h2` itself —
//! that connection has to be carried explicitly, by generalizing the
//! discriminee together with `Eq.refl` of itself (Lean's `cases h : e`).
//! [`Dev::bool_cases_remember`] is exactly that construction, built once and
//! reused; without it the `true` branch would have no way to derive
//! `Eq Char h h2` from `char_eq_of_beq_eq_true`, and the goal
//! `Eq Str (cons h t) (cons h2 t2)` would be unreachable. No step in either
//! direction uses `Classical.em`, `propext`, `funext`, or `Quot.sound` — the
//! `Bool.rec` case split is exhaustive by construction (`Bool` has exactly
//! two constructors), not an appeal to excluded middle.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_str_beq_and_laws`] declares into, plus the
/// already-admitted `Char`/`Str`/`char_beq` handles its terms are built
/// from.
#[derive(Debug, Clone, Copy)]
pub(super) struct StrBeqNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub char_beq: NameId,
    pub char_beq_refl: NameId,
    pub char_eq_of_beq_eq_true: NameId,
    pub str_beq: NameId,
    pub str_beq_refl: NameId,
    pub str_eq_of_beq_eq_true: NameId,
    pub str_beq_eq_true_of_eq: NameId,
}

/// Declare `str_beq` as a checked double-`Str.rec` recursion and prove its
/// laws, in dependency order.
#[allow(clippy::too_many_lines)] // straight-line declaration sequence; see monoid.rs's same allow.
pub(super) fn declare_str_beq_and_laws(
    kernel: &mut Kernel,
    names: &StrBeqNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_str_beq()?;
    dev.prove_str_beq_refl()?;
    dev.prove_str_eq_of_beq_eq_true()?;
    dev.prove_str_beq_eq_true_of_eq()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 34_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: StrBeqNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    bool_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &StrBeqNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let bool_ty = k.const_(n.logic.bool_, vec![]);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            str_ty,
            char_ty,
            bool_ty,
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

    /// `char_beq a b` — the already-declared constant applied, not inlined.
    fn char_beq_of(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.char_beq, vec![]);
        self.apply(f, &[a, b])
    }

    /// `str_beq a b` — the declared constant applied, not inlined.
    fn str_beq_of(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.str_beq, vec![]);
        self.apply(f, &[a, b])
    }

    /// `cond c t e : Bool` — the `Bool` if-then-else via `Bool.rec`
    /// (`cond Bool.true t e ↝ t`, `cond Bool.false t e ↝ e`). Duplicated
    /// from `super::StringPrelude::bool_cond` (see the module doc).
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
    fn eq_str(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let st = self.str_ty;
        self.apply(eq, &[st, x, y])
    }

    /// `Eq.refl.{1} Str x : Eq Str x x`.
    fn refl_str(&mut self, x: ExprId) -> ExprId {
        let r = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let st = self.str_ty;
        self.apply(r, &[st, x])
    }

    /// `Eq.{1} Char x y`.
    fn eq_char(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let ct = self.char_ty;
        self.apply(eq, &[ct, x, y])
    }

    /// `Eq.trans`-style transport for `Bool`: from `h1 : Eq Bool a b` and
    /// `h2 : Eq Bool b c` build `Eq Bool a c`.
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
            let eq_a_z = self.eq_str(a, z);
            let eq_b_z = self.eq_str(b, z);
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

    /// Congruence in `bool_cond · t e` (the CONDITION argument varying, `t`
    /// and `e` fixed): from `proof : Eq Bool c c'` build
    /// `Eq Bool (bool_cond c t e) (bool_cond c' t e)`.
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

    /// Congruence in `Str.cons · tail` (the HEAD argument varying, `tail`
    /// fixed): from `proof : Eq Char x y` build
    /// `Eq Str (cons x tail) (cons y tail)`.
    fn cons_congr_head(&mut self, tail: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(x, tail);
        let motive = {
            let (z_fv, z) = self.fvar();
            let cons_z = self.cons(z, tail);
            let concl = self.eq_str(cons_x, cons_z);
            let hyp = self.eq_char(x, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
            let char_ty = self.char_ty;
            self.lam_fv(z_fv, char_ty, inner)
        };
        let base = self.refl_str(cons_x);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let char_ty = self.char_ty;
        self.apply(rec, &[char_ty, x, motive, base, y, proof])
    }

    /// Congruence in `Str.cons head ·` (the TAIL argument varying, `head`
    /// fixed): from `proof : Eq Str x y` build
    /// `Eq Str (cons head x) (cons head y)`. Mirrors `monoid::Dev::cons_congr`.
    fn cons_congr_tail(&mut self, head: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(head, x);
        let motive = {
            let (z_fv, z) = self.fvar();
            let cons_z = self.cons(head, z);
            let concl = self.eq_str(cons_x, cons_z);
            let hyp = self.eq_str(x, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
            let str_ty = self.str_ty;
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl_str(cons_x);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// Eliminate an impossible `Eq Bool Bool.false Bool.true` into
    /// `target : Prop`. Duplicated from `char_beq::Dev::false_bool_elim`
    /// (see that module's doc for why this is duplicated rather than
    /// shared).
    fn false_bool_elim(&mut self, target: ExprId, equality: ExprId) -> ExprId {
        let bool_ty = self.bool_ty;
        let false_v = self.bool_false_val();
        let true_v = self.bool_true_val();
        let prop = self.k.sort_zero();
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
    /// `Eq Bool v0 Bool.true`) — Lean's `cases h : e` idiom, built as
    /// `Bool.rec` over a motive `λ v, Eq Bool v0 v → result_ty(v)`, applied
    /// to `(v0, Eq.refl Bool v0)`. Plain `Bool.rec` on `v0` would forget the
    /// connection between the branch and `v0` itself; the `cons`/`cons` case
    /// of `str_eq_of_beq_eq_true` needs that connection to invoke
    /// `char_eq_of_beq_eq_true` on the real `char_beq h h2`, not on an
    /// unrelated bound `v`. Returns a term of type `result_ty(v0)`.
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

    /// `str_beq : Str → Str → Bool`, a double `Str.rec`:
    ///
    /// ```text
    /// str_beq nil          u            ≔ Str.rec (λ_.Bool) true (λ _ _ _ => false) u
    /// str_beq (cons h t)   u            ≔ Str.rec (λ_.Bool) false
    ///                                        (λ h2 t2 _ => cond (char_beq h h2) (str_beq t t2) false)
    ///                                        u
    /// ```
    fn define_str_beq(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let bool_ty = self.bool_ty;
        let str_to_bool = self.arrow(str_ty, bool_ty);

        let outer_motive = self
            .k
            .lam(self.anon, str_ty, str_to_bool, BinderInfo::Default);

        // Outer `nil` minor: `λ (u : Str), <is u nil?>`.
        let outer_nil_minor = {
            let (u_fv, u) = self.fvar();
            let inner_motive = self.k.lam(self.anon, str_ty, bool_ty, BinderInfo::Default);
            let inner_rec = self.k.const_(self.n.str_rec, vec![self.one]);
            let true_ = self.bool_true_val();
            let cons_minor = {
                let (h2_fv, _h2) = self.fvar();
                let (t2_fv, _t2) = self.fvar();
                let (ih2_fv, _ih2) = self.fvar();
                let false_ = self.bool_false_val();
                let with_ih2 = self.lam_fv(ih2_fv, bool_ty, false_);
                let with_t2 = self.lam_fv(t2_fv, str_ty, with_ih2);
                self.lam_fv(h2_fv, char_ty, with_t2)
            };
            let e0 = self.k.app(inner_rec, inner_motive);
            let e0 = self.k.app(e0, true_);
            let e0 = self.k.app(e0, cons_minor);
            let applied = self.k.app(e0, u);
            self.lam_fv(u_fv, str_ty, applied)
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

        let (a_fv, a) = self.fvar();
        let (b_fv, b) = self.fvar();
        let row = self.k.app(outer, a);
        let applied = self.k.app(row, b);
        let value = {
            let with_b = self.lam_fv(b_fv, str_ty, applied);
            self.lam_fv(a_fv, str_ty, with_b)
        };
        let ty = {
            let inner = self.arrow(str_ty, bool_ty);
            self.arrow(str_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.str_beq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- str_beq_refl ---------------------------------------------------------

    /// `str_beq_refl : ∀ (s : Str), Eq Bool (str_beq s s) Bool.true`.
    fn prove_str_beq_refl(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (s_fv, s) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let sb = d.str_beq_of(x, x);
            let t = d.bool_true_val();
            d.eq_bool(sb, t)
        };
        let stmt = goal(self, s);
        let proof = self.induct(
            &goal,
            &|d| {
                let t = d.bool_true_val();
                d.refl_bool(t)
            },
            &|d, h, t_, ih| {
                // Goal: Eq Bool (str_beq (cons h t_) (cons h t_)) Bool.true.
                // ι: str_beq (cons h t_)(cons h t_) ≡ bool_cond (char_beq h h)(str_beq t_ t_)(false).
                let cb_hh = d.char_beq_of(h, h);
                let true_ = d.bool_true_val();
                let false_ = d.bool_false_val();
                let sbtt = d.str_beq_of(t_, t_);
                let cond_lhs = d.bool_cond(cb_hh, sbtt, false_);
                let cond_rhs = {
                    let sbtt2 = d.str_beq_of(t_, t_);
                    d.bool_cond(true_, sbtt2, false_)
                };
                let refl_h = {
                    let lemma = d.k.const_(d.n.char_beq_refl, vec![]);
                    d.k.app(lemma, h)
                };
                let sbtt3 = d.str_beq_of(t_, t_);
                let step1 = d.bool_cond_congr_c(cb_hh, true_, sbtt3, false_, refl_h);
                d.bool_trans(cond_lhs, cond_rhs, true_, step1, ih)
            },
            s,
        );
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.str_beq_refl;
        self.declare_theorem(name, ty, value)
    }

    // --- str_eq_of_beq_eq_true -------------------------------------------------

    /// `Π b, Eq Bool (str_beq a b) Bool.true → Eq Str a b`.
    fn row_type_beq(&mut self, a: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (b_fv, b) = self.fvar();
        let sb = self.str_beq_of(a, b);
        let t = self.bool_true_val();
        let premise = self.eq_bool(sb, t);
        let concl = self.eq_str(a, b);
        let imp = self.arrow(premise, concl);
        self.pi_fv(b_fv, str_ty, imp)
    }

    /// The outer `nil` case of `str_eq_of_beq_eq_true`: builds the inner
    /// induction over `b`, producing a proof of `row_type_beq(nil)`.
    fn nil_row_proof(&mut self) -> ExprId {
        let str_ty = self.str_ty;
        let (b_fv, b) = self.fvar();
        let inner = self.induct(
            &|d, x| {
                let nil = d.nil();
                let sb = d.str_beq_of(nil, x);
                let t = d.bool_true_val();
                let premise = d.eq_bool(sb, t);
                let nil2 = d.nil();
                let concl = d.eq_str(nil2, x);
                d.arrow(premise, concl)
            },
            &|d| {
                // nil/nil: str_beq nil nil ≡ true; premise ≡ Eq Bool true true.
                let (hp_fv, _hp) = d.fvar();
                let nil = d.nil();
                let sb = d.str_beq_of(nil, nil);
                let t = d.bool_true_val();
                let premise = d.eq_bool(sb, t);
                let nil2 = d.nil();
                let body = d.refl_str(nil2);
                d.lam_fv(hp_fv, premise, body)
            },
            &|d, h2, t2, _ih2| {
                // nil/cons: str_beq nil (cons h2 t2) ≡ false → contradiction.
                let (hp_fv, hp) = d.fvar();
                let nil = d.nil();
                let consed = d.cons(h2, t2);
                let sb = d.str_beq_of(nil, consed);
                let t = d.bool_true_val();
                let premise = d.eq_bool(sb, t);
                let nil2 = d.nil();
                let target = d.eq_str(nil2, consed);
                let body = d.false_bool_elim(target, hp);
                d.lam_fv(hp_fv, premise, body)
            },
            b,
        );
        self.lam_fv(b_fv, str_ty, inner)
    }

    /// The outer `cons(h, t_, ih_a)` case of `str_eq_of_beq_eq_true`: builds
    /// the inner induction over `b`, producing a proof of
    /// `row_type_beq(cons h t_)`.
    fn cons_row_proof(&mut self, h: ExprId, t_: ExprId, ih_a: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let (b_fv, b) = self.fvar();
        let inner = self.induct(
            &move |d, x| {
                let consed = d.cons(h, t_);
                let sb = d.str_beq_of(consed, x);
                let t = d.bool_true_val();
                let premise = d.eq_bool(sb, t);
                let concl = d.eq_str(consed, x);
                d.arrow(premise, concl)
            },
            &move |d| {
                // cons/nil: str_beq (cons h t_) nil ≡ false → contradiction.
                let (hp_fv, hp) = d.fvar();
                let consed = d.cons(h, t_);
                let nil = d.nil();
                let sb = d.str_beq_of(consed, nil);
                let t = d.bool_true_val();
                let premise = d.eq_bool(sb, t);
                let nil2 = d.nil();
                let target = d.eq_str(consed, nil2);
                let body = d.false_bool_elim(target, hp);
                d.lam_fv(hp_fv, premise, body)
            },
            &move |d, h2, t2, _ih2| d.cons_cons_case(h, t_, ih_a, h2, t2),
            b,
        );
        self.lam_fv(b_fv, str_ty, inner)
    }

    /// The `cons h t_` / `cons h2 t2` cell: `bool_cases_remember` on
    /// `char_beq h h2` — the `false` branch is the impossible
    /// `Eq Bool Bool.false Bool.true`; the `true` branch combines
    /// `char_eq_of_beq_eq_true` (on the head) with the outer induction
    /// hypothesis `ih_a` applied to `t2` (on the tail) via two chained
    /// `cons` congruences.
    fn cons_cons_case(
        &mut self,
        h: ExprId,
        t_: ExprId,
        ih_a: ExprId,
        h2: ExprId,
        t2: ExprId,
    ) -> ExprId {
        // `bool_cases_remember` already returns a term of type
        // `result_ty(v0) = (Eq Bool (str_beq (cons h t_)(cons h2 t2)) true) →
        // Eq Str (cons h t_)(cons h2 t2)` (up to ι) — exactly the type this
        // `cons`/`cons` minor must have. No extra abstraction here: wrapping
        // it in a further `λ hp, …` would curry an argument the caller's
        // `induct` never supplies (caught by the unused-variable warning on
        // the `hp` this used to bind).
        let v0 = self.char_beq_of(h, h2);
        self.bool_cases_remember(
            v0,
            &move |d, v| {
                let false_ = d.bool_false_val();
                let sbt = d.str_beq_of(t_, t2);
                let cnd = d.bool_cond(v, sbt, false_);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let cl = d.cons(h, t_);
                let cr = d.cons(h2, t2);
                let tgt = d.eq_str(cl, cr);
                d.arrow(prem2, tgt)
            },
            &move |d, _h_eq_false| {
                let (hp2_fv, hp2) = d.fvar();
                let false_ = d.bool_false_val();
                let sbt = d.str_beq_of(t_, t2);
                let cnd = d.bool_cond(false_, sbt, false_);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);
                let cl = d.cons(h, t_);
                let cr = d.cons(h2, t2);
                let tgt = d.eq_str(cl, cr);
                let body2 = d.false_bool_elim(tgt, hp2);
                d.lam_fv(hp2_fv, prem2, body2)
            },
            &move |d, h_eq_true| {
                let (hp2_fv, hp2) = d.fvar();
                let true_ = d.bool_true_val();
                let false_ = d.bool_false_val();
                let sbt = d.str_beq_of(t_, t2);
                let cnd = d.bool_cond(true_, sbt, false_);
                let tt = d.bool_true_val();
                let prem2 = d.eq_bool(cnd, tt);

                let char_eq = {
                    let lemma = d.k.const_(d.n.char_eq_of_beq_eq_true, vec![]);
                    let e = d.k.app(lemma, h);
                    let e = d.k.app(e, h2);
                    d.k.app(e, h_eq_true)
                };
                let str_eq = {
                    let e = d.k.app(ih_a, t2);
                    d.k.app(e, hp2)
                };
                let step1 = d.cons_congr_head(t_, h, h2, char_eq);
                let step2 = d.cons_congr_tail(h2, t_, t2, str_eq);
                let cl = d.cons(h, t_);
                let mid = d.cons(h2, t_);
                let cr = d.cons(h2, t2);
                let target2 = d.str_trans(cl, mid, cr, step1, step2);
                d.lam_fv(hp2_fv, prem2, target2)
            },
        )
    }

    /// `str_eq_of_beq_eq_true : ∀ (a b : Str),
    ///     Eq Bool (str_beq a b) Bool.true → Eq Str a b`.
    fn prove_str_eq_of_beq_eq_true(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (a_fv, a) = self.fvar();
        let stmt = self.row_type_beq(a);
        let proof = self.induct(
            &|d, x| d.row_type_beq(x),
            &|d| d.nil_row_proof(),
            &|d, h, t_, ih_a| d.cons_row_proof(h, t_, ih_a),
            a,
        );
        let ty = self.pi_fv(a_fv, str_ty, stmt);
        let value = self.lam_fv(a_fv, str_ty, proof);
        let name = self.n.str_eq_of_beq_eq_true;
        self.declare_theorem(name, ty, value)
    }

    // --- str_beq_eq_true_of_eq -------------------------------------------------

    /// `str_beq_eq_true_of_eq : ∀ (a b : Str),
    ///     Eq Str a b → Eq Bool (str_beq a b) Bool.true`.
    ///
    /// Pure `Eq.rec` transport of `str_beq_refl a` along the hypothesis —
    /// no induction on `Str` needed, mirroring `char_beq`'s own
    /// `char_beq_eq_true_of_eq`.
    fn prove_str_beq_eq_true_of_eq(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let (a_fv, a) = self.fvar();
        let (b_fv, b) = self.fvar();
        let source = self.eq_str(a, b);
        let target = {
            let sb = self.str_beq_of(a, b);
            let t = self.bool_true_val();
            self.eq_bool(sb, t)
        };
        let (heq_fv, heq) = self.fvar();

        let motive = {
            let (z_fv, z) = self.fvar();
            let sb = self.str_beq_of(a, z);
            let t = self.bool_true_val();
            let concl = self.eq_bool(sb, t);
            let hyp = self.eq_str(a, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = {
            let lemma = self.k.const_(self.n.str_beq_refl, vec![]);
            self.k.app(lemma, a)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let body = self.apply(rec, &[str_ty, a, motive, base, b, heq]);

        let value = {
            let with_heq = self.lam_fv(heq_fv, source, body);
            let with_b = self.lam_fv(b_fv, str_ty, with_heq);
            self.lam_fv(a_fv, str_ty, with_b)
        };
        let ty = {
            let inner = self.arrow(source, target);
            let with_b = self.pi_fv(b_fv, str_ty, inner);
            self.pi_fv(a_fv, str_ty, with_b)
        };
        let name = self.n.str_beq_eq_true_of_eq;
        self.declare_theorem(name, ty, value)
    }
}
