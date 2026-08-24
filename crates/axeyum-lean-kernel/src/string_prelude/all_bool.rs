//! `Str.all_bool : (Char → Bool) → Str → Bool` — the `Bool`-valued twin of
//! [`super::all::AllNames::all_`] — plus `all_iff_All`, the bridge theorem
//! relating it to the `Prop`-valued `All p s` at `p := λ c, Eq Bool (q c)
//! Bool.true`.
//!
//! # Why this exists now
//!
//! `all.rs`'s module doc explains why `All` was built `Prop`-valued first:
//! a `Bool`-valued twin needed decidable `Char` equality, which did not
//! exist. It does now (`char_beq.rs`), and — critically — this twin does
//! **not actually need `char_beq`** to be built: `all_bool` folds an
//! arbitrary caller-supplied `q : Char → Bool` over the word via
//! short-circuit `Bool` "and" (`bool_cond`, reused from `str_beq.rs`'s
//! duplicate of `super::StringPrelude::bool_cond`), the same way `str_beq`
//! folds `char_beq` — decidable `Char` equality was the missing PATTERN,
//! not a missing ingredient of this particular function.
//!
//! # Design
//!
//! ```text
//! all_bool q nil        ≔ Bool.true
//! all_bool q (cons h t) ≔ bool_cond (q h) (all_bool q t) Bool.false
//! ```
//!
//! so a single `Bool.false` from any character short-circuits the whole
//! word to `Bool.false`, mirroring `str_beq`'s `cons`/`cons` short circuit.
//!
//! `all_iff_All` states, for the SAME underlying test lifted from `Bool` to
//! `Prop` (`p c := Eq Bool (q c) Bool.true`):
//!
//! ```text
//! all_iff_All : ∀ (q : Char → Bool) (s : Str),
//!     Iff (Eq Bool (all_bool q s) Bool.true) (All (λ c, Eq Bool (q c) Bool.true) s)
//! ```
//!
//! Proved by `Str.rec` induction on `s`. The `nil` case is two trivial
//! `Iff` directions (`Eq Bool Bool.true Bool.true` against `True`, both
//! ι-reducts of the two sides). The `cons` case case-splits on the opaque
//! `q h` via [`super::str_beq::Dev::bool_cases_remember`]'s idiom
//! (duplicated here, same reason as every other cross-module duplicate in
//! this slice — see `all.rs`'s module doc): the `false` branch relates two
//! "both sides are absurd" propositions via `And.left`/[`Self::false_bool_elim`],
//! and the `true` branch reduces to exactly the induction hypothesis `ih`
//! (an `Iff` on the tail), composed with `Iff.mp`/`Iff.mpr`. No step uses
//! `Classical.em`, `propext`, `funext`, or `Quot.sound`.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_all_bool_and_iff`] declares into, plus the
/// already-admitted `Char`/`Str`/`All` handles its terms are built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct AllBoolNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_rec: NameId,
    pub all_: NameId,
    pub all_bool: NameId,
    pub all_iff_all: NameId,
}

/// Declare `all_bool` as a checked structural recursion and prove
/// `all_iff_All`.
pub(super) fn declare_all_bool_and_iff(
    kernel: &mut Kernel,
    names: &AllBoolNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_all_bool()?;
    dev.prove_all_iff_all()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 40_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: AllBoolNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    bool_ty: ExprId,
    prop: ExprId,
    char_to_bool: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &AllBoolNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let bool_ty = k.const_(n.logic.bool_, vec![]);
        let prop = k.sort_zero();
        let char_to_bool = k.pi(anon, char_ty, bool_ty, BinderInfo::Default);
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
            char_to_bool,
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

    fn bool_true_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_true, vec![])
    }

    fn bool_false_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_false, vec![])
    }

    /// `all_bool q s` — the declared constant applied, not inlined.
    fn all_bool_of(&mut self, q: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.all_bool, vec![]);
        self.apply(f, &[q, s])
    }

    /// `All pred s` — the already-declared constant applied, not inlined.
    fn all_of(&mut self, pred: ExprId, s: ExprId) -> ExprId {
        let a = self.k.const_(self.n.all_, vec![]);
        self.apply(a, &[pred, s])
    }

    /// `λ (c : Char), Eq Bool (q c) Bool.true` — the `Prop`-valued predicate
    /// `All` needs, lifted from a `Bool`-valued `q`.
    fn pred_of(&mut self, q: ExprId) -> ExprId {
        let char_ty = self.char_ty;
        let (c_fv, c) = self.fvar();
        let qc = self.k.app(q, c);
        let t = self.bool_true_val();
        let body = self.eq_bool(qc, t);
        self.lam_fv(c_fv, char_ty, body)
    }

    /// `cond c t e : Bool` — duplicated from `str_beq::Dev::bool_cond` (see
    /// this module's doc for why).
    fn bool_cond(&mut self, c: ExprId, t: ExprId, e: ExprId) -> ExprId {
        let bool_ty = self.bool_ty;
        let motive = self.k.lam(self.anon, bool_ty, bool_ty, BinderInfo::Default);
        let rec = self.k.const_(self.n.logic.bool_rec, vec![self.one]);
        let e0 = self.k.app(rec, motive);
        let e0 = self.k.app(e0, e);
        let e0 = self.k.app(e0, t);
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

    /// `And a b : Prop`.
    fn and_ty(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let and_ = self.k.const_(self.n.logic.and, vec![]);
        self.apply(and_, &[a, b])
    }

    /// `And.intro a b proof_a proof_b : And a b`.
    fn and_intro(&mut self, a: ExprId, b: ExprId, proof_a: ExprId, proof_b: ExprId) -> ExprId {
        let c = self.k.const_(self.n.logic.and_intro, vec![]);
        self.apply(c, &[a, b, proof_a, proof_b])
    }

    /// `And.left a b proof : a`.
    fn and_left(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let c = self.k.const_(self.n.logic.and_left, vec![]);
        self.apply(c, &[a, b, proof])
    }

    /// `And.right a b proof : b`.
    fn and_right(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let c = self.k.const_(self.n.logic.and_right, vec![]);
        self.apply(c, &[a, b, proof])
    }

    /// `Iff a b : Prop`.
    fn iff_ty(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let iff = self.k.const_(self.n.logic.iff, vec![]);
        self.apply(iff, &[a, b])
    }

    /// `Iff.intro a b mp mpr : Iff a b`.
    fn iff_intro(&mut self, a: ExprId, b: ExprId, mp: ExprId, mpr: ExprId) -> ExprId {
        let c = self.k.const_(self.n.logic.iff_intro, vec![]);
        self.apply(c, &[a, b, mp, mpr])
    }

    /// `Iff.mp a b proof : a → b`.
    fn iff_mp(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let c = self.k.const_(self.n.logic.iff_mp, vec![]);
        self.apply(c, &[a, b, proof])
    }

    /// `Iff.mpr a b proof : b → a`.
    fn iff_mpr(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let c = self.k.const_(self.n.logic.iff_mpr, vec![]);
        self.apply(c, &[a, b, proof])
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

    /// Case-split on an opaque `Bool` term `v0` while keeping its identity
    /// available in each branch. Duplicated from `str_beq::Dev`'s helper of
    /// the same name (see that module's doc for the construction).
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

    /// `all_bool : (Char → Bool) → Str → Bool`:
    ///
    /// ```text
    /// all_bool ≔ λ (q : Char → Bool) (s : Str),
    ///   Str.rec.{1} (motive := λ _ => Bool) true
    ///     (λ h t ih => bool_cond (q h) ih false) s
    /// ```
    fn define_all_bool(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let bool_ty = self.bool_ty;
        let char_to_bool = self.char_to_bool;

        let (q_fv, q) = self.fvar();
        let (s_fv, s) = self.fvar();

        let motive = self.k.lam(self.anon, str_ty, bool_ty, BinderInfo::Default);
        let true_minor = self.bool_true_val();
        // minor for cons := λ (h : Char) (t : Str) (ih : Bool), cond (q h) ih false.
        let cons_minor = {
            let (h_fv, h) = self.fvar();
            let (t_fv, _t) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let qh = self.k.app(q, h);
            let false_ = self.bool_false_val();
            let body = self.bool_cond(qh, ih, false_);
            let with_ih = self.lam_fv(ih_fv, bool_ty, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_ih);
            self.lam_fv(h_fv, char_ty, with_t)
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let applied = self.apply(rec, &[motive, true_minor, cons_minor, s]);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied);
            self.lam_fv(q_fv, char_to_bool, with_s)
        };
        let ty = {
            let inner = self.arrow(str_ty, bool_ty);
            self.arrow(char_to_bool, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.all_bool,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the bridge theorem -----------------------------------------------

    /// `all_iff_All : ∀ (q : Char → Bool) (s : Str),
    ///     Iff (Eq Bool (all_bool q s) Bool.true) (All (λ c, Eq Bool (q c) Bool.true) s)`.
    #[allow(clippy::too_many_lines)] // straight-line proof by nested case split; see monoid.rs's same allow.
    fn prove_all_iff_all(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_to_bool = self.char_to_bool;

        let (q_fv, q) = self.fvar();
        let pred = self.pred_of(q);

        let goal = move |d: &mut Self, x: ExprId| {
            let ab = d.all_bool_of(q, x);
            let t = d.bool_true_val();
            let lhs = d.eq_bool(ab, t);
            let rhs = d.all_of(pred, x);
            d.iff_ty(lhs, rhs)
        };
        let (s_fv, s) = self.fvar();
        let stmt = goal(self, s);

        let proof = self.induct(
            &goal,
            &move |d| {
                // nil case: Iff (Eq Bool (all_bool q nil) true) (All pred nil)
                //   ≡ Iff (Eq Bool true true) True.
                let nil = d.nil();
                let ab = d.all_bool_of(q, nil);
                let t = d.bool_true_val();
                let lhs_ty = d.eq_bool(ab, t);
                let rhs_ty = d.all_of(pred, nil);

                let mp = {
                    let (hp_fv, _hp) = d.fvar();
                    let true_intro = d.k.const_(d.n.logic.true_intro, vec![]);
                    d.lam_fv(hp_fv, lhs_ty, true_intro)
                };
                let mpr = {
                    let (hq_fv, _hq) = d.fvar();
                    let t2 = d.bool_true_val();
                    let body = d.refl_bool(t2);
                    d.lam_fv(hq_fv, rhs_ty, body)
                };
                d.iff_intro(lhs_ty, rhs_ty, mp, mpr)
            },
            &move |d, h, t_, ih| {
                // cons case: case-split on `q h`.
                let v0 = d.k.app(q, h);
                d.bool_cases_remember(
                    v0,
                    &move |d, v| {
                        let false_ = d.bool_false_val();
                        let ab_t = d.all_bool_of(q, t_);
                        let cnd = d.bool_cond(v, ab_t, false_);
                        let tt = d.bool_true_val();
                        let lhs = d.eq_bool(cnd, tt);
                        let vt = d.eq_bool(v, tt);
                        let all_t = d.all_of(pred, t_);
                        let rhs = d.and_ty(vt, all_t);
                        d.iff_ty(lhs, rhs)
                    },
                    &move |d, _h_eq_false| {
                        // v = false: LHS ≡ Eq Bool false true (absurd);
                        // RHS = And (Eq Bool false true) (All pred t_).
                        let false_ = d.bool_false_val();
                        let ab_t = d.all_bool_of(q, t_);
                        let cnd = d.bool_cond(false_, ab_t, false_);
                        let tt = d.bool_true_val();
                        let lhs_ty = d.eq_bool(cnd, tt);
                        let vt = d.eq_bool(false_, tt);
                        let all_t = d.all_of(pred, t_);
                        let rhs_ty = d.and_ty(vt, all_t);

                        let mp = {
                            let (hp_fv, hp) = d.fvar();
                            let second = d.false_bool_elim(all_t, hp);
                            let body = d.and_intro(vt, all_t, hp, second);
                            d.lam_fv(hp_fv, lhs_ty, body)
                        };
                        let mpr = {
                            let (hq_fv, hq) = d.fvar();
                            let body = d.and_left(vt, all_t, hq);
                            d.lam_fv(hq_fv, rhs_ty, body)
                        };
                        d.iff_intro(lhs_ty, rhs_ty, mp, mpr)
                    },
                    &move |d, _h_eq_true| {
                        // v = true: LHS ≡ Eq Bool (all_bool q t_) true;
                        // RHS = And (Eq Bool true true) (All pred t_).
                        let true_ = d.bool_true_val();
                        let false_ = d.bool_false_val();
                        let ab_t = d.all_bool_of(q, t_);
                        let cnd = d.bool_cond(true_, ab_t, false_);
                        let tt = d.bool_true_val();
                        let lhs_ty = d.eq_bool(cnd, tt);
                        let vt = d.eq_bool(true_, tt);
                        let all_t = d.all_of(pred, t_);
                        let rhs_ty = d.and_ty(vt, all_t);
                        let ab_t2 = d.all_bool_of(q, t_);
                        let tt2 = d.bool_true_val();
                        let ih_lhs = d.eq_bool(ab_t2, tt2);

                        let mp = {
                            let (hp_fv, hp) = d.fvar();
                            let refl_tt = d.refl_bool(tt);
                            let all_part = d.iff_mp(ih_lhs, all_t, ih);
                            let all_part = d.k.app(all_part, hp);
                            let body = d.and_intro(vt, all_t, refl_tt, all_part);
                            d.lam_fv(hp_fv, lhs_ty, body)
                        };
                        let mpr = {
                            let (hq_fv, hq) = d.fvar();
                            let all_part = d.and_right(vt, all_t, hq);
                            let back = d.iff_mpr(ih_lhs, all_t, ih);
                            let body = d.k.app(back, all_part);
                            d.lam_fv(hq_fv, rhs_ty, body)
                        };
                        d.iff_intro(lhs_ty, rhs_ty, mp, mpr)
                    },
                )
            },
            s,
        );

        let ty = {
            let with_s = self.pi_fv(s_fv, str_ty, stmt);
            self.pi_fv(q_fv, char_to_bool, with_s)
        };
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, proof);
            self.lam_fv(q_fv, char_to_bool, with_s)
        };
        let name = self.n.all_iff_all;
        self.declare_theorem(name, ty, value)
    }
}
