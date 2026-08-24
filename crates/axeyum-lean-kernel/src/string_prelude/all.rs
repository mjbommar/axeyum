//! `Str.All : (Char → Prop) → Str → Prop` — "every character of this word
//! satisfies `p`" — plus `all_nil`, `all_append` (the splitting law: `All p`
//! distributes over `append`), and `all_of_isPrefix` (a prefix of a string
//! all of whose characters satisfy `p` also satisfies it).
//!
//! # Design — `Prop`-valued, built by structural recursion (not `Exists`)
//!
//! Unlike `isPrefix`/`isSuffix`/`contains` (`predicates.rs`), which are
//! existentials because they assert *some* witness exists, `All` is a
//! **universal** statement over a syntactically-bounded structure (`Str`
//! itself, via `Str.rec`) — exactly like `length`/`reverse`/`map`, just
//! landing in `Prop` (`Sort 0`) instead of `Nat`/`Str`. The definition:
//!
//! ```text
//! All ≔ λ (p : Char → Prop) (s : Str),
//!   Str.rec.{1} (motive := λ _ => Prop) True (λ h t ih => And (p h) ih) s
//! ```
//!
//! so `All p nil ≡ True` and `All p (cons h t) ≡ And (p h) (All p t)` hold by
//! ι-computation — the elimination target is `Prop` itself, an element of
//! `Sort 1`, so this instantiates `Str.rec.{1}`, the same level `length`'s
//! `Str → Nat` motive uses (`Nat : Sort 1` too).
//!
//! `Prop`-valued was chosen over a `Bool`-valued alternative for the same
//! reason `predicates.rs` chose `Prop` existentials over `Bool` decision
//! procedures: `all_of_isPrefix` needs to compose with `isPrefix`, which is
//! already `Prop`-valued (an `Exists`), and every law here is a fact a
//! reconstruction *cites*, not a value it *evaluates*. A `Bool`-valued `all`
//! would need nothing extra to define (it needs no `Char` equality, unlike a
//! decidable `isPrefix`), but it would not compose with `isPrefix` without an
//! extra soundness/completeness bridge lemma — not needed here.
//!
//! # What is proved
//!
//! | law               | statement                                                  | route |
//! |---------------------|-----------------------------------------------------------|-------|
//! | `all_nil`          | `∀ p, All p nil`                                            | ι, `True.intro` |
//! | `all_append`        | `∀ p s t, All p (append s t) → And (All p s) (All p t)`     | `Str.rec` induction on `s`, `And` intro/elim |
//! | `all_of_isPrefix`   | `∀ p pfx s, isPrefix pfx s → All p s → All p pfx`            | `Exists.rec` elimination + `all_append` |
//!
//! `all_append` is stated in the **splitting** direction (elimination, not
//! introduction) because that is the direction `all_of_isPrefix` needs: given
//! `isPrefix pfx s` (a witness `w` with `append pfx w = s`) and `All p s`,
//! transporting `All p s` along the witness equation gives
//! `All p (append pfx w)`, and `all_append` peels off `All p pfx`.
//!
//! This module duplicates `predicates.rs`'s private `is_prefix_pred`/
//! `exists_elim_str` builders rather than importing them — they are
//! `pub(self)` to that module's own `Dev`, and `Str` is already declared by
//! the time this module runs, exactly the situation `cancel.rs`'s module doc
//! notes for its own duplicated `tail_fn`.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_all_and_laws`] declares into, plus the
/// already-admitted `Str`/`Char`/`append`/`isPrefix` handles its terms are
/// built from.
#[derive(Debug, Clone, Copy)]
pub(super) struct AllNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub is_prefix: NameId,
    pub all_: NameId,
    pub all_nil: NameId,
    pub all_append: NameId,
    pub all_of_is_prefix: NameId,
}

/// Declare `All` as a checked structural recursion and prove its laws, in
/// dependency order.
pub(super) fn declare_all_and_laws(
    kernel: &mut Kernel,
    // By reference: `AllNames` embeds `LogicPrelude` and so exceeds clippy's
    // 256-byte `large_types_passed_by_value` limit, exactly the trap
    // `MonoidNames`/`PredicateNames`/`MapNames`/`FoldrNames` already hit.
    names: &AllNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_all()?;
    dev.prove_all_nil()?;
    dev.prove_all_append()?;
    dev.prove_all_of_is_prefix()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 18_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: AllNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    prop: ExprId,
    char_to_prop: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &AllNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let prop = k.sort_zero();
        let char_to_prop = k.pi(anon, char_ty, prop, BinderInfo::Default);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            str_ty,
            char_ty,
            prop,
            char_to_prop,
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

    /// `All p s` — the declared constant applied, not inlined.
    fn all_of(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let a = self.k.const_(self.n.all_, vec![]);
        self.apply(a, &[p, s])
    }

    /// `isPrefix p s` — the already-declared constant applied, not inlined.
    fn is_prefix_of(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.is_prefix, vec![]);
        self.apply(f, &[p, s])
    }

    /// `λ (t : Str), Eq Str (append p t) s` — the predicate `isPrefix p s`
    /// existentially quantifies. Duplicated from `predicates.rs`'s own
    /// `is_prefix_pred` (private to that module's `Dev`); see the module doc.
    fn is_prefix_pred(&mut self, p: ExprId, s: ExprId) -> ExprId {
        let (t_fv, t) = self.fvar();
        let apt = self.append(p, t);
        let body = self.eq(apt, s);
        let str_ty = self.str_ty;
        self.lam_fv(t_fv, str_ty, body)
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
    /// `Eq Str b a`. Mirrors `reverse::Dev::eq_symm`.
    fn eq_symm(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
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

    /// Transport `All p ·` along `heq : Eq Str a b`: from
    /// `proof : All p a` build `All p b`.
    fn transport_all(
        &mut self,
        p: ExprId,
        a: ExprId,
        b: ExprId,
        heq: ExprId,
        proof: ExprId,
    ) -> ExprId {
        let str_ty = self.str_ty;
        let motive = {
            let (z_fv, z) = self.fvar();
            let all_z = self.all_of(p, z);
            let hyp_ty = self.eq(a, z);
            let inner = self.k.lam(self.anon, hyp_ty, all_z, BinderInfo::Default);
            self.lam_fv(z_fv, str_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        self.apply(rec, &[str_ty, a, motive, proof, b, heq])
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

    /// `Exists.{1} Str pred`.
    fn exists_str(&mut self, pred: ExprId) -> ExprId {
        let ex = self.k.const_(self.n.logic.exists_, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(ex, &[str_ty, pred])
    }

    /// `Exists.rec.{1} Str pred motive minor major`, with the **non-dependent**
    /// motive `λ _ : Exists Str pred, result` — i.e. `Exists.elim` specialized
    /// to `Str`. Duplicated from `predicates.rs`'s own `exists_elim_str`
    /// (private to that module's `Dev`); see the module doc.
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

    /// `All : (Char → Prop) → Str → Prop`:
    ///
    /// ```text
    /// All ≔ λ (p : Char → Prop) (s : Str),
    ///   Str.rec.{1} (motive := λ _ => Prop) True (λ h t ih => And (p h) ih) s
    /// ```
    fn define_all(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let prop = self.prop;
        let char_to_prop = self.char_to_prop;

        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();

        // motive := λ (_ : Str), Prop.
        let motive = self.k.lam(self.anon, str_ty, prop, BinderInfo::Default);
        let true_minor = self.k.const_(self.n.logic.true_, vec![]);
        // minor for cons := λ (h : Char) (t : Str) (ih : Prop), And (p h) ih.
        let cons_minor = {
            let (h_fv, h) = self.fvar();
            let (t_fv, _t) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let ph = self.k.app(p, h);
            let and_ = self.k.const_(self.n.logic.and, vec![]);
            let e = self.k.app(and_, ph);
            let body = self.k.app(e, ih);
            let with_ih = self.lam_fv(ih_fv, prop, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_ih);
            self.lam_fv(h_fv, char_ty, with_t)
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.one]);
        let applied = self.apply(rec, &[motive, true_minor, cons_minor, s]);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied);
            self.lam_fv(p_fv, char_to_prop, with_s)
        };
        let ty = {
            let inner = self.arrow(str_ty, prop);
            self.arrow(char_to_prop, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.all_,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the laws -------------------------------------------------------------

    /// `all_nil : ∀ (p : Char → Prop), All p nil`.
    ///
    /// One ι-step: `All p nil ≡ True`, and `True.intro : True` closes it.
    fn prove_all_nil(&mut self) -> Result<(), KernelError> {
        let (p_fv, p) = self.fvar();
        let nil = self.nil();
        let stmt = self.all_of(p, nil);
        let proof = self.k.const_(self.n.logic.true_intro, vec![]);
        let char_to_prop = self.char_to_prop;
        let ty = self.pi_fv(p_fv, char_to_prop, stmt);
        let value = self.lam_fv(p_fv, char_to_prop, proof);
        let name = self.n.all_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `all_append : ∀ (p : Char → Prop) (s t : Str),
    ///     All p (append s t) → And (All p s) (All p t)`.
    ///
    /// Induction on `s`, `p`/`t` fixed.
    /// - **base** (`s = nil`): `append nil t ≡ t`, so the hypothesis is
    ///   already (up to ι) `All p t`; pair it with `all_nil p : All p nil`.
    /// - **step** (`s = cons h s'`): the hypothesis is (up to ι)
    ///   `And (p h) (All p (append s' t))`; `And.right` feeds the induction
    ///   hypothesis to split off `All p s'`/`All p t`, `And.left` recovers
    ///   `p h`, and `And.intro` reassembles `All p (cons h s')`/`All p t`.
    fn prove_all_append(&mut self) -> Result<(), KernelError> {
        let (p_fv, p) = self.fvar();
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();

        let goal = |d: &mut Self, x: ExprId| {
            let hyp_ty = {
                let ax = d.append(x, t);
                d.all_of(p, ax)
            };
            let concl_ty = {
                let all_x = d.all_of(p, x);
                let all_t = d.all_of(p, t);
                d.and_ty(all_x, all_t)
            };
            d.arrow(hyp_ty, concl_ty)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                // λ (hyp : All p (append nil t)), And.intro (All p nil) (All p t)
                //     (all_nil p) hyp
                let hyp_ty = {
                    let a = d.nil();
                    let ax = d.append(a, t);
                    d.all_of(p, ax)
                };
                let (hyp_fv, hyp) = d.fvar();
                let all_nil_p = {
                    let lemma = d.k.const_(d.n.all_nil, vec![]);
                    d.k.app(lemma, p)
                };
                let nil = d.nil();
                let all_nil_ty = d.all_of(p, nil);
                let all_t_ty = d.all_of(p, t);
                let body = d.and_intro(all_nil_ty, all_t_ty, all_nil_p, hyp);
                d.lam_fv(hyp_fv, hyp_ty, body)
            },
            &|d, h, sp, ih| {
                // hyp : All p (append (cons h sp) t), defeq
                //   And (p h) (All p (append sp t)).
                let hyp_ty = {
                    let consed = d.cons(h, sp);
                    let a = d.append(consed, t);
                    d.all_of(p, a)
                };
                let (hyp_fv, hyp) = d.fvar();
                let ph = d.k.app(p, h);
                let all_sp_t = {
                    let a = d.append(sp, t);
                    d.all_of(p, a)
                };
                let ph_proof = d.and_left(ph, all_sp_t, hyp);
                let rest = d.and_right(ph, all_sp_t, hyp);
                // ih : All p (append sp t) → And (All p sp) (All p t).
                let pair = d.k.app(ih, rest);
                let all_sp = d.all_of(p, sp);
                let all_t = d.all_of(p, t);
                let split_sp = d.and_left(all_sp, all_t, pair);
                let split_t = d.and_right(all_sp, all_t, pair);
                let all_cons = d.and_intro(ph, all_sp, ph_proof, split_sp);
                let all_cons_ty = {
                    let consed = d.cons(h, sp);
                    d.all_of(p, consed)
                };
                let concl = d.and_intro(all_cons_ty, all_t, all_cons, split_t);
                d.lam_fv(hyp_fv, hyp_ty, concl)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let char_to_prop = self.char_to_prop;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            let over_s = self.pi_fv(s_fv, str_ty, over_t);
            self.pi_fv(p_fv, char_to_prop, over_s)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            let over_s = self.lam_fv(s_fv, str_ty, over_t);
            self.lam_fv(p_fv, char_to_prop, over_s)
        };
        let name = self.n.all_append;
        self.declare_theorem(name, ty, value)
    }

    /// `And a b : Prop`.
    fn and_ty(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let and_ = self.k.const_(self.n.logic.and, vec![]);
        self.apply(and_, &[a, b])
    }

    /// `all_of_isPrefix : ∀ (p : Char → Prop) (pfx s : Str),
    ///     isPrefix pfx s → All p s → All p pfx`.
    ///
    /// Eliminates the `isPrefix pfx s` existential to a witness `w` and
    /// `heq : Eq Str (append pfx w) s`; transports `All p s` backward along
    /// `heq` (via `eq_symm`) to `All p (append pfx w)`, then `all_append`
    /// peels off `All p pfx`.
    fn prove_all_of_is_prefix(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_to_prop = self.char_to_prop;

        let (p_fv, p) = self.fvar();
        let (pfx_fv, pfx) = self.fvar();
        let (s_fv, s) = self.fvar();

        let hpfx_ty = self.is_prefix_of(pfx, s);
        let hall_ty = self.all_of(p, s);
        let target = self.all_of(p, pfx);

        let pred = self.is_prefix_pred(pfx, s);

        let (hpfx_fv, hpfx) = self.fvar();
        let (hall_fv, hall) = self.fvar();

        let body = self.exists_elim_str(
            pred,
            target,
            &|d, w, heq| {
                // heq : Eq Str (append pfx w) s.
                let append_pfx_w = d.append(pfx, w);
                let symm_heq = d.eq_symm(append_pfx_w, s, heq);
                let transported = d.transport_all(p, s, append_pfx_w, symm_heq, hall);
                // all_append p pfx w transported : And (All p pfx) (All p w).
                let pair = {
                    let lemma = d.k.const_(d.n.all_append, vec![]);
                    let e = d.k.app(lemma, p);
                    let e = d.k.app(e, pfx);
                    let e = d.k.app(e, w);
                    d.k.app(e, transported)
                };
                let all_pfx = d.all_of(p, pfx);
                let all_w = d.all_of(p, w);
                d.and_left(all_pfx, all_w, pair)
            },
            hpfx,
        );

        let value = {
            let with_hall = self.lam_fv(hall_fv, hall_ty, body);
            let with_hpfx = self.lam_fv(hpfx_fv, hpfx_ty, with_hall);
            let with_s = self.lam_fv(s_fv, str_ty, with_hpfx);
            let with_pfx = self.lam_fv(pfx_fv, str_ty, with_s);
            self.lam_fv(p_fv, char_to_prop, with_pfx)
        };
        let ty = {
            let inner = self.arrow(hall_ty, target);
            let with_hpfx = self.arrow(hpfx_ty, inner);
            let with_s = self.pi_fv(s_fv, str_ty, with_hpfx);
            let with_pfx = self.pi_fv(pfx_fv, str_ty, with_s);
            self.pi_fv(p_fv, char_to_prop, with_pfx)
        };
        let name = self.n.all_of_is_prefix;
        self.declare_theorem(name, ty, value)
    }
}
