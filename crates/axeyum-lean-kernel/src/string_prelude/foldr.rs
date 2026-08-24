//! `Str.foldr : Π (α : Sort u), (Char → α → α) → α → Str → α` — the universal
//! recursor over the free monoid, **universe-polymorphic in its result
//! type** so it folds into `Nat`, `Str`, a `Prop`, or anything else, exactly
//! `Str.rec` itself already is. Plus `foldr_nil`/`foldr_cons` (its defining
//! equations, both `Eq.refl`-closed) and the two laws that justify calling it
//! universal: `length_eq_foldr` (the existing `length` IS a fold) and
//! `append_eq_foldr` (so is `append`, folding `Str.cons` itself).
//!
//! # The definition, and its universe
//!
//! `Str.rec` (built by [`Kernel::add_recursive_datatype_family`] for `Str`)
//! is itself universe-polymorphic in its motive's target sort — this module
//! already instantiates it at `.{0}` for `Prop`-motive induction proofs and
//! at `.{1}` for `Str`/`Nat`-valued structural recursions (`monoid.rs`,
//! `length.rs`, `reverse.rs`, `take_drop.rs`). `foldr` just keeps that level
//! **open** as its own bound universe parameter `u` instead of fixing it:
//!
//! ```text
//! foldr.{u} ≔ λ (α : Sort u) (f : Char → α → α) (init : α) (s : Str),
//!   Str.rec.{u} (motive := λ _ => α) init (λ h t ih => f h ih) s
//! ```
//!
//! so `foldr α f init nil ≡ init` and
//! `foldr α f init (cons h t) ≡ f h (foldr α f init t)` hold by ι-computation
//! alone, exactly the `append`/`length`/`reverse`/`map` pattern — `foldr_nil`/
//! `foldr_cons` are that fact made citable by name, both closing by
//! `Eq.refl` alone.
//!
//! `α` is an **explicit** argument (not `{α}`): every call site here needs to
//! supply it anyway (`length_eq_foldr` instantiates at `Nat`, `append_eq_foldr`
//! at `Str`), and this module's own convention throughout `string_prelude`
//! passes recursor motives/carriers explicitly rather than through implicit
//! unification (`Exists.{u} (α : Sort u) (p : α → Prop) : Prop` in
//! [`LogicPrelude`] is the same choice).
//!
//! # What is proved
//!
//! | law               | statement                                                     | route |
//! |---------------------|------------------------------------------------------------|-------|
//! | `foldr_nil`        | `∀ α f init, foldr α f init nil = init`                      | ι, `Eq.refl` |
//! | `foldr_cons`       | `∀ α f init h t, foldr α f init (cons h t) = f h (foldr α f init t)` | ι, `Eq.refl` |
//! | `length_eq_foldr`  | `∀ s, length s = foldr Nat (fun _ n => succ n) zero s`        | `Str.rec` induction on `s`, `Nat.succ` congruence |
//! | `append_eq_foldr`  | `∀ s t, append s t = foldr Str Str.cons t s`                  | `Str.rec` induction on `s`, `cons`-congruence |
//!
//! Both fusion laws are proved the same way: the recursor being folded
//! (`length`/`append`) and `foldr` itself are two DIFFERENT `Str.rec`
//! applications with the same shape, so neither side ι-reduces into the
//! other automatically past the first `cons`/`nil` — a structural induction
//! bridges them, exactly like every other cross-definition law in this
//! prelude (`reverse_append`, `map_append`, …).

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_foldr`] declares into, plus the
/// already-admitted `Str`/`Char`/`append`/`length` handles its terms are
/// built from. `foldr_uparam` is the bound universe parameter `u` in
/// `foldr.{u}`'s own signature.
#[derive(Debug, Clone, Copy)]
pub(super) struct FoldrNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub str_rec: NameId,
    pub append: NameId,
    pub length: NameId,
    pub foldr: NameId,
    pub foldr_uparam: NameId,
    pub foldr_nil: NameId,
    pub foldr_cons: NameId,
    pub length_eq_foldr: NameId,
    pub append_eq_foldr: NameId,
}

/// Declare `foldr` as a checked, universe-polymorphic structural recursion
/// and prove its laws, in dependency order.
pub(super) fn declare_foldr(
    kernel: &mut Kernel,
    // By reference: `FoldrNames` embeds `LogicPrelude` and so exceeds
    // clippy's 256-byte `large_types_passed_by_value` limit, exactly the trap
    // `MonoidNames`/`TakeDropNames`/`MapNames` already hit.
    names: &FoldrNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_foldr()?;
    dev.prove_foldr_nil()?;
    dev.prove_foldr_cons()?;
    dev.prove_length_eq_foldr()?;
    dev.prove_append_eq_foldr()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 16_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: FoldrNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    u_lvl: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &FoldrNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let u_lvl = k.level_param(n.foldr_uparam);
        let str_ty = k.const_(n.str_ind, vec![]);
        let char_ty = k.const_(n.char_ind, vec![]);
        let nat_ty = k.const_(n.logic.nat, vec![]);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            u_lvl,
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

    /// `length s` — the already-declared constant applied, not inlined.
    fn length_of(&mut self, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.length, vec![]);
        self.k.app(f, s)
    }

    /// `foldr.{lvl} α f init s` — the declared constant applied at the given
    /// level instantiation, not inlined.
    fn foldr_of(
        &mut self,
        lvl: LevelId,
        alpha: ExprId,
        f: ExprId,
        init: ExprId,
        s: ExprId,
    ) -> ExprId {
        let c = self.k.const_(self.n.foldr, vec![lvl]);
        self.apply(c, &[alpha, f, init, s])
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

    /// `Eq.{lvl} α x y`, at an arbitrary carrier `alpha : Sort lvl`. Used for
    /// `foldr_nil`/`foldr_cons`, which are stated at the bound `α : Sort u`.
    fn eq_at(&mut self, lvl: LevelId, alpha: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![lvl]);
        self.apply(eq, &[alpha, x, y])
    }

    /// `Eq.refl.{lvl} α x : Eq α x x`.
    fn refl_at(&mut self, lvl: LevelId, alpha: ExprId, x: ExprId) -> ExprId {
        let refl = self.k.const_(self.n.logic.eq_refl, vec![lvl]);
        self.apply(refl, &[alpha, x])
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
        uparams: Vec<NameId>,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.k.add_declaration(Declaration::Theorem {
            name,
            uparams,
            ty,
            value,
        })
    }

    // --- the definition -----------------------------------------------------

    /// `foldr.{u} : Π (α : Sort u), (Char → α → α) → α → Str → α`:
    ///
    /// ```text
    /// foldr ≔ λ (α : Sort u) (f : Char → α → α) (init : α) (s : Str),
    ///   Str.rec.{u} (motive := λ _ => α) init (λ h t ih => f h ih) s
    /// ```
    fn define_foldr(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let sort_u = self.k.sort(self.u_lvl);

        let (alpha_fv, alpha) = self.fvar();
        let step_ty = {
            let a_to_a = self.arrow(alpha, alpha);
            self.arrow(char_ty, a_to_a)
        };
        let (f_fv, f) = self.fvar();
        let (init_fv, init) = self.fvar();
        let (s_fv, s) = self.fvar();

        // motive := λ (_ : Str), α (a non-dependent result, at `Sort u`).
        let motive = self.k.lam(self.anon, str_ty, alpha, BinderInfo::Default);
        // minor for cons := λ (h : Char) (t : Str) (ih : α), f h ih.
        let cons_minor = {
            let (h_fv, h) = self.fvar();
            let (t_fv, _t) = self.fvar();
            let (ih_fv, ih) = self.fvar();
            let fh = self.k.app(f, h);
            let body = self.k.app(fh, ih);
            let with_ih = self.lam_fv(ih_fv, alpha, body);
            let with_t = self.lam_fv(t_fv, str_ty, with_ih);
            self.lam_fv(h_fv, char_ty, with_t)
        };
        let rec = self.k.const_(self.n.str_rec, vec![self.u_lvl]);
        let applied = self.apply(rec, &[motive, init, cons_minor, s]);

        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, applied);
            let with_init = self.lam_fv(init_fv, alpha, with_s);
            let with_f = self.lam_fv(f_fv, step_ty, with_init);
            self.lam_fv(alpha_fv, sort_u, with_f)
        };
        let ty = {
            let with_s = self.arrow(str_ty, alpha);
            let with_init = self.arrow(alpha, with_s);
            let with_f = self.arrow(step_ty, with_init);
            self.pi_fv(alpha_fv, sort_u, with_f)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.foldr,
            uparams: vec![self.n.foldr_uparam],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the defining equations, by name ------------------------------------

    /// `foldr_nil.{u} : ∀ (α : Sort u) (f : Char → α → α) (init : α),
    ///     Eq α (foldr α f init nil) init`.
    ///
    /// One ι-step: the recursor's `nil` minor *is* `init`.
    fn prove_foldr_nil(&mut self) -> Result<(), KernelError> {
        let char_ty = self.char_ty;
        let sort_u = self.k.sort(self.u_lvl);
        let u_lvl = self.u_lvl;

        let (alpha_fv, alpha) = self.fvar();
        let step_ty = {
            let a_to_a = self.arrow(alpha, alpha);
            self.arrow(char_ty, a_to_a)
        };
        let (f_fv, f) = self.fvar();
        let (init_fv, init) = self.fvar();

        let nil = self.nil();
        let lhs = self.foldr_of(u_lvl, alpha, f, init, nil);
        let stmt = self.eq_at(u_lvl, alpha, lhs, init);
        let proof = self.refl_at(u_lvl, alpha, init);

        let ty = {
            let over_init = self.pi_fv(init_fv, alpha, stmt);
            let over_f = self.pi_fv(f_fv, step_ty, over_init);
            self.pi_fv(alpha_fv, sort_u, over_f)
        };
        let value = {
            let over_init = self.lam_fv(init_fv, alpha, proof);
            let over_f = self.lam_fv(f_fv, step_ty, over_init);
            self.lam_fv(alpha_fv, sort_u, over_f)
        };
        let name = self.n.foldr_nil;
        self.declare_theorem(name, vec![self.n.foldr_uparam], ty, value)
    }

    /// `foldr_cons.{u} : ∀ (α : Sort u) (f : Char → α → α) (init : α)
    ///     (h : Char) (t : Str),
    ///     Eq α (foldr α f init (cons h t)) (f h (foldr α f init t))`.
    ///
    /// The recursion's step equation, again by ι and `Eq.refl` — the
    /// recursor's own `ih` unfolds definitionally to `foldr α f init t`.
    fn prove_foldr_cons(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let char_ty = self.char_ty;
        let sort_u = self.k.sort(self.u_lvl);
        let u_lvl = self.u_lvl;

        let (alpha_fv, alpha) = self.fvar();
        let step_ty = {
            let a_to_a = self.arrow(alpha, alpha);
            self.arrow(char_ty, a_to_a)
        };
        let (f_fv, f) = self.fvar();
        let (init_fv, init) = self.fvar();
        let (h_fv, h) = self.fvar();
        let (t_fv, t) = self.fvar();

        let consed = self.cons(h, t);
        let lhs = self.foldr_of(u_lvl, alpha, f, init, consed);
        let foldr_t = self.foldr_of(u_lvl, alpha, f, init, t);
        let rhs = {
            let fh = self.k.app(f, h);
            self.k.app(fh, foldr_t)
        };
        let stmt = self.eq_at(u_lvl, alpha, lhs, rhs);
        let proof = self.refl_at(u_lvl, alpha, rhs);

        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            let over_h = self.pi_fv(h_fv, char_ty, over_t);
            let over_init = self.pi_fv(init_fv, alpha, over_h);
            let over_f = self.pi_fv(f_fv, step_ty, over_init);
            self.pi_fv(alpha_fv, sort_u, over_f)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            let over_h = self.lam_fv(h_fv, char_ty, over_t);
            let over_init = self.lam_fv(init_fv, alpha, over_h);
            let over_f = self.lam_fv(f_fv, step_ty, over_init);
            self.lam_fv(alpha_fv, sort_u, over_f)
        };
        let name = self.n.foldr_cons;
        self.declare_theorem(name, vec![self.n.foldr_uparam], ty, value)
    }

    // --- the subsumption laws -------------------------------------------------

    /// `length_eq_foldr : ∀ (s : Str),
    ///     Eq Nat (length s) (foldr Nat (fun _ n => Nat.succ n) Nat.zero s)`.
    ///
    /// Induction on `s`. Base: both sides ι-reduce to `Nat.zero`. Step: both
    /// sides ι/β-reduce to `Nat.succ ·`-wrapped forms and a `Nat.succ`
    /// congruence closes the gap via the induction hypothesis.
    fn prove_length_eq_foldr(&mut self) -> Result<(), KernelError> {
        let nat_ty = self.nat_ty;
        let char_ty = self.char_ty;
        let one = self.one;

        // step_fn := λ (_ : Char) (n : Nat), Nat.succ n.
        let step_fn = {
            let n_b = self.k.bvar(0);
            let succ_n = self.nat_succ(n_b);
            let inner = self.k.lam(self.anon, nat_ty, succ_n, BinderInfo::Default);
            self.k.lam(self.anon, char_ty, inner, BinderInfo::Default)
        };
        let zero = self.nat_zero();

        let (s_fv, s) = self.fvar();
        let goal = move |d: &mut Self, x: ExprId| {
            let lhs = d.length_of(x);
            let rhs = d.foldr_of(one, nat_ty, step_fn, zero, x);
            d.eq_nat(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                let zero = d.nat_zero();
                d.refl_nat(zero)
            },
            &move |d, _h, sp, ih| {
                let lhs_inner = d.length_of(sp);
                let rhs_inner = d.foldr_of(one, nat_ty, step_fn, zero, sp);
                d.succ_congr(lhs_inner, rhs_inner, ih)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.length_eq_foldr;
        self.declare_theorem(name, vec![], ty, value)
    }

    /// `append_eq_foldr : ∀ (s t : Str),
    ///     Eq Str (append s t) (foldr Str Str.cons t s)`.
    ///
    /// Induction on `s`, `t` fixed. Base: both sides ι-reduce to `t`. Step:
    /// both sides ι-reduce to `cons h ·`-wrapped forms (`Str.cons` is
    /// literally the `foldr` step function here, so `f h ih` unfolds to
    /// `cons h ih` with no further congruence work) and `cons_congr` closes
    /// the gap via the induction hypothesis.
    fn prove_append_eq_foldr(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let one = self.one;
        let cons_fn = self.k.const_(self.n.str_cons, vec![]);

        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let goal = move |d: &mut Self, x: ExprId| {
            let lhs = d.append(x, t);
            let rhs = d.foldr_of(one, str_ty, cons_fn, t, x);
            d.eq(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| d.refl(t),
            &move |d, h, sp, ih| {
                let lhs_inner = d.append(sp, t);
                let rhs_inner = d.foldr_of(one, str_ty, cons_fn, t, sp);
                d.cons_congr(h, lhs_inner, rhs_inner, ih)
            },
            s,
        );
        let stmt = goal(self, s);
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            self.pi_fv(s_fv, str_ty, over_t)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            self.lam_fv(s_fv, str_ty, over_t)
        };
        let name = self.n.append_eq_foldr;
        self.declare_theorem(name, vec![], ty, value)
    }
}
