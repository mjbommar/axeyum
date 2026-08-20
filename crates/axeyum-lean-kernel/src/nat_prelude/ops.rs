//! The reusable proof-construction layer: [`NatState`], [`NatOps`], [`NatDev`].
//!
//! Every declaration script in the sibling modules runs against this layer;
//! downstream developments implement [`NatOps`] with its two required methods.

use super::NatPrelude;
use super::bezout::{bezout_after_mp_exists, bezout_tail_exists};
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;

/// The non-kernel state a [`NatOps`] development carries: the interned prelude
/// names, the cached `Nat` type expression, the anonymous name root, and a
/// monotone free-variable counter.
///
/// The counter starts well above anything the type-checker's own
/// [`LocalContext`](crate::LocalContext) mints while descending the *closed*
/// terms a declaration hands it, so a development's free variables can never
/// collide with the kernel's.
#[derive(Debug)]
pub struct NatState {
    prelude: NatPrelude,
    anon: NameId,
    nat_ty: ExprId,
    next_fvar: u64,
}

/// The first free-variable id a [`NatState`] mints.
const FVAR_BASE: u64 = 1_000;

impl NatState {
    /// The state for a development over `prelude` in `kernel`.
    pub fn new(kernel: &mut Kernel, prelude: NatPrelude) -> Self {
        let anon = kernel.anon();
        let nat_ty = kernel.const_(prelude.nat, vec![]);
        Self {
            prelude,
            anon,
            nat_ty,
            next_fvar: FVAR_BASE,
        }
    }

    /// The interned names this development builds on.
    pub fn prelude(&self) -> NatPrelude {
        self.prelude
    }

    /// The expression `Nat` (the carrier type).
    pub fn nat_ty(&self) -> ExprId {
        self.nat_ty
    }

    /// The anonymous name root.
    pub fn anon(&self) -> NameId {
        self.anon
    }

    /// Mint a fresh free-variable id.
    pub fn fresh_fvar(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }
}

/// The reusable proof-construction layer over [`NatPrelude`].
///
/// Implement the two required methods on your own development struct — then all
/// of `Nat` arithmetic, the `Eq` combinators, induction, and the declaration
/// plumbing become methods on it, and your own operators can stay ordinary
/// inherent methods (so every closure below keeps taking `&mut YourDev`). For a
/// development that needs nothing of its own, [`NatDev`] is a ready-made
/// implementor over a borrowed kernel.
///
/// Every method here only *builds* terms except the three declaration helpers
/// ([`define_binary`](Self::define_binary), [`declare_theorem`](Self::declare_theorem),
/// [`try_theorem`](Self::try_theorem)/[`theorem`](Self::theorem)), which push
/// through the kernel's trusted gate and therefore re-type-check what they were
/// given.
pub trait NatOps {
    /// The kernel this development declares into.
    fn kernel(&mut self) -> &mut Kernel;

    /// The interned names and free-variable counter of this development.
    fn nat_state(&mut self) -> &mut NatState;

    // --- interned handles ---------------------------------------------------

    /// The prelude names (a `Copy` snapshot).
    fn prelude(&mut self) -> NatPrelude {
        self.nat_state().prelude()
    }

    /// The expression `Nat`.
    fn nat_ty(&mut self) -> ExprId {
        self.nat_state().nat_ty()
    }

    /// The anonymous name root (the binder name used for every generated
    /// binder — binder names are cosmetic, de Bruijn indices carry the meaning).
    fn anon_name(&mut self) -> NameId {
        self.nat_state().anon()
    }

    /// Mint a fresh free-variable id.
    fn fresh_fvar(&mut self) -> u64 {
        self.nat_state().fresh_fvar()
    }

    /// The universe level `1` (the level `Nat : Sort 1` lives at, and the `Eq`
    /// universe argument for equations between naturals).
    fn level_one(&mut self) -> LevelId {
        let z = self.kernel().level_zero();
        self.kernel().level_succ(z)
    }

    // --- term builders ------------------------------------------------------

    /// Left-associated application `head a1 a2 …`.
    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.kernel().app(e, a);
        }
        e
    }

    /// A universe-monomorphic constant applied to `args`.
    fn const_app(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let c = self.kernel().const_(name, vec![]);
        self.apply(c, args)
    }

    /// Apply a previously declared lemma to arguments (an alias of
    /// [`const_app`](Self::const_app) that reads as the proof step it is).
    fn lemma(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        self.const_app(name, args)
    }

    /// The computational `Bool` carrier.
    fn bool_ty(&mut self) -> ExprId {
        let name = self.prelude().logic.bool_;
        self.kernel().const_(name, vec![])
    }

    /// `Bool.true`.
    fn bool_true(&mut self) -> ExprId {
        let name = self.prelude().logic.bool_true;
        self.kernel().const_(name, vec![])
    }

    /// `Bool.false`.
    fn bool_false(&mut self) -> ExprId {
        let name = self.prelude().logic.bool_false;
        self.kernel().const_(name, vec![])
    }

    /// Computational `if condition then on_true else on_false` at `Nat`.
    fn bool_select_nat(&mut self, condition: ExprId, on_true: ExprId, on_false: ExprId) -> ExprId {
        let bool_ty = self.bool_ty();
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let motive = self.kernel().lam(anon, bool_ty, nat, BinderInfo::Default);
        let one = self.level_one();
        let bool_rec = self.prelude().logic.bool_rec;
        let rec = self.kernel().const_(bool_rec, vec![one]);
        self.apply(rec, &[motive, on_false, on_true, condition])
    }

    /// `Nat.zero`.
    fn zero(&mut self) -> ExprId {
        let n = self.prelude().zero;
        self.kernel().const_(n, vec![])
    }

    /// `Nat.succ x`.
    fn succ(&mut self, x: ExprId) -> ExprId {
        let n = self.prelude().succ;
        let s = self.kernel().const_(n, vec![]);
        self.kernel().app(s, x)
    }

    /// The unary numeral `succ^n zero`.
    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.zero();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }

    /// `Nat.add x y`.
    fn add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().add;
        self.const_app(f, &[x, y])
    }

    /// `Nat.mul x y`.
    fn mul(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().mul;
        self.const_app(f, &[x, y])
    }

    /// `Nat.pow x y`.
    fn pow(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().pow;
        self.const_app(f, &[x, y])
    }

    /// Computational natural-number equality `Nat.beq x y`.
    fn beq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().beq;
        self.const_app(f, &[x, y])
    }

    /// Shared executable division state; `selector = true` gives the quotient
    /// and `selector = false` the remainder.
    fn div_mod_state(&mut self, divisor: ExprId, dividend: ExprId, selector: ExprId) -> ExprId {
        let f = self.prelude().div_mod_state;
        self.const_app(f, &[divisor, dividend, selector])
    }

    /// Total executable quotient `Nat.div dividend divisor`.
    fn div(&mut self, dividend: ExprId, divisor: ExprId) -> ExprId {
        let f = self.prelude().div;
        self.const_app(f, &[dividend, divisor])
    }

    /// Total executable remainder `Nat.mod dividend divisor`.
    fn modulo(&mut self, dividend: ExprId, divisor: ExprId) -> ExprId {
        let f = self.prelude().mod_;
        self.const_app(f, &[dividend, divisor])
    }

    /// Executable Euclidean `Nat.gcd left right`, with Lean's first-argument
    /// recursion orientation.
    fn gcd(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let f = self.prelude().gcd;
        self.const_app(f, &[left, right])
    }

    /// Balanced natural Bézout certificates for `g` over generators `m,n`.
    fn bezout(&mut self, m: ExprId, n: ExprId, g: ExprId) -> ExprId {
        let f = self.prelude().bezout;
        self.const_app(f, &[m, n, g])
    }

    /// The equality carried by a balanced Bézout certificate.
    #[allow(clippy::too_many_arguments)]
    fn bezout_equation(
        &mut self,
        m: ExprId,
        n: ExprId,
        g: ExprId,
        mp: ExprId,
        mn: ExprId,
        np: ExprId,
        nn: ExprId,
    ) -> ExprId {
        let m_negative = self.mul(m, mn);
        let n_negative = self.mul(n, nn);
        let g_plus_m_negative = self.add(g, m_negative);
        let left = self.add(g_plus_m_negative, n_negative);
        let m_positive = self.mul(m, mp);
        let n_positive = self.mul(n, np);
        let right = self.add(m_positive, n_positive);
        self.eq(left, right)
    }

    /// `∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np`.
    fn bezout_witnesses(&mut self, m: ExprId, n: ExprId, g: ExprId) -> ExprId {
        let nat = self.nat_ty();
        let one = self.level_one();
        let exists_name = self.prelude().logic.exists_;

        let mp_fv = self.fresh_fvar();
        let mp = self.kernel().fvar(mp_fv);
        let mn_fv = self.fresh_fvar();
        let mn = self.kernel().fvar(mn_fv);
        let np_fv = self.fresh_fvar();
        let np = self.kernel().fvar(np_fv);
        let nn_fv = self.fresh_fvar();
        let nn = self.kernel().fvar(nn_fv);
        let equation = self.bezout_equation(m, n, g, mp, mn, np, nn);
        let nn_predicate = self.lam_fv(nn_fv, nat, equation);
        let exists = self.kernel().const_(exists_name, vec![one]);
        let nn_exists = self.apply(exists, &[nat, nn_predicate]);
        let np_predicate = self.lam_fv(np_fv, nat, nn_exists);
        let exists = self.kernel().const_(exists_name, vec![one]);
        let np_exists = self.apply(exists, &[nat, np_predicate]);
        let mn_predicate = self.lam_fv(mn_fv, nat, np_exists);
        let exists = self.kernel().const_(exists_name, vec![one]);
        let mn_exists = self.apply(exists, &[nat, mn_predicate]);
        let mp_predicate = self.lam_fv(mp_fv, nat, mn_exists);
        let exists = self.kernel().const_(exists_name, vec![one]);
        self.apply(exists, &[nat, mp_predicate])
    }

    /// Introduce all four witnesses of a balanced Bézout certificate.
    #[allow(clippy::too_many_arguments)]
    fn bezout_intro(
        &mut self,
        m: ExprId,
        n: ExprId,
        g: ExprId,
        mp: ExprId,
        mn: ExprId,
        np: ExprId,
        nn: ExprId,
        equation: ExprId,
    ) -> ExprId
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let one = self.level_one();
        let intro_name = self.prelude().logic.exists_intro;
        let exists_name = self.prelude().logic.exists_;

        let nn_fv = self.fresh_fvar();
        let nn_var = self.kernel().fvar(nn_fv);
        let nn_body = self.bezout_equation(m, n, g, mp, mn, np, nn_var);
        let nn_predicate = self.lam_fv(nn_fv, nat, nn_body);
        let intro = self.kernel().const_(intro_name, vec![one]);
        let nn_exists = self.apply(intro, &[nat, nn_predicate, nn, equation]);

        let np_fv = self.fresh_fvar();
        let np_var = self.kernel().fvar(np_fv);
        let np_body = {
            let nn_fv = self.fresh_fvar();
            let nn_var = self.kernel().fvar(nn_fv);
            let equation = self.bezout_equation(m, n, g, mp, mn, np_var, nn_var);
            let predicate = self.lam_fv(nn_fv, nat, equation);
            let exists = self.kernel().const_(exists_name, vec![one]);
            self.apply(exists, &[nat, predicate])
        };
        let np_predicate = self.lam_fv(np_fv, nat, np_body);
        let intro = self.kernel().const_(intro_name, vec![one]);
        let np_exists = self.apply(intro, &[nat, np_predicate, np, nn_exists]);

        let mn_fv = self.fresh_fvar();
        let mn_var = self.kernel().fvar(mn_fv);
        let mn_body = bezout_tail_exists(self, m, n, g, mp, mn_var);
        let mn_predicate = self.lam_fv(mn_fv, nat, mn_body);
        let intro = self.kernel().const_(intro_name, vec![one]);
        let mn_exists = self.apply(intro, &[nat, mn_predicate, mn, np_exists]);

        let mp_fv = self.fresh_fvar();
        let mp_var = self.kernel().fvar(mp_fv);
        let mp_body = bezout_after_mp_exists(self, m, n, g, mp_var);
        let mp_predicate = self.lam_fv(mp_fv, nat, mp_body);
        let intro = self.kernel().const_(intro_name, vec![one]);
        self.apply(intro, &[nat, mp_predicate, mp, mn_exists])
    }

    /// `Nat.pred x`.
    fn pred(&mut self, x: ExprId) -> ExprId {
        let f = self.prelude().pred;
        self.const_app(f, &[x])
    }

    /// Truncated subtraction `Nat.sub x y`.
    fn sub(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().sub;
        self.const_app(f, &[x, y])
    }

    /// `Nat.sumRange f n`.
    fn sum_range(&mut self, f: ExprId, n: ExprId) -> ExprId {
        let name = self.prelude().sum_range;
        self.const_app(name, &[f, n])
    }

    /// `Nat.factorial n`.
    fn factorial(&mut self, n: ExprId) -> ExprId {
        let name = self.prelude().factorial;
        self.const_app(name, &[n])
    }

    /// `Nat.le x y` (the `Prop` `x ≤ y`).
    fn le(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().le;
        self.const_app(f, &[x, y])
    }

    /// `Nat.lt x y` (definitionally `Nat.le (Nat.succ x) y`).
    fn lt(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().lt;
        self.const_app(f, &[x, y])
    }

    /// `Nat.inClosedInterval lower upper value`.
    fn in_closed_interval(&mut self, lower: ExprId, upper: ExprId, value: ExprId) -> ExprId {
        let f = self.prelude().in_closed_interval;
        self.const_app(f, &[lower, upper, value])
    }

    /// `Nat.divMod divisor dividend quotient remainder`.
    fn div_mod(
        &mut self,
        divisor: ExprId,
        dividend: ExprId,
        quotient: ExprId,
        remainder: ExprId,
    ) -> ExprId {
        let f = self.prelude().div_mod;
        self.const_app(f, &[divisor, dividend, quotient, remainder])
    }

    /// `Nat.dvd a n` (the proposition `a ∣ n`).
    fn dvd(&mut self, a: ExprId, n: ExprId) -> ExprId {
        let f = self.prelude().dvd;
        self.const_app(f, &[a, n])
    }

    /// `Nat.modEq d a b` (balanced witnesses: `∃ u v, a+d*u=b+d*v`).
    fn mod_eq(&mut self, d: ExprId, a: ExprId, b: ExprId) -> ExprId {
        let f = self.prelude().mod_eq;
        self.const_app(f, &[d, a, b])
    }

    /// One side of a balanced congruence witness, `a + d*u`.
    fn mod_eq_sum(&mut self, d: ExprId, a: ExprId, u: ExprId) -> ExprId {
        let multiple = self.mul(d, u);
        self.add(a, multiple)
    }

    /// `fun v : Nat => a+d*u=b+d*v`.
    fn mod_eq_inner_predicate(&mut self, d: ExprId, a: ExprId, b: ExprId, u: ExprId) -> ExprId {
        let v_fv = self.fresh_fvar();
        let v = self.kernel().fvar(v_fv);
        let lhs = self.mod_eq_sum(d, a, u);
        let rhs = self.mod_eq_sum(d, b, v);
        let body = self.eq(lhs, rhs);
        let nat = self.nat_ty();
        self.lam_fv(v_fv, nat, body)
    }

    /// `∃ v, a+d*u=b+d*v`.
    fn mod_eq_inner_exists(&mut self, d: ExprId, a: ExprId, b: ExprId, u: ExprId) -> ExprId {
        let predicate = self.mod_eq_inner_predicate(d, a, b, u);
        let one = self.level_one();
        let exists_name = self.prelude().logic.exists_;
        let exists = self.kernel().const_(exists_name, vec![one]);
        let nat = self.nat_ty();
        self.apply(exists, &[nat, predicate])
    }

    /// `fun u : Nat => ∃ v, a+d*u=b+d*v`.
    fn mod_eq_outer_predicate(&mut self, d: ExprId, a: ExprId, b: ExprId) -> ExprId {
        let u_fv = self.fresh_fvar();
        let u = self.kernel().fvar(u_fv);
        let body = self.mod_eq_inner_exists(d, a, b, u);
        let nat = self.nat_ty();
        self.lam_fv(u_fv, nat, body)
    }

    /// `∃ u v, a+d*u=b+d*v`.
    fn mod_eq_witnesses(&mut self, d: ExprId, a: ExprId, b: ExprId) -> ExprId {
        let predicate = self.mod_eq_outer_predicate(d, a, b);
        let one = self.level_one();
        let exists_name = self.prelude().logic.exists_;
        let exists = self.kernel().const_(exists_name, vec![one]);
        let nat = self.nat_ty();
        self.apply(exists, &[nat, predicate])
    }

    /// `Nat.valuationAt a n e`, exact divisibility by `a^e`.
    fn valuation_at(&mut self, a: ExprId, n: ExprId, e: ExprId) -> ExprId {
        let f = self.prelude().valuation_at;
        self.const_app(f, &[a, n, e])
    }

    /// `fun q : Nat => Eq Nat n (a * q)`, the witness predicate defining
    /// [`NatPrelude::dvd`].
    fn dvd_predicate(&mut self, a: ExprId, n: ExprId) -> ExprId {
        let q_fv = self.fresh_fvar();
        let q = self.kernel().fvar(q_fv);
        let aq = self.mul(a, q);
        let body = self.eq(n, aq);
        let nat = self.nat_ty();
        self.lam_fv(q_fv, nat, body)
    }

    // --- binders ------------------------------------------------------------

    /// `fun (_ : ty) => body`, abstracting the free variable `fv` in `body`.
    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel().abstract_fvars(body, &[fv]);
        let anon = self.anon_name();
        self.kernel().lam(anon, ty, b, BinderInfo::Default)
    }

    /// `∀ (_ : ty), body`, abstracting the free variable `fv` in `body`.
    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel().abstract_fvars(body, &[fv]);
        let anon = self.anon_name();
        self.kernel().pi(anon, ty, b, BinderInfo::Default)
    }

    /// The non-dependent arrow `dom → cod`.
    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        let anon = self.anon_name();
        self.kernel().pi(anon, dom, cod, BinderInfo::Default)
    }

    // --- Eq -----------------------------------------------------------------

    /// `Eq.{1} Nat x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.prelude().logic.eq;
        let eq = self.kernel().const_(name, vec![one]);
        let nat = self.nat_ty();
        self.apply(eq, &[nat, x, y])
    }

    /// `Eq.refl.{1} Nat a : Eq Nat a a`.
    fn refl(&mut self, a: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.prelude().logic.eq_refl;
        let refl = self.kernel().const_(name, vec![one]);
        let nat = self.nat_ty();
        self.apply(refl, &[nat, a])
    }

    /// `Eq.{1} Bool x y`.
    fn bool_eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.prelude().logic.eq;
        let eq = self.kernel().const_(name, vec![one]);
        let bool_ty = self.bool_ty();
        self.apply(eq, &[bool_ty, x, y])
    }

    /// `Eq.refl.{1} Bool value`.
    fn bool_refl(&mut self, value: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.prelude().logic.eq_refl;
        let refl = self.kernel().const_(name, vec![one]);
        let bool_ty = self.bool_ty();
        self.apply(refl, &[bool_ty, value])
    }

    /// `h : Eq Bool a b  ⊢  Eq Bool b a`.
    fn bool_symm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId
    where
        Self: Sized,
    {
        let motive = self.bool_eq_motive(a, &|d, value| d.bool_eq(value, a));
        let refl_case = self.bool_refl(a);
        self.bool_transport(a, motive, refl_case, b, h)
    }

    /// `h1 : Eq Bool a b`, `h2 : Eq Bool b c  ⊢  Eq Bool a c`.
    fn bool_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId
    where
        Self: Sized,
    {
        let motive = self.bool_eq_motive(b, &|d, value| d.bool_eq(a, value));
        self.bool_transport(b, motive, h1, c, h2)
    }

    /// `Eq.rec.{0,1} Bool p motive refl_case q h : motive q h`.
    fn bool_transport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let zero = self.kernel().level_zero();
        let one = self.level_one();
        let eq_rec = self.prelude().logic.eq_rec;
        let rec = self.kernel().const_(eq_rec, vec![zero, one]);
        let bool_ty = self.bool_ty();
        self.apply(rec, &[bool_ty, p, motive, refl_case, q, h])
    }

    /// Build `fun (x : Bool) (_ : Eq Bool a x) => body x`.
    fn bool_eq_motive(&mut self, a: ExprId, body: &dyn Fn(&mut Self, ExprId) -> ExprId) -> ExprId
    where
        Self: Sized,
    {
        let value_fv = self.fresh_fvar();
        let value = self.kernel().fvar(value_fv);
        let conclusion = body(self, value);
        let equality = self.bool_eq(a, value);
        let anon = self.anon_name();
        let inner = self
            .kernel()
            .lam(anon, equality, conclusion, BinderInfo::Default);
        let bool_ty = self.bool_ty();
        self.lam_fv(value_fv, bool_ty, inner)
    }

    /// Eliminate an impossible equality `Bool.false = Bool.true` into `target`.
    fn false_true_elim(&mut self, target: ExprId, equality: ExprId) -> ExprId {
        let logic = self.prelude().logic;
        let bool_ty = self.bool_ty();
        let false_value = self.bool_false();
        let true_value = self.bool_true();
        let prop = self.kernel().sort_zero();
        let anon = self.anon_name();
        let zero = self.kernel().level_zero();
        let one = self.level_one();
        let discriminator = {
            let motive = self.kernel().lam(anon, bool_ty, prop, BinderInfo::Default);
            // Selecting a proposition eliminates into `Sort 1`: the selected
            // proposition itself has type `Prop : Sort 1`.
            let rec = self.kernel().const_(logic.bool_rec, vec![one]);
            let false_prop = self.kernel().const_(logic.false_, vec![]);
            let true_prop = self.kernel().const_(logic.true_, vec![]);
            self.apply(rec, &[motive, true_prop, false_prop])
        };
        let motive = {
            let value_fv = self.fresh_fvar();
            let value = self.kernel().fvar(value_fv);
            let equality_ty = self.bool_eq(false_value, value);
            let body = self.apply(discriminator, &[value]);
            let inner = self
                .kernel()
                .lam(anon, equality_ty, body, BinderInfo::Default);
            self.lam_fv(value_fv, bool_ty, inner)
        };
        let true_intro = self.kernel().const_(logic.true_intro, vec![]);
        let eq_rec = self.kernel().const_(logic.eq_rec, vec![zero, one]);
        let impossible = self.apply(
            eq_rec,
            &[
                bool_ty,
                false_value,
                motive,
                true_intro,
                true_value,
                equality,
            ],
        );
        let false_rec = self.kernel().const_(logic.false_rec, vec![zero]);
        let false_ty = self.kernel().const_(logic.false_, vec![]);
        let false_motive = self
            .kernel()
            .lam(anon, false_ty, target, BinderInfo::Default);
        self.apply(false_rec, &[false_motive, impossible])
    }

    /// `Eq.rec.{0,1} Nat p motive refl_case q h : motive q h`.
    fn transport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel().level_zero();
        let one = self.level_one();
        let name = self.prelude().logic.eq_rec;
        let rec = self.kernel().const_(name, vec![z, one]);
        let nat = self.nat_ty();
        self.apply(rec, &[nat, p, motive, refl_case, q, h])
    }

    /// Build the `Eq.rec` motive `fun (x : Nat) (_ : Eq Nat a x) => body(x)`.
    fn eq_motive(&mut self, a: ExprId, body: &dyn Fn(&mut Self, ExprId) -> ExprId) -> ExprId
    where
        Self: Sized,
    {
        let x_fv = self.fresh_fvar();
        let x = self.kernel().fvar(x_fv);
        let concl = body(self, x);
        let hyp = self.eq(a, x);
        let anon = self.anon_name();
        let inner = self.kernel().lam(anon, hyp, concl, BinderInfo::Default);
        let nat = self.nat_ty();
        self.lam_fv(x_fv, nat, inner)
    }

    /// `h : Eq Nat a b  ⊢  Eq Nat b a`.
    fn symm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId
    where
        Self: Sized,
    {
        let motive = self.eq_motive(a, &|d, x| d.eq(x, a));
        let refl_case = self.refl(a);
        self.transport(a, motive, refl_case, b, h)
    }

    /// `h1 : Eq Nat a b`, `h2 : Eq Nat b c  ⊢  Eq Nat a c`.
    fn trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId
    where
        Self: Sized,
    {
        let motive = self.eq_motive(b, &|d, x| d.eq(a, x));
        self.transport(b, motive, h1, c, h2)
    }

    /// Chain `a = x1 = x2 = … = z` from `(rhs, proof)` steps, returning the last
    /// right-hand side and a proof of `Eq Nat start last`.
    fn chain(&mut self, start: ExprId, steps: &[(ExprId, ExprId)]) -> (ExprId, ExprId)
    where
        Self: Sized,
    {
        let mut current = start;
        let mut proof = self.refl(start);
        for &(next, step) in steps {
            proof = self.trans(start, current, next, proof, step);
            current = next;
        }
        (current, proof)
    }

    /// Congruence in an arbitrary one-hole context: `h : Eq Nat a b` gives
    /// `Eq Nat (f a) (f b)`.
    fn congr(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId
    where
        Self: Sized,
    {
        let fa = f(self, a);
        let motive = self.eq_motive(a, &|d, x| {
            let fx = f(d, x);
            d.eq(fa, fx)
        });
        let refl_case = self.refl(fa);
        self.transport(a, motive, refl_case, b, h)
    }

    // --- induction ----------------------------------------------------------

    /// `Nat.rec.{0} (fun x => p x) base (fun j ih => step j ih) target`, a proof
    /// of `p target` for a `Prop`-valued motive.
    fn induct(
        &mut self,
        p: &dyn Fn(&mut Self, ExprId) -> ExprId,
        base: &dyn Fn(&mut Self) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let motive = {
            let x_fv = self.fresh_fvar();
            let x = self.kernel().fvar(x_fv);
            let body = p(self, x);
            self.lam_fv(x_fv, nat, body)
        };
        let base_term = base(self);
        let step_term = {
            let j_fv = self.fresh_fvar();
            let j = self.kernel().fvar(j_fv);
            let ih_fv = self.fresh_fvar();
            let ih = self.kernel().fvar(ih_fv);
            let hyp_ty = p(self, j);
            let body = step(self, j, ih);
            let inner = self.lam_fv(ih_fv, hyp_ty, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let z = self.kernel().level_zero();
        let name = self.prelude().rec;
        let rec = self.kernel().const_(name, vec![z]);
        self.apply(rec, &[motive, base_term, step_term, target])
    }

    // --- declarations -------------------------------------------------------

    /// `def name : Nat → Nat → Nat := fun x y => Nat.rec (fun _ => Nat) (base x) (fun j ih => step x j ih) y`
    ///
    /// i.e. structural recursion on the **second** argument, so
    /// `name x zero ≡ base x` and `name x (succ j) ≡ step x j (name x j)` hold
    /// definitionally (β/δ/ι) and no equation lemmas are needed. `height` is the
    /// [`ReducibilityHint::Regular`] delta height: give a definition a strictly
    /// greater height than every definition it calls.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection if the generated definition does not
    /// type-check or the name is already taken.
    fn define_binary(
        &mut self,
        name: NameId,
        height: u16,
        base: &dyn Fn(&mut Self, ExprId) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId, ExprId) -> ExprId,
    ) -> Result<NameId, KernelError>
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let x_fv = self.fresh_fvar();
        let x = self.kernel().fvar(x_fv);
        let motive = self.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let minor_zero = base(self, x);
        let minor_succ = {
            let j_fv = self.fresh_fvar();
            let j = self.kernel().fvar(j_fv);
            let ih_fv = self.fresh_fvar();
            let ih = self.kernel().fvar(ih_fv);
            let body = step(self, x, j, ih);
            let inner = self.lam_fv(ih_fv, nat, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let y_fv = self.fresh_fvar();
        let y = self.kernel().fvar(y_fv);
        let one = self.level_one();
        let rec_name = self.prelude().rec;
        let rec = self.kernel().const_(rec_name, vec![one]);
        let body = self.apply(rec, &[motive, minor_zero, minor_succ, y]);
        let value = {
            let inner = self.lam_fv(y_fv, nat, body);
            self.lam_fv(x_fv, nat, inner)
        };
        let ty = {
            let inner = self.arrow(nat, nat);
            self.arrow(nat, inner)
        };
        self.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(height),
        })?;
        Ok(name)
    }

    /// Admit `theorem name : ty := value` through the kernel's trusted gate.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection — i.e. the kernel **refused** the proof.
    fn declare_theorem(
        &mut self,
        name: NameId,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    }

    /// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Nat), stmt := fun … => proof`,
    /// where `build` receives the `arity` universally quantified variables and
    /// returns `(statement, proof)`.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection — the kernel re-checks `proof` against
    /// `stmt` inside `add_declaration`, so an `Err` here means the proof was
    /// **rejected**.
    fn try_theorem(
        &mut self,
        name: NameId,
        arity: usize,
        build: &dyn Fn(&mut Self, &[ExprId]) -> (ExprId, ExprId),
    ) -> Result<ExprId, KernelError>
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let fvs: Vec<u64> = (0..arity).map(|_| self.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| self.kernel().fvar(f)).collect();
        let (stmt, proof) = build(self, &vars);
        let mut ty = stmt;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = self.pi_fv(fv, nat, ty);
            value = self.lam_fv(fv, nat, value);
        }
        self.declare_theorem(name, ty, value)?;
        Ok(ty)
    }

    /// [`try_theorem`](Self::try_theorem), returning the declared statement or
    /// the trusted gate's typed rejection.
    ///
    /// # Errors
    ///
    /// Returns the trusted kernel gate's typed rejection.
    fn theorem(
        &mut self,
        name: NameId,
        arity: usize,
        build: &dyn Fn(&mut Self, &[ExprId]) -> (ExprId, ExprId),
    ) -> Result<ExprId, KernelError>
    where
        Self: Sized,
    {
        self.try_theorem(name, arity, build)
    }

    /// A readable rendering of a kernel rejection (the payloads are [`ExprId`]s,
    /// which say nothing on their own).
    fn explain(&mut self, e: &KernelError) -> String {
        match e {
            KernelError::DeclarationValueMismatch { declared, inferred } => {
                let declared = self.kernel().render_lean(*declared);
                let inferred = self.kernel().render_lean(*inferred);
                format!(
                    "DeclarationValueMismatch\n    declared : {declared}\n    inferred : {inferred}"
                )
            }
            KernelError::TypeMismatch { expected, got } => {
                let expected = self.kernel().render_lean(*expected);
                let got = self.kernel().render_lean(*got);
                format!("TypeMismatch\n    expected : {expected}\n    got      : {got}")
            }
            other => format!("{other:?}"),
        }
    }
}

/// A ready-made [`NatOps`] development over a borrowed kernel, for callers with
/// no development struct of their own. [`build_nat_prelude`](super::build_nat_prelude)
/// uses it to prove the prelude's own theorems.
pub struct NatDev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
}

impl<'k> NatDev<'k> {
    /// A development over `kernel` using the already-built `prelude`.
    pub fn new(kernel: &'k mut Kernel, prelude: NatPrelude) -> Self {
        let state = NatState::new(kernel, prelude);
        Self { kernel, state }
    }
}

impl NatOps for NatDev<'_> {
    fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}
