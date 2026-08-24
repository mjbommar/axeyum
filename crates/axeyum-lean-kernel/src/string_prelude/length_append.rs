//! `String.length_append : ∀ s t,
//!     Eq Nat (length (append s t)) (add (length s) (length t))` — the
//! free-monoid-to-`(ℕ, +)` homomorphism, and the one string-prelude theorem
//! that genuinely needs `nat_prelude`'s arithmetic (`Nat.add`, `zero_add`,
//! `succ_add`) rather than just the bare `Nat` inductive in [`LogicPrelude`].
//!
//! # Why this is not part of [`build_string_prelude`](super::build_string_prelude)
//!
//! `length`/`length_nil`/`length_cons` (`length.rs`) need nothing beyond the
//! `Nat` inductive already sitting in [`LogicPrelude`], so they are declared
//! unconditionally by `build_string_prelude` and every existing caller
//! (`word_reconstruct`, `lex_reconstruct`, `regex_reconstruct`) gets them for
//! free. `Nat.add` and its algebraic laws are a separate, larger prelude
//! (`nat_prelude`) that none of those callers build today; forcing it into
//! every string reconstruction would be real, avoidable kernel-checking cost
//! for callers that never touch arithmetic. So this theorem is a deliberate,
//! opt-in composition step: build `nat_prelude::build_nat_prelude` and
//! [`build_string_prelude`](super::build_string_prelude) in the *same*
//! [`Kernel`] (order does not matter; both cache through the shared `Logic`
//! prelude — see `prelude_composition.rs`), then call
//! [`build_string_length_append`].
//!
//! # The proof
//!
//! Induction on `s`, with `t` fixed:
//!
//! - **base** (`s = nil`): `append nil t ≡ t` and `length nil ≡ zero` (ι), so
//!   the goal is `length t = add zero (length t)` — `Eq.symm (zero_add
//!   (length t))`.
//! - **step** (`s = cons h s'`): both sides ι-reduce one layer
//!   (`length (append (cons h s') t) ≡ succ (length (append s' t))`,
//!   `add (length (cons h s')) (length t) ≡ add (succ (length s')) (length t)`,
//!   the latter stuck because `add` recurses on the second argument);
//!   `succ_add` un-sticks it (`add (succ n) m = succ (add n m)`), and chaining
//!   a `succ`-congruence on the induction hypothesis with `Eq.symm succ_add`
//!   closes the step — the same shape as `monoid::prove_append_assoc`'s
//!   `cons`-congruence step, one level up at `Nat.succ`.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError, NatPrelude};

use super::StringPrelude;

/// `length_append`'s interned name, the only thing this composition step
/// produces.
#[derive(Debug, Clone, Copy)]
pub struct StringLengthArithmetic {
    /// `length_append : ∀ (s t : Str),
    ///     Eq Nat (length (append s t)) (add (length s) (length t))`.
    pub length_append: NameId,
}

/// Declare and prove `length_append` in a kernel that already has both
/// `sp` (from [`build_string_prelude`](super::build_string_prelude)) and
/// `nat` (from `nat_prelude::build_nat_prelude`) admitted.
///
/// # Errors
///
/// Returns whatever the trusted declaration gate rejects the proof term
/// with — see [`Kernel::add_declaration`].
pub fn build_string_length_append(
    kernel: &mut Kernel,
    sp: &StringPrelude,
    nat: &NatPrelude,
) -> Result<StringLengthArithmetic, KernelError> {
    let one = sp.one;
    let name = kernel.name_str(sp.str_ind, "length_append");
    let mut dev = Dev::new(kernel, sp, nat, one);
    dev.prove_length_append(name)?;
    Ok(StringLengthArithmetic {
        length_append: name,
    })
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 5_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    sp: &'k StringPrelude,
    nat: NatPrelude,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, sp: &'k StringPrelude, nat: &NatPrelude, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(sp.str_ind, vec![]);
        let nat_ty = k.const_(nat.nat, vec![]);
        Self {
            k,
            sp,
            nat: *nat,
            anon,
            zero,
            one,
            str_ty,
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

    /// `append a b`.
    fn append(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.sp.append, vec![]);
        self.apply(f, &[a, b])
    }

    /// `length s`.
    fn length_of(&mut self, s: ExprId) -> ExprId {
        let f = self.k.const_(self.sp.length, vec![]);
        self.k.app(f, s)
    }

    /// `add x y`.
    fn add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.k.const_(self.nat.add, vec![]);
        self.apply(f, &[x, y])
    }

    fn nat_succ(&mut self, n: ExprId) -> ExprId {
        let s = self.k.const_(self.nat.logic.nat_succ, vec![]);
        self.k.app(s, n)
    }

    /// `Eq.{1} Nat x y`.
    fn eq_nat(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.nat.logic.eq, vec![self.one]);
        let nat_ty = self.nat_ty;
        self.apply(eq, &[nat_ty, x, y])
    }

    /// `Eq.refl.{1} Nat x : Eq Nat x x`.
    fn refl_nat(&mut self, x: ExprId) -> ExprId {
        let refl = self.k.const_(self.nat.logic.eq_refl, vec![self.one]);
        let nat_ty = self.nat_ty;
        self.apply(refl, &[nat_ty, x])
    }

    /// `Eq.symm`-style transport over `Nat`: from `proof : Eq Nat a b` build
    /// `Eq Nat b a`.
    fn eq_symm_nat(&mut self, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let motive = {
            let (x_fv, x) = self.fvar();
            let eq_x_a = self.eq_nat(x, a);
            let eq_a_x = self.eq_nat(a, x);
            let inner = self.k.lam(self.anon, eq_a_x, eq_x_a, BinderInfo::Default);
            let nat_ty = self.nat_ty;
            self.lam_fv(x_fv, nat_ty, inner)
        };
        let base = self.refl_nat(a);
        let rec = self
            .k
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        let nat_ty = self.nat_ty;
        self.apply(rec, &[nat_ty, a, motive, base, b, proof])
    }

    /// `Eq.trans`-style transport over `Nat`: from `h1 : Eq Nat a b` and
    /// `h2 : Eq Nat b c` build `Eq Nat a c`.
    fn eq_trans_nat(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let (z_fv, z) = self.fvar();
            let eq_a_z = self.eq_nat(a, z);
            let eq_b_z = self.eq_nat(b, z);
            let inner = self.k.lam(self.anon, eq_b_z, eq_a_z, BinderInfo::Default);
            let nat_ty = self.nat_ty;
            self.lam_fv(z_fv, nat_ty, inner)
        };
        let rec = self
            .k
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        let nat_ty = self.nat_ty;
        self.apply(rec, &[nat_ty, b, motive, h1, c, h2])
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
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        let nat_ty = self.nat_ty;
        self.apply(rec, &[nat_ty, x, motive, base, y, proof])
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
        let char_ty = self.k.const_(self.sp.char_ind, vec![]);
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
            self.lam_fv(h_fv, char_ty, mid)
        };
        let rec = self.k.const_(self.sp.str_rec, vec![self.zero]);
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

    /// `length_append : ∀ (s t : Str),
    ///     Eq Nat (length (append s t)) (add (length s) (length t))`.
    fn prove_length_append(&mut self, name: NameId) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let (t_fv, t) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let lhs = {
                let inner = d.append(x, t);
                d.length_of(inner)
            };
            let rhs = {
                let lx = d.length_of(x);
                let lt = d.length_of(t);
                d.add(lx, lt)
            };
            d.eq_nat(lhs, rhs)
        };
        let proof = self.induct(
            &goal,
            &|d| {
                // base: Eq Nat (length t) (add zero (length t)), via
                // Eq.symm (zero_add (length t)).
                let lt = d.length_of(t);
                let zero_add = d.nat.zero_add;
                let applied = {
                    let lemma = d.k.const_(zero_add, vec![]);
                    d.k.app(lemma, lt)
                }; // : Eq Nat (add zero (length t)) (length t)
                let nat_zero = d.k.const_(d.nat.logic.nat_zero, vec![]);
                let add_zero_lt = d.add(nat_zero, lt);
                d.eq_symm_nat(add_zero_lt, lt, applied)
            },
            &|d, _h, sp, ih| {
                // ih : Eq Nat (length (append sp t)) (add (length sp) (length t))
                // step1 : Eq Nat (succ (length (append sp t)))
                //                (succ (add (length sp) (length t)))
                let lhs_inner = {
                    let a = d.append(sp, t);
                    d.length_of(a)
                };
                let rhs_inner = {
                    let lsp = d.length_of(sp);
                    let lt = d.length_of(t);
                    d.add(lsp, lt)
                };
                let step1 = d.succ_congr(lhs_inner, rhs_inner, ih);
                // step2 : Eq.symm (succ_add (length sp) (length t))
                //   : Eq Nat (succ (add (length sp) (length t)))
                //            (add (succ (length sp)) (length t))
                let lsp = d.length_of(sp);
                let lt = d.length_of(t);
                let succ_add = {
                    let lemma = d.k.const_(d.nat.succ_add, vec![]);
                    let e = d.k.app(lemma, lsp);
                    d.k.app(e, lt)
                }; // : Eq Nat (add (succ lsp) lt) (succ (add lsp lt))
                let succ_lsp = d.nat_succ(lsp);
                let add_succ_lsp_lt = d.add(succ_lsp, lt);
                let succ_add_lsp_lt = d.nat_succ(rhs_inner);
                let step2 = d.eq_symm_nat(add_succ_lsp_lt, succ_add_lsp_lt, succ_add);
                let a = d.nat_succ(lhs_inner);
                let b = succ_add_lsp_lt;
                let c = add_succ_lsp_lt;
                d.eq_trans_nat(a, b, c, step1, step2)
            },
            s,
        );
        let stmt = goal(self, s);
        let str_ty = self.str_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            self.pi_fv(s_fv, str_ty, over_t)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            self.lam_fv(s_fv, str_ty, over_t)
        };
        self.declare_theorem(name, ty, value)
    }
}
