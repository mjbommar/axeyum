//! `Str.substr_append_split : ∀ (n m : Nat) (s : Str),
//!     Eq Str (append (take n s) (substr n m s)) (take (Nat.add n m) s)` — the
//! `take`/`substr` splitting law, tying `substr` to `Nat.add` the way
//! `take_append_drop` ties `take`/`drop` to `append`. Like `length_append`,
//! this needs `nat_prelude`'s arithmetic (`Nat.add`, `zero_add`, `succ_add`)
//! rather than just the bare `Nat` inductive in [`LogicPrelude`], so it is a
//! deliberate, opt-in composition step, NOT part of
//! [`build_string_prelude`](super::build_string_prelude) — see
//! `length_append.rs`'s module doc for why that split is preserved.
//!
//! # The proof
//!
//! Induction on `n`, with `m` fixed throughout (exactly `length_append`'s
//! shape, one level up): `G(x) := ∀ s, Eq Str (append (take x s) (take m
//! (drop x s))) (take (add x m) s)` (`substr n m s` is `δ`-defeq `take m
//! (drop n s)` throughout, so the statement is proved in that unfolded
//! shape and the kernel accepts it against the `substr`-headed type for
//! free).
//!
//! - **base** (`x = 0`): `take 0 s ≡ nil`, `drop 0 s ≡ s` (ι), so the LHS is
//!   defeq `take m s`; `add 0 m = m` is `zero_add`, not definitional (`add`
//!   recurses on its SECOND argument, so `add 0 ·` is stuck on a free `m`),
//!   so the RHS needs a congruence in `take`'s *count* argument
//!   (`take_count_congr`) transporting `Eq.symm (zero_add m)` across it.
//! - **step, `s = nil`**: both `take (n'+1) nil` and `drop (n'+1) nil` ι to
//!   `nil`, so the LHS is defeq `take m nil` — itself `Nat.rec`-stuck for a
//!   free `m`, needing the same internal `take m nil = nil` case split
//!   `substr.rs` uses (duplicated here per this prelude's per-module
//!   convention). The RHS `take (add (n'+1) m) nil` is stuck the same way on
//!   the (opaque) sum `add (n'+1) m`. Both case-split to `nil`, chained by
//!   `Eq.trans`/`Eq.symm`.
//! - **step, `s = cons h t`**: `take`/`drop` each ι one layer (`take (n'+1)
//!   (cons h t) ≡ cons h (take n' t)`, `drop (n'+1) (cons h t) ≡ drop n' t`),
//!   and `append (cons h ·) ·` ι-unfolds, so the LHS is defeq `cons h
//!   (append (take n' t) (take m (drop n' t)))` — exactly the (outer)
//!   induction hypothesis `ih` applied at `t`, lifted through `cons_congr`.
//!   The RHS needs `succ_add` (`add (n'+1) m = succ (add n' m)`) transported
//!   through `take_count_congr`, after which `take (succ (add n' m)) (cons h
//!   t)` ι-reduces (`take_succ_cons`) to `cons h (take (add n' m) t)` — the
//!   same term `cons_congr` produced. `Eq.trans` (with an `Eq.symm` to face
//!   the right way) chains the two.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError, NatPrelude};

use super::StringPrelude;

/// `substr_append_split`'s interned name, the only thing this composition
/// step produces.
#[derive(Debug, Clone, Copy)]
pub struct StringSubstrArithmetic {
    /// `substr_append_split : ∀ (n m : Nat) (s : Str),
    ///     Eq Str (append (take n s) (substr n m s)) (take (add n m) s)`.
    pub substr_append_split: NameId,
}

/// Declare and prove `substr_append_split` in a kernel that already has both
/// `sp` (from [`build_string_prelude`](super::build_string_prelude)) and
/// `nat` (from `nat_prelude::build_nat_prelude`) admitted.
///
/// # Errors
///
/// Returns whatever the trusted declaration gate rejects the proof term
/// with — see [`Kernel::add_declaration`].
pub fn build_string_substr_arithmetic(
    kernel: &mut Kernel,
    sp: &StringPrelude,
    nat: &NatPrelude,
) -> Result<StringSubstrArithmetic, KernelError> {
    let one = sp.one;
    let name = kernel.name_str(sp.str_ind, "substr_append_split");
    let mut dev = Dev::new(kernel, sp, nat, one);
    dev.prove_substr_append_split(name)?;
    Ok(StringSubstrArithmetic {
        substr_append_split: name,
    })
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 9_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    sp: &'k StringPrelude,
    nat: NatPrelude,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, sp: &'k StringPrelude, nat: &NatPrelude, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let str_ty = k.const_(sp.str_ind, vec![]);
        let char_ty = k.const_(sp.char_ind, vec![]);
        let nat_ty = k.const_(nat.nat, vec![]);
        Self {
            k,
            sp,
            nat: *nat,
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

    fn nil(&mut self) -> ExprId {
        self.k.const_(self.sp.str_nil, vec![])
    }

    fn cons(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        let c = self.k.const_(self.sp.str_cons, vec![]);
        self.apply(c, &[head, tail])
    }

    /// `append a b`.
    fn append(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.sp.append, vec![]);
        self.apply(f, &[a, b])
    }

    /// `take n s`.
    fn take_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.sp.take, vec![]);
        self.apply(f, &[count, s])
    }

    /// `drop n s`.
    fn drop_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.sp.drop, vec![]);
        self.apply(f, &[count, s])
    }

    /// `add x y`.
    fn add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.k.const_(self.nat.add, vec![]);
        self.apply(f, &[x, y])
    }

    fn nat_zero(&mut self) -> ExprId {
        self.k.const_(self.nat.logic.nat_zero, vec![])
    }

    fn nat_succ(&mut self, x: ExprId) -> ExprId {
        let s = self.k.const_(self.nat.logic.nat_succ, vec![]);
        self.k.app(s, x)
    }

    /// `Eq.{1} Str x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.nat.logic.eq, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(eq, &[str_ty, x, y])
    }

    /// `Eq.refl.{1} Str x : Eq Str x x`.
    fn refl(&mut self, x: ExprId) -> ExprId {
        let refl = self.k.const_(self.nat.logic.eq_refl, vec![self.one]);
        let str_ty = self.str_ty;
        self.apply(refl, &[str_ty, x])
    }

    /// `Eq.{1} Nat x y`.
    fn eq_nat(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.nat.logic.eq, vec![self.one]);
        let nat_ty = self.nat_ty;
        self.apply(eq, &[nat_ty, x, y])
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
        let base = {
            let refl = self.k.const_(self.nat.logic.eq_refl, vec![self.one]);
            let nat_ty = self.nat_ty;
            self.apply(refl, &[nat_ty, a])
        };
        let rec = self
            .k
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        let nat_ty = self.nat_ty;
        self.apply(rec, &[nat_ty, a, motive, base, b, proof])
    }

    /// `Eq.symm`-style transport over `Str`: from `proof : Eq Str a b` build
    /// `Eq Str b a`.
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
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, a, motive, base, b, proof])
    }

    /// `Eq.trans`-style transport over `Str`: from `h1 : Eq Str a b` and
    /// `h2 : Eq Str b c` build `Eq Str a c`.
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
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        let str_ty = self.str_ty;
        self.apply(rec, &[str_ty, b, motive, h1, c, h2])
    }

    /// Congruence in the one-hole context `take · s` (the `Nat` *count*
    /// argument): from `proof : Eq Nat a b` build `Eq Str (take a s) (take b
    /// s)`.
    fn take_count_congr(&mut self, s: ExprId, a: ExprId, b: ExprId, proof: ExprId) -> ExprId {
        let take_a_s = self.take_of(a, s);
        let nat_ty = self.nat_ty;
        let motive = {
            let (z_fv, z) = self.fvar();
            let take_z_s = self.take_of(z, s);
            let conclusion = self.eq(take_a_s, take_z_s);
            let hypothesis = self.eq_nat(a, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            self.lam_fv(z_fv, nat_ty, inner)
        };
        let base = self.refl(take_a_s);
        let rec = self
            .k
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        self.apply(rec, &[nat_ty, a, motive, base, b, proof])
    }

    /// Congruence in the one-hole context `cons head ·`: from
    /// `proof : Eq Str x y` build `Eq Str (cons head x) (cons head y)`.
    fn cons_congr(&mut self, head: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let cons_x = self.cons(head, x);
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
        let base = self.refl(cons_x);
        let rec = self
            .k
            .const_(self.nat.logic.eq_rec, vec![self.zero, self.one]);
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// `Str.rec.{0} motive minor_nil minor_cons target` — a `Prop`-motive
    /// case split / induction over the free monoid. Mirrors
    /// `take_drop::Dev::induct_str`.
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
        let rec = self.k.const_(self.sp.str_rec, vec![self.zero]);
        self.apply(rec, &[motive_term, nil_term, cons_term, target])
    }

    /// `Nat.rec.{0} motive minor_zero minor_succ target` — a `Prop`-motive
    /// induction over `Nat`. Mirrors `take_drop::Dev::induct_nat`.
    fn induct_nat(
        &mut self,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
        minor_zero: &dyn Fn(&mut Self) -> ExprId,
        minor_succ: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let motive_term = {
            let (n_fv, n_) = self.fvar();
            let body = motive(self, n_);
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
        let rec = self.k.const_(self.nat.logic.nat_rec, vec![self.zero]);
        self.apply(rec, &[motive_term, zero_term, succ_term, target])
    }

    /// `∀ m, Eq Str (take m nil) nil` — mirrors
    /// `substr::Dev::take_nil_case_split`. Duplicated here (rather than
    /// shared) per this prelude's per-module convention.
    fn take_nil_case_split(&mut self, target: ExprId) -> ExprId {
        let goal = |d: &mut Self, x: ExprId| {
            let nil = d.nil();
            let lhs = d.take_of(x, nil);
            d.eq(lhs, nil)
        };
        self.induct_nat(
            &goal,
            &|d| {
                let nil = d.nil();
                d.refl(nil)
            },
            &|d, _np, _ih| {
                let nil = d.nil();
                d.refl(nil)
            },
            target,
        )
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

    /// `substr_append_split : ∀ (n m : Nat) (s : Str),
    ///     Eq Str (append (take n s) (substr n m s)) (take (add n m) s)`.
    ///
    /// Proved in the `take m (drop n s)` unfolding of `substr n m s`
    /// throughout (the two are `δ`-defeq), then stated against the
    /// `substr`-headed type.
    #[allow(clippy::too_many_lines)] // straight-line proof script; see build_string_prelude's same allow.
    fn prove_substr_append_split(&mut self, name: NameId) -> Result<(), KernelError> {
        let nat_ty = self.nat_ty;

        let (m_fv, m) = self.fvar();

        // G(x) := ∀ s, Eq Str (append (take x s) (take m (drop x s))) (take (add x m) s).
        let goal = |d: &mut Self, x: ExprId| {
            let (s_fv, s) = d.fvar();
            let lhs = {
                let t = d.take_of(x, s);
                let dr = d.drop_of(x, s);
                let tm = d.take_of(m, dr);
                d.append(t, tm)
            };
            let sum = d.add(x, m);
            let rhs = d.take_of(sum, s);
            let stmt = d.eq(lhs, rhs);
            let str_ty = d.str_ty;
            d.pi_fv(s_fv, str_ty, stmt)
        };

        let (n_fv, n_) = self.fvar();
        let proof = self.induct_nat(
            &goal,
            &|d| {
                // base: λ s, <Eq Str (take m s) (take (add 0 m) s)>
                //   (LHS `append (take 0 s) (take m (drop 0 s))` is defeq `take m s`).
                let (s_fv, s) = d.fvar();
                let zero = d.nat_zero();
                let sum = d.add(zero, m);
                let zero_add = {
                    let lemma = d.k.const_(d.nat.zero_add, vec![]);
                    d.k.app(lemma, m)
                }; // : Eq Nat (add zero m) m
                let symm = d.eq_symm_nat(sum, m, zero_add); // : Eq Nat m (add zero m)
                let congr = d.take_count_congr(s, m, sum, symm); // : Eq Str (take m s) (take sum s)
                let str_ty = d.str_ty;
                d.lam_fv(s_fv, str_ty, congr)
            },
            &|d, np, ih| {
                // step: λ s, <case split on s> : G(succ np).
                let (s_fv, s) = d.fvar();
                let succ_np = d.nat_succ(np);
                let inner_goal = |d: &mut Self, y: ExprId| {
                    let lhs = {
                        let t = d.take_of(succ_np, y);
                        let dr = d.drop_of(succ_np, y);
                        let tm = d.take_of(m, dr);
                        d.append(t, tm)
                    };
                    let sum = d.add(succ_np, m);
                    let rhs = d.take_of(sum, y);
                    d.eq(lhs, rhs)
                };
                let case_split = d.induct_str(
                    &inner_goal,
                    &|d| {
                        // s = nil: Eq Str (take m nil) (take (add (succ np) m) nil),
                        // each side case-split to `nil` independently.
                        let nil = d.nil();
                        let take_m_nil = d.take_of(m, nil);
                        let sum = d.add(succ_np, m);
                        let take_sum_nil = d.take_of(sum, nil);
                        let lhs_nil = d.take_nil_case_split(m); // Eq Str (take m nil) nil
                        let rhs_nil = d.take_nil_case_split(sum); // Eq Str (take sum nil) nil
                        let rhs_nil_symm = d.eq_symm(take_sum_nil, nil, rhs_nil); // Eq Str nil (take sum nil)
                        d.eq_trans(take_m_nil, nil, take_sum_nil, lhs_nil, rhs_nil_symm)
                    },
                    &|d, h, t, _ih2| {
                        // s = cons h t: ih_t via the OUTER induction hypothesis at t.
                        let ih_t = d.k.app(ih, t);
                        // ih_t : Eq Str (append (take np t) (take m (drop np t)))
                        //               (take (add np m) t)
                        let inner = {
                            let tt = d.take_of(np, t);
                            let dt = d.drop_of(np, t);
                            let tm = d.take_of(m, dt);
                            d.append(tt, tm)
                        };
                        let sum_np = d.add(np, m);
                        let take_sum_np_t = d.take_of(sum_np, t);
                        let a = d.cons_congr(h, inner, take_sum_np_t, ih_t);
                        // a : Eq Str (cons h inner) (cons h (take sum_np t)).

                        // b : Eq Str (take (add (succ np) m) (cons h t))
                        //            (take (succ sum_np) (cons h t))
                        //   — the latter ι-reduces (`take_succ_cons`) to
                        //     `cons h (take sum_np t)`, the same term `a` produced.
                        let succ_add = {
                            let lemma = d.k.const_(d.nat.succ_add, vec![]);
                            let e = d.k.app(lemma, np);
                            d.k.app(e, m)
                        }; // : Eq Nat (add (succ np) m) (succ (add np m))
                        let succ_np_m = d.add(succ_np, m);
                        let succ_sum_np = d.nat_succ(sum_np);
                        let consed = d.cons(h, t);
                        let b = d.take_count_congr(consed, succ_np_m, succ_sum_np, succ_add);

                        let lhs_final = d.cons(h, inner);
                        let mid = d.cons(h, take_sum_np_t);
                        let rhs_final = d.take_of(succ_np_m, consed);
                        let b_symm = d.eq_symm(rhs_final, mid, b);
                        d.eq_trans(lhs_final, mid, rhs_final, a, b_symm)
                    },
                    s,
                );
                let str_ty = d.str_ty;
                d.lam_fv(s_fv, str_ty, case_split)
            },
            n_,
        );

        let stmt = goal(self, n_);
        let ty = {
            let over_m = self.pi_fv(m_fv, nat_ty, stmt);
            self.pi_fv(n_fv, nat_ty, over_m)
        };
        let value = {
            let over_m = self.lam_fv(m_fv, nat_ty, proof);
            self.lam_fv(n_fv, nat_ty, over_m)
        };
        self.declare_theorem(name, ty, value)
    }
}
