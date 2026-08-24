//! `Str.substr : Nat → Nat → Str → Str` and `Str.at : Nat → Str → Str` — the
//! SMT-LIB `str.substr`/`str.at` string operations, built directly on
//! `take`/`drop` (`take_drop.rs`) with **no `Nat.min`/`Nat.sub` needed**.
//!
//! # `substr` — offset/length, not offset/end
//!
//! ```text
//! substr ≔ λ (n m : Nat) (s : Str), take m (drop n s)
//! ```
//!
//! matching SMT-LIB's `str.substr s n m` (substring of length `m` starting at
//! offset `n`). Because `take`/`drop` are already **total** (the count simply
//! runs out when the string does — see `take_drop.rs`'s module doc), `substr`
//! inherits totality for free: no side condition, no `Nat.min`/`Nat.sub`
//! needed anywhere below.
//!
//! Three laws fall out without touching `nat_prelude`:
//!
//! - `substr_zero_zero : ∀ s, substr 0 0 s = nil` — closes by `Eq.refl`
//!   alone: `take 0 X` ι-reduces to `nil` regardless of `X` (the zero branch
//!   of `take`'s `Nat.rec` discards its `Str` argument entirely), so this
//!   never even needs to look at `drop 0 s`.
//! - `substr_zero_len : ∀ (n : Nat) (s : Str), substr n 0 s = nil` — the same
//!   fact, generalized over `n`: still closes by `Eq.refl` alone, for exactly
//!   the same reason (`take 0` ignores its argument, so it does not matter
//!   that `drop n s` is stuck for an opaque `n`).
//! - `substr_nil : ∀ (n m : Nat), substr n m nil = nil` — this one is **not**
//!   definitional: with `n`/`m` both free, `drop n nil` and `take m nil` are
//!   each stuck on `Nat.rec` applied to a variable. Two internal case splits
//!   (`drop n nil = nil` and `take m nil = nil`, each a `Nat.rec` cases over
//!   its own count, both branches closing by `Eq.refl` since `Str.rec` on a
//!   literal `nil` target fires unconditionally) chain by congruence and
//!   transitivity into the result.
//!
//! # `Str.at` — the partial operator, made total by convention
//!
//! `str.at s n` in SMT-LIB returns the **empty string** when `n` is out of
//! range (not an error, not `unknown`); a `Char`-valued signature would need
//! a default character to fall back on, and this prelude's `Char` may have
//! **zero constructors** (`num_chars == 0`, exercised by
//! `tests::empty_alphabet_admits`) — there may be *no* character available to
//! default to, so `Nat → Str → Char` is not just a worse signature here, it
//! is sometimes an impossible one. `Nat → Str → Str` (a result of length 0 or
//! 1) has no such problem and is exactly what SMT-LIB specifies.
//!
//! ```text
//! at ≔ λ (n : Nat) (s : Str), take 1 (drop n s)
//! ```
//!
//! (equivalently `substr n 1 s`; defined directly to keep proofs to a single
//! `δ`-unfold). Two theorems:
//!
//! - `at_nil : ∀ n, at n nil = nil` — the out-of-range case at the empty
//!   string, via the same `drop n nil = nil` case split `substr_nil` needs.
//! - `at_cons_zero : ∀ (c : Char) (t : Str), at 0 (cons c t) = cons c nil` —
//!   the in-range case, closing by `Eq.refl` alone (`drop 0` is the identity,
//!   and `take 1 (cons c t)` ι-reduces to `cons c (take 0 t)` which
//!   ι-reduces to `cons c nil` regardless of `t`).
//!
//! The **general** out-of-range convention (`n ≥ length s ⇒ at n s = nil`)
//! is not stated as a theorem here — it would need `Nat.le`/`length`
//! reasoning this module does not have without pulling in more of
//! `nat_prelude` — but it is exercised as a **test**
//! (`at_out_of_range_beyond_length`, `tests.rs`) at a concrete `n` strictly
//! greater than a concrete string's length, and at `n` exactly equal to it,
//! both computed by pure kernel ι-reduction: the same totality `take`/`drop`
//! already give (`take_drop.rs`'s `take_and_drop_iota_compute_on_concrete_strings`
//! test does the analogous thing for `take`/`drop` directly). This is
//! deliberate: CLAUDE.md's rule for a partial/underspecified operator is that
//! its degenerate case must be exercised, not merely asserted convenient —
//! `n = 0` alone would never distinguish "out of range" from "in range at the
//! start", so the test uses `n ≥ length s` with `length s > 0`.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_substr_and_at`] declares into, plus the
/// already-admitted `Str`/`Char`/`take`/`drop` handles its terms are built
/// from.
#[derive(Debug, Clone, Copy)]
pub(super) struct SubstrNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub str_ind: NameId,
    pub str_nil: NameId,
    pub str_cons: NameId,
    pub take: NameId,
    pub drop: NameId,
    pub substr: NameId,
    pub substr_zero_zero: NameId,
    pub substr_zero_len: NameId,
    pub substr_nil: NameId,
    pub at: NameId,
    pub at_nil: NameId,
    pub at_cons_zero: NameId,
}

/// Declare `substr` and `at` as checked definitions over `take`/`drop`, and
/// prove their laws, in dependency order.
pub(super) fn declare_substr_and_at(
    kernel: &mut Kernel,
    // By reference: `SubstrNames` embeds `LogicPrelude` and so exceeds
    // clippy's 256-byte `large_types_passed_by_value` limit, exactly the trap
    // `MonoidNames`/`NatPrelude`/`TakeDropNames` already hit.
    names: &SubstrNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_substr()?;
    dev.prove_substr_zero_zero()?;
    dev.prove_substr_zero_len()?;
    dev.prove_substr_nil()?;
    dev.define_at()?;
    dev.prove_at_nil()?;
    dev.prove_at_cons_zero()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 8_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: SubstrNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    str_ty: ExprId,
    char_ty: ExprId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &SubstrNames, one: LevelId) -> Self {
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

    /// `take n s` — the already-declared constant applied, not inlined.
    fn take_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.take, vec![]);
        self.apply(f, &[count, s])
    }

    /// `drop n s` — the already-declared constant applied, not inlined.
    fn drop_of(&mut self, count: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.drop, vec![]);
        self.apply(f, &[count, s])
    }

    /// `substr n m s` — the declared constant applied, not inlined.
    fn substr_of(&mut self, n_: ExprId, m: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.substr, vec![]);
        self.apply(f, &[n_, m, s])
    }

    /// `at n s` — the declared constant applied, not inlined.
    fn at_of(&mut self, n_: ExprId, s: ExprId) -> ExprId {
        let f = self.k.const_(self.n.at, vec![]);
        self.apply(f, &[n_, s])
    }

    fn nat_zero(&mut self) -> ExprId {
        self.k.const_(self.n.logic.nat_zero, vec![])
    }

    fn nat_succ(&mut self, x: ExprId) -> ExprId {
        let s = self.k.const_(self.n.logic.nat_succ, vec![]);
        self.k.app(s, x)
    }

    fn nat_one(&mut self) -> ExprId {
        let z = self.nat_zero();
        self.nat_succ(z)
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

    /// Congruence in the one-hole context `take m ·`: from
    /// `proof : Eq Str x y` build `Eq Str (take m x) (take m y)`. Mirrors
    /// `take_drop::Dev::cons_congr`.
    fn take_congr(&mut self, m: ExprId, x: ExprId, y: ExprId, proof: ExprId) -> ExprId {
        let take_m_x = self.take_of(m, x);
        let str_ty = self.str_ty;
        let motive = {
            let (z_fv, z) = self.fvar();
            let take_m_z = self.take_of(m, z);
            let conclusion = self.eq(take_m_x, take_m_z);
            let hypothesis = self.eq(x, z);
            let inner = self
                .k
                .lam(self.anon, hypothesis, conclusion, BinderInfo::Default);
            self.lam_fv(z_fv, str_ty, inner)
        };
        let base = self.refl(take_m_x);
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        self.apply(rec, &[str_ty, x, motive, base, y, proof])
    }

    /// `Eq.trans`-style transport over `Str`: from `h1 : Eq Str a b` and
    /// `h2 : Eq Str b c` build `Eq Str a c`. Mirrors
    /// `length_append::Dev::eq_trans_nat`.
    fn eq_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let str_ty = self.str_ty;
        let motive = {
            let (z_fv, z) = self.fvar();
            let eq_a_z = self.eq(a, z);
            let eq_b_z = self.eq(b, z);
            let inner = self.k.lam(self.anon, eq_b_z, eq_a_z, BinderInfo::Default);
            self.lam_fv(z_fv, str_ty, inner)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        self.apply(rec, &[str_ty, b, motive, h1, c, h2])
    }

    /// `Nat.rec.{0} motive minor_zero minor_succ target` — a `Prop`-motive
    /// induction (here always used as a `cases`, discarding `ih`) over
    /// `Nat`, over the bare `Nat` in [`LogicPrelude`]. Mirrors
    /// `take_drop::Dev::induct_nat`.
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

    // --- internal case-split lemmas (not exported by name) -------------------
    //
    // Both close every branch by `Eq.refl` alone: `Str.rec` on a *literal*
    // `nil` target fires unconditionally, so neither branch needs to know
    // anything about the discarded predecessor count.

    /// `∀ n, Eq Str (drop n nil) nil`.
    fn drop_nil_case_split(&mut self, target: ExprId) -> ExprId {
        let goal = |d: &mut Self, x: ExprId| {
            let nil = d.nil();
            let lhs = d.drop_of(x, nil);
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

    /// `∀ m, Eq Str (take m nil) nil`.
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

    // --- substr ---------------------------------------------------------------

    /// `substr : Nat → Nat → Str → Str := λ n m s, take m (drop n s)`.
    fn define_substr(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let nat_ty = self.nat_ty;
        let (n_fv, n_) = self.fvar();
        let (m_fv, m) = self.fvar();
        let (s_fv, s) = self.fvar();
        let dropped = self.drop_of(n_, s);
        let took = self.take_of(m, dropped);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, took);
            let with_m = self.lam_fv(m_fv, nat_ty, with_s);
            self.lam_fv(n_fv, nat_ty, with_m)
        };
        let ty = {
            let str_to_str = self.arrow(str_ty, str_ty);
            let inner = self.arrow(nat_ty, str_to_str);
            self.arrow(nat_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.substr,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `substr_zero_zero : ∀ (s : Str), Eq Str (substr 0 0 s) nil`.
    ///
    /// Closes by `Eq.refl` alone: `take 0 X` ι-reduces to `nil` regardless of
    /// `X`, so `drop 0 s` is never even inspected.
    fn prove_substr_zero_zero(&mut self) -> Result<(), KernelError> {
        let (s_fv, s) = self.fvar();
        let zero_n = self.nat_zero();
        let zero_m = self.nat_zero();
        let lhs = self.substr_of(zero_n, zero_m, s);
        let nil = self.nil();
        let stmt = self.eq(lhs, nil);
        let proof = self.refl(nil);
        let str_ty = self.str_ty;
        let ty = self.pi_fv(s_fv, str_ty, stmt);
        let value = self.lam_fv(s_fv, str_ty, proof);
        let name = self.n.substr_zero_zero;
        self.declare_theorem(name, ty, value)
    }

    /// `substr_zero_len : ∀ (n : Nat) (s : Str), Eq Str (substr n 0 s) nil`.
    ///
    /// Closes by `Eq.refl` alone, for the same reason as `substr_zero_zero`
    /// generalized over `n`: `take 0` discards its `Str` argument, so it does
    /// not matter that `drop n s` is stuck for an opaque `n`.
    fn prove_substr_zero_len(&mut self) -> Result<(), KernelError> {
        let (n_fv, n_) = self.fvar();
        let (s_fv, s) = self.fvar();
        let zero = self.nat_zero();
        let lhs = self.substr_of(n_, zero, s);
        let nil = self.nil();
        let stmt = self.eq(lhs, nil);
        let proof = self.refl(nil);
        let nat_ty = self.nat_ty;
        let str_ty = self.str_ty;
        let ty = {
            let over_s = self.pi_fv(s_fv, str_ty, stmt);
            self.pi_fv(n_fv, nat_ty, over_s)
        };
        let value = {
            let over_s = self.lam_fv(s_fv, str_ty, proof);
            self.lam_fv(n_fv, nat_ty, over_s)
        };
        let name = self.n.substr_zero_len;
        self.declare_theorem(name, ty, value)
    }

    /// `substr_nil : ∀ (n m : Nat), Eq Str (substr n m nil) nil`.
    ///
    /// NOT definitional (both counts free, so `drop n nil` and `take m nil`
    /// are each `Nat.rec`-stuck): chain the two internal case splits by
    /// congruence (`take m ·`) and transitivity.
    fn prove_substr_nil(&mut self) -> Result<(), KernelError> {
        let (n_fv, n_) = self.fvar();
        let (m_fv, m) = self.fvar();
        let nil = self.nil();
        let drop_nil_proof = self.drop_nil_case_split(n_);
        let dropped = self.drop_of(n_, nil);
        let step1 = self.take_congr(m, dropped, nil, drop_nil_proof);
        let take_nil_proof = self.take_nil_case_split(m);
        let took_dropped = self.take_of(m, dropped);
        let took_nil = self.take_of(m, nil);
        let combined = self.eq_trans(took_dropped, took_nil, nil, step1, take_nil_proof);
        let stmt = {
            let lhs = self.substr_of(n_, m, nil);
            self.eq(lhs, nil)
        };
        let nat_ty = self.nat_ty;
        let ty = {
            let over_m = self.pi_fv(m_fv, nat_ty, stmt);
            self.pi_fv(n_fv, nat_ty, over_m)
        };
        let value = {
            let over_m = self.lam_fv(m_fv, nat_ty, combined);
            self.lam_fv(n_fv, nat_ty, over_m)
        };
        let name = self.n.substr_nil;
        self.declare_theorem(name, ty, value)
    }

    // --- at ---------------------------------------------------------------

    /// `at : Nat → Str → Str := λ n s, take 1 (drop n s)`.
    fn define_at(&mut self) -> Result<(), KernelError> {
        let str_ty = self.str_ty;
        let nat_ty = self.nat_ty;
        let (n_fv, n_) = self.fvar();
        let (s_fv, s) = self.fvar();
        let one = self.nat_one();
        let dropped = self.drop_of(n_, s);
        let took = self.take_of(one, dropped);
        let value = {
            let with_s = self.lam_fv(s_fv, str_ty, took);
            self.lam_fv(n_fv, nat_ty, with_s)
        };
        let ty = {
            let inner = self.arrow(str_ty, str_ty);
            self.arrow(nat_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.at,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    /// `at_nil : ∀ (n : Nat), Eq Str (at n nil) nil` — the out-of-range
    /// convention at the empty string. NOT definitional for a free `n` (same
    /// obstruction as `substr_nil`): built from the `drop n nil = nil` case
    /// split via `take`-congruence; `take 1 nil` then ι-reduces to `nil`.
    fn prove_at_nil(&mut self) -> Result<(), KernelError> {
        let (n_fv, n_) = self.fvar();
        let one = self.nat_one();
        let nil = self.nil();
        let drop_nil_proof = self.drop_nil_case_split(n_);
        let dropped = self.drop_of(n_, nil);
        let congr = self.take_congr(one, dropped, nil, drop_nil_proof);
        let stmt = {
            let lhs = self.at_of(n_, nil);
            self.eq(lhs, nil)
        };
        let nat_ty = self.nat_ty;
        let ty = self.pi_fv(n_fv, nat_ty, stmt);
        let value = self.lam_fv(n_fv, nat_ty, congr);
        let name = self.n.at_nil;
        self.declare_theorem(name, ty, value)
    }

    /// `at_cons_zero : ∀ (c : Char) (t : Str), Eq Str (at 0 (cons c t)) (cons c nil)`.
    ///
    /// Closes by `Eq.refl` alone: `drop 0` is the identity, and
    /// `take 1 (cons c t)` ι-reduces to `cons c (take 0 t)`, which
    /// ι-reduces to `cons c nil` regardless of `t`.
    fn prove_at_cons_zero(&mut self) -> Result<(), KernelError> {
        let (c_fv, c) = self.fvar();
        let (t_fv, t) = self.fvar();
        let zero = self.nat_zero();
        let consed = self.cons(c, t);
        let lhs = self.at_of(zero, consed);
        let nil = self.nil();
        let rhs = self.cons(c, nil);
        let stmt = self.eq(lhs, rhs);
        let proof = self.refl(rhs);
        let char_ty = self.char_ty;
        let str_ty = self.str_ty;
        let ty = {
            let over_t = self.pi_fv(t_fv, str_ty, stmt);
            self.pi_fv(c_fv, char_ty, over_t)
        };
        let value = {
            let over_t = self.lam_fv(t_fv, str_ty, proof);
            self.lam_fv(c_fv, char_ty, over_t)
        };
        let name = self.n.at_cons_zero;
        self.declare_theorem(name, ty, value)
    }
}
