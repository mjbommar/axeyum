//! The **construction** of `ℤ` over the proved `ℕ` development: the inductive
//! carrier and every operation, as checked definitions rather than axioms.
//!
//! `Int` is Lean's own normalized representation — `Int.ofNat n` for `n ≥ 0`
//! and `Int.negSucc n` for `-(n+1)` — so every integer has exactly one
//! representative and `Eq Int` is ordinary propositional equality. That is the
//! whole reason this route is taken over a setoid quotient of `ℕ × ℕ`: a
//! quotient would make `Quot.sound` part of the trusted surface of every
//! integer theorem, which is precisely the assumption this lane exists to
//! remove.
//!
//! Every definition below recurses on constructors, so its defining equations
//! hold **definitionally** (β/δ/ι) and no equation lemmas are needed:
//!
//! | term | value |
//! |---|---|
//! | `Int.zero` | `Int.ofNat 0` |
//! | `Int.one` | `Int.ofNat 1` |
//! | `Int.negOfNat 0` | `Int.ofNat 0` |
//! | `Int.negOfNat (succ k)` | `Int.negSucc k` |
//! | `Int.subNatNat m n` | `Int.ofNat (m-n)` when `n-m ≡ 0`, else `Int.negSucc k` for `n-m ≡ succ k` |
//! | `Int.add (ofNat m) (ofNat n)` | `Int.ofNat (m+n)` |
//! | `Int.add (ofNat m) (negSucc n)` | `Int.subNatNat m (succ n)` |
//! | `Int.add (negSucc m) (ofNat n)` | `Int.subNatNat n (succ m)` |
//! | `Int.add (negSucc m) (negSucc n)` | `Int.negSucc (succ (m+n))` |
//! | `Int.neg (ofNat n)` | `Int.negOfNat n` |
//! | `Int.neg (negSucc m)` | `Int.ofNat (succ m)` |
//! | `Int.mul (ofNat m) (ofNat n)` | `Int.ofNat (m*n)` |
//! | `Int.mul (ofNat m) (negSucc n)` | `Int.negOfNat (m * succ n)` |
//! | `Int.mul (negSucc m) (ofNat n)` | `Int.negOfNat (succ m * n)` |
//! | `Int.mul (negSucc m) (negSucc n)` | `Int.ofNat (succ m * succ n)` |
//! | `Int.le (ofNat m) (ofNat n)` | `Nat.le m n` |
//! | `Int.le (ofNat m) (negSucc n)` | `False` |
//! | `Int.le (negSucc m) (ofNat n)` | `True` |
//! | `Int.le (negSucc m) (negSucc n)` | `Nat.le n m` |
//!
//! `Int.lt` has the same four-case shape over `Nat.lt`.
//!
//! The two mixed `Int.add` cases are deliberately *the same term*, which is why
//! [`add_comm`](super::algebra) needs no argument at all in those branches.

use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Delta height for the leaf integer definitions. Above every `Nat` definition
/// in the environment (the tallest is `Nat.gcd`'s Bézout development at 12), as
/// the reducibility contract requires: a definition must outrank everything it
/// unfolds to.
const LEAF_HEIGHT: u16 = 20;
/// Delta height for definitions that call a leaf one.
const DERIVED_HEIGHT: u16 = 21;

/// Admit the inductive carrier `Int` with its two constructors.
pub(super) fn declare_carrier(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type1 = d.kernel().sort(one);
    // Int.ofNat : Nat → Int, Int.negSucc : Nat → Int.
    let ctor_ty = d.kernel().pi(anon, nat, int_ty, BinderInfo::Default);
    d.kernel().add_inductive(
        p.z,
        &[],
        0,
        type1,
        &[(p.of_nat, ctor_ty), (p.neg_succ, ctor_ty)],
    )
}

/// `def name : Nat → Int` by structural recursion, with `zero_case` for `0` and
/// `succ_case k` for `succ k` (the recursive result is discarded).
fn define_nat_to_int(
    d: &mut IntDev<'_>,
    name: NameId,
    height: u16,
    zero_case: &dyn Fn(&mut IntDev<'_>) -> ExprId,
    succ_case: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
    let minor_zero = zero_case(d);
    let minor_succ = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ih_fv = d.fresh_fvar();
        let body = succ_case(d, k);
        let inner = d.lam_fv(ih_fv, int_ty, body);
        d.lam_fv(k_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, int_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(height),
    })
}

/// Admit the constants and the two normalization helpers `Int.negOfNat` and
/// `Int.subNatNat`.
pub(super) fn declare_normalizers(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();

    // Int.zero := Int.ofNat 0
    {
        let zero = d.zero();
        let value = d.of_nat(zero);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.zero,
            uparams: vec![],
            ty: int_ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }
    // Int.one := Int.ofNat 1
    {
        let one = d.num(1);
        let value = d.of_nat(one);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.one,
            uparams: vec![],
            ty: int_ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }
    // Int.negOfNat 0 ≡ Int.ofNat 0; Int.negOfNat (succ k) ≡ Int.negSucc k
    define_nat_to_int(
        d,
        p.neg_of_nat,
        LEAF_HEIGHT,
        &|d| {
            let zero = d.zero();
            d.of_nat(zero)
        },
        &|d, k| d.neg_succ(k),
    )?;
    // Int.subNatNat m n := Nat.rec (fun _ => Int) (ofNat (m-n)) (fun k _ => negSucc k) (n-m)
    {
        let nat = d.nat_ty();
        let int_ty = d.int_ty();
        let anon = d.anon_name();
        let one = d.level_one();
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
        let minor_zero = {
            let difference = d.sub(m, n);
            d.of_nat(difference)
        };
        let minor_succ = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let ih_fv = d.fresh_fvar();
            let body = d.neg_succ(k);
            let inner = d.lam_fv(ih_fv, int_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let scrutinee = d.sub(n, m);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one]);
        let body = d.apply(rec, &[motive, minor_zero, minor_succ, scrutinee]);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(m_fv, nat, inner)
        };
        let ty = {
            let inner = d.arrow(nat, int_ty);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.sub_nat_nat,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }
    Ok(())
}

/// `def name : Int → Int → carrier` by nested `Int.rec` on both arguments,
/// where `result` is the codomain and `level` its universe.
///
/// The four builders receive the `Nat` field of each constructor.
fn define_binary_int(
    d: &mut IntDev<'_>,
    name: NameId,
    height: u16,
    result: ExprId,
    result_level: crate::level::LevelId,
    of_of: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    of_neg: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    neg_of: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    neg_neg: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let rec_name = d.int().rec;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let outer_motive = d.kernel().lam(anon, int_ty, result, BinderInfo::Default);

    // One inner `Int.rec` on `b`, given the outer constructor's field `m`.
    let inner = |d: &mut IntDev<'_>,
                 m: ExprId,
                 on_of: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
                 on_neg: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId|
     -> ExprId {
        let motive = d.kernel().lam(anon, int_ty, result, BinderInfo::Default);
        let minor_of = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = on_of(d, m, n);
            d.lam_fv(n_fv, nat, body)
        };
        let minor_neg = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = on_neg(d, m, n);
            d.lam_fv(n_fv, nat, body)
        };
        let rec = d.kernel().const_(rec_name, vec![result_level]);
        d.apply(rec, &[motive, minor_of, minor_neg, b])
    };

    let minor_of_nat = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = inner(d, m, of_of, of_neg);
        d.lam_fv(m_fv, nat, body)
    };
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = inner(d, m, neg_of, neg_neg);
        d.lam_fv(m_fv, nat, body)
    };
    let rec = d.kernel().const_(rec_name, vec![result_level]);
    let body = d.apply(rec, &[outer_motive, minor_of_nat, minor_neg_succ, a]);
    let value = {
        let with_b = d.lam_fv(b_fv, int_ty, body);
        d.lam_fv(a_fv, int_ty, with_b)
    };
    let ty = {
        let inner_ty = d.arrow(int_ty, result);
        d.arrow(int_ty, inner_ty)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(height),
    })
}

/// Admit `Int.neg`, `Int.add` and `Int.mul`.
pub(super) fn declare_operations(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let one = d.level_one();

    // Int.neg (ofNat n) ≡ negOfNat n; Int.neg (negSucc m) ≡ ofNat (succ m)
    {
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let motive = d.kernel().lam(anon, int_ty, int_ty, BinderInfo::Default);
        let minor_of = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = d.neg_of_nat(n);
            d.lam_fv(n_fv, nat, body)
        };
        let minor_neg = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let successor = d.succ(m);
            let body = d.of_nat(successor);
            d.lam_fv(m_fv, nat, body)
        };
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor_of, minor_neg, a]);
        let value = d.lam_fv(a_fv, int_ty, body);
        let ty = d.arrow(int_ty, int_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.neg,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
        })?;
    }

    define_binary_int(
        d,
        p.add,
        DERIVED_HEIGHT,
        int_ty,
        one,
        &|d, m, n| {
            let sum = NatOps::add(d, m, n);
            d.of_nat(sum)
        },
        &|d, m, n| {
            let successor = d.succ(n);
            d.sub_nat_nat(m, successor)
        },
        &|d, m, n| {
            let successor = d.succ(m);
            d.sub_nat_nat(n, successor)
        },
        &|d, m, n| {
            let sum = NatOps::add(d, m, n);
            let successor = d.succ(sum);
            d.neg_succ(successor)
        },
    )?;

    define_binary_int(
        d,
        p.mul,
        DERIVED_HEIGHT,
        int_ty,
        one,
        &|d, m, n| {
            let product = NatOps::mul(d, m, n);
            d.of_nat(product)
        },
        &|d, m, n| {
            let successor = d.succ(n);
            let product = NatOps::mul(d, m, successor);
            d.neg_of_nat(product)
        },
        &|d, m, n| {
            let successor = d.succ(m);
            let product = NatOps::mul(d, successor, n);
            d.neg_of_nat(product)
        },
        &|d, m, n| {
            let left = d.succ(m);
            let right = d.succ(n);
            let product = NatOps::mul(d, left, right);
            d.of_nat(product)
        },
    )
}

/// Admit `Int.le` and `Int.lt` as four-case definitions over `Nat.le`/`Nat.lt`.
pub(super) fn declare_order_definitions(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    define_binary_int(
        d,
        p.le,
        LEAF_HEIGHT,
        prop,
        one,
        &|d, m, n| NatOps::le(d, m, n),
        &|d, _m, _n| d.false_ty(),
        &|d, _m, _n| d.true_ty(),
        &|d, m, n| NatOps::le(d, n, m),
    )?;

    define_binary_int(
        d,
        p.lt,
        LEAF_HEIGHT,
        prop,
        one,
        &|d, m, n| NatOps::lt(d, m, n),
        &|d, _m, _n| d.false_ty(),
        &|d, _m, _n| d.true_ty(),
        &|d, m, n| NatOps::lt(d, n, m),
    )
}
