//! `Int.ediv` and `Int.emod` — the Euclidean ("E-rounding") quotient and
//! remainder over the constructed `ℤ`, as checked structural definitions.
//!
//! ## The zero convention, and why it matches Lean 4 core
//!
//! Both operations are **total**: `Int.ediv a 0 = 0` and `Int.emod a 0 = a`.
//! This is not a case bolted on afterward — it falls straight out of the
//! already-proved `ℕ` prelude's own zero convention
//! (`Nat.div_zero : div n zero = zero`, `Nat.mod_zero : mod n zero = n`,
//! `crates/axeyum-lean-kernel/src/nat_prelude/division.rs`), because every
//! branch below is stated in terms of `Nat.div`/`Nat.mod` rather than as a
//! fresh case split on the divisor being zero.
//!
//! This is deliberately the **Euclidean** convention (`0 ≤ emod a b < natAbs b`
//! for `b ≠ 0`), not truncating (`tdiv`/`tmod`) or flooring (`fdiv`/`fmod`)
//! division — matching Lean 4 core's `Int.ediv`/`Int.emod` bit for bit
//! (`Init.Data.Int.DivMod.Basic`, fetched and transcribed 2026-08-22):
//!
//! ```text
//! def ediv : Int → Int → Int
//!   | ofNat m,   ofNat n   => ofNat (m / n)
//!   | ofNat m,   -[n+1]    => -ofNat (m / succ n)
//!   | -[_+1],    0         => 0
//!   | -[m+1],    ofNat (succ n) => -[m / succ n +1]
//!   | -[m+1],    -[n+1]    => ofNat (succ (m / succ n))
//!
//! def emod : Int → Int → Int
//!   | ofNat m,   n => ofNat (m % natAbs n)
//!   | -[m+1],    n => subNatNat (natAbs n) (succ (m % natAbs n))
//! ```
//!
//! (`-[n+1]` is Lean's notation for `Int.negSucc n`.) Choosing anything else
//! here — truncation, say — would make every later reconstruction of an
//! `Int.ediv`/`Int.emod`-shaped SMT-LIB goal (`div`/`mod` are E-rounding in
//! SMT-LIB too) a silent wrong-answer generator against both Lean 4 and the
//! solver's own semantics, which is exactly the failure mode this module's own
//! docs warn against elsewhere in this repository.
//!
//! ## The four-branch shape, and where an internal split is unavoidable
//!
//! Like `Int.add`/`Int.mul`/`Int.le` in [`super::defs`], both operations are
//! declared with [`define_binary_int`] — nested `Int.rec` on `a` then `b`,
//! never on the `Nat` payload itself:
//!
//! | `a` \ `b` | `ofNat n` | `negSucc n` |
//! |---|---|---|
//! | `ofNat m` | `ediv ↦ ofNat (m/n)`, `emod ↦ ofNat (m%n)` | `ediv ↦ negOfNat (m / succ n)`, `emod ↦ ofNat (m % succ n)` |
//! | `negSucc m` | `ediv ↦` *(see below)*, `emod ↦ subNatNat n (succ (m%n))` | `ediv ↦ ofNat (succ (m / succ n))`, `emod ↦ subNatNat (succ n) (succ (m % succ n))` |
//!
//! Lean's own pattern match splits the `negSucc _, ofNat _` row of `ediv`
//! again, into `ofNat 0` and `ofNat (succ n)` — because `Int.ediv (negSucc m) 0`
//! must be `0`, not `negSucc (Nat.div m 0)` (`Nat.div m 0` is `0`, so that
//! would wrongly give `negSucc 0 = -1`). So `ediv`'s `neg_of` branch alone
//! carries an internal `Nat.rec` on `n`: `n = 0 ↦ Int.zero`,
//! `n = succ n' ↦ Int.negSucc (Nat.div m (succ n'))`.
//!
//! `emod`'s matching row needs **no** internal split: `subNatNat n (succ (m%n))`
//! is already correct at `n = 0`, for free — `Nat.mod m 0 = m` collapses it to
//! `subNatNat 0 (succ m) = negSucc m`, i.e. `emod (negSucc m) 0 = negSucc m`,
//! exactly the `emod _ 0 = _` invariant. No proof obligation was dodged here:
//! there is simply nothing to split, because `subNatNat`'s own case split
//! (on its two `Nat` arguments) already covers it.

use super::defs::{DERIVED_HEIGHT, define_binary_int};
use super::ops::{IntDev, Shape, case_split, exists_elim};
use super::sub_nat_nat::by_borrow;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Admit `Int.ediv : Int → Int → Int`, the Euclidean quotient.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_ediv(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let one = d.level_one();
    define_binary_int(
        d,
        p.ediv,
        DERIVED_HEIGHT,
        int_ty,
        one,
        // ofNat m, ofNat n => ofNat (m / n)
        &|d, m, n| {
            let q = NatOps::div(d, m, n);
            d.of_nat(q)
        },
        // ofNat m, negSucc n => negOfNat (m / succ n)
        &|d, m, n| {
            let succ_n = d.succ(n);
            let q = NatOps::div(d, m, succ_n);
            d.neg_of_nat(q)
        },
        // negSucc m, ofNat n => Nat.rec on n: 0 ↦ zero; succ n' ↦ negSucc (m / succ n')
        &|d, m, n| {
            let nat = d.nat_ty();
            let int_ty = d.int_ty();
            let anon = d.anon_name();
            let one = d.level_one();
            let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
            let minor_zero = d.izero();
            let minor_succ = {
                let np_fv = d.fresh_fvar();
                let np = d.kernel().fvar(np_fv);
                let ih_fv = d.fresh_fvar();
                let succ_np = d.succ(np);
                let quotient = NatOps::div(d, m, succ_np);
                let body = d.neg_succ(quotient);
                let inner = d.lam_fv(ih_fv, int_ty, body);
                d.lam_fv(np_fv, nat, inner)
            };
            let rec_name = d.prelude().rec;
            let rec = d.kernel().const_(rec_name, vec![one]);
            d.apply(rec, &[motive, minor_zero, minor_succ, n])
        },
        // negSucc m, negSucc n => ofNat (succ (m / succ n))
        &|d, m, n| {
            let succ_n = d.succ(n);
            let q = NatOps::div(d, m, succ_n);
            let s = d.succ(q);
            d.of_nat(s)
        },
    )
}

/// Admit `Int.emod : Int → Int → Int`, the Euclidean remainder.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let one = d.level_one();
    define_binary_int(
        d,
        p.emod,
        DERIVED_HEIGHT,
        int_ty,
        one,
        // ofNat m, ofNat n => ofNat (m % n)
        &|d, m, n| {
            let r = NatOps::modulo(d, m, n);
            d.of_nat(r)
        },
        // ofNat m, negSucc n => ofNat (m % succ n)
        &|d, m, n| {
            let succ_n = d.succ(n);
            let r = NatOps::modulo(d, m, succ_n);
            d.of_nat(r)
        },
        // negSucc m, ofNat n => subNatNat n (succ (m % n))
        &|d, m, n| {
            let r = NatOps::modulo(d, m, n);
            let sr = d.succ(r);
            d.sub_nat_nat(n, sr)
        },
        // negSucc m, negSucc n => subNatNat (succ n) (succ (m % succ n))
        &|d, m, n| {
            let succ_n = d.succ(n);
            let r = NatOps::modulo(d, m, succ_n);
            let sr = d.succ(r);
            d.sub_nat_nat(succ_n, sr)
        },
    )
}

// ---------------------------------------------------------------------------
// `Int.ediv_add_emod` — the division algorithm as an equation.
// ---------------------------------------------------------------------------
//
// `∀ a b, b * (a / b) + a % b = a`. Proved by `Int.rec` case analysis on both
// `a` and `b` (four branches); within each branch every operation is already
// pinned to a specific `ℕ`-level formula by [`declare_ediv`]/[`declare_emod`]'s
// own `Int.rec` structure, so the branch goal is (up to defeq) a statement
// about `Nat.div`/`Nat.mod`, closed by the same `Nat.div_mod_exec` this
// module's header quoted the semantics from.
//
// Two of the four branches (`negSucc _, ofNat _` and `negSucc _, negSucc _`)
// share one closing argument once their `Int.mul`/`Int.emod` sides are
// unfolded: both reduce to `negOfNat (K * succ q) + subNatNat K (succ r)` for
// `K := succ divisor_pred`, `q := a.natAbs / K`, `r := a.natAbs % K` — see
// [`close_negative_dividend_row`].

/// `Nat.eq (Nat.add (Nat.mul (succ k) (Nat.div dividend (succ k))) (Nat.mod
/// dividend (succ k))) dividend` — the division algorithm at a **positive**
/// divisor given as `succ k`, read straight off `Nat.div_mod_exec`.
fn div_mod_identity_succ(d: &mut IntDev<'_>, k: ExprId, dividend: ExprId) -> ExprId {
    let p = d.int();
    let divisor = d.succ(k);
    let quotient = NatOps::div(d, dividend, divisor);
    let remainder = NatOps::modulo(d, dividend, divisor);
    let witness = d.const_app(p.nat.div_mod_exec, &[k, dividend]);
    let product = NatOps::mul(d, divisor, quotient);
    let reconstructed = NatOps::add(d, product, remainder);
    let equation_ty = d.eq(dividend, reconstructed);
    let bound_ty = NatOps::lt(d, remainder, divisor);
    let equation = d.and_left(equation_ty, bound_ty, witness);
    d.symm(dividend, reconstructed, equation)
}

/// The same identity for an **arbitrary** divisor `n` (zero included), by
/// case-splitting on `n`. At `n = 0` it is `Nat.zero_mul` + `Nat.zero_add` +
/// `Nat.mod_zero`; at `n = succ k` it is [`div_mod_identity_succ`].
fn div_mod_identity_any(d: &mut IntDev<'_>, n: ExprId, dividend: ExprId) -> ExprId {
    let goal = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let quotient = NatOps::div(d, dividend, x);
        let remainder = NatOps::modulo(d, dividend, x);
        let product = NatOps::mul(d, x, quotient);
        let sum = NatOps::add(d, product, remainder);
        d.eq(sum, dividend)
    };
    d.induct(
        &goal,
        &|d| {
            let zero = d.zero();
            let quotient = NatOps::div(d, dividend, zero);
            let remainder = NatOps::modulo(d, dividend, zero);
            let product = NatOps::mul(d, zero, quotient);
            let sum = NatOps::add(d, product, remainder);
            let zero_plus_r = NatOps::add(d, zero, remainder);
            let h1 = {
                let name = d.int().nat.zero_mul;
                d.const_app(name, &[quotient])
            };
            let h1_lift = d.congr(product, zero, h1, &|d, x| NatOps::add(d, x, remainder));
            let h2 = {
                let name = d.int().nat.zero_add;
                d.const_app(name, &[remainder])
            };
            let h3 = {
                let name = d.int().nat.mod_zero;
                d.const_app(name, &[dividend])
            };
            let (_, proof) = d.chain(
                sum,
                &[(zero_plus_r, h1_lift), (remainder, h2), (dividend, h3)],
            );
            proof
        },
        &|d, k, _ih| div_mod_identity_succ(d, k, dividend),
        n,
    )
}

/// `ofNat m, ofNat n` branch: `n*(m/n) + m%n = m`, purely definitional on the
/// `Int` side (`Int.add`/`Int.mul` both compute on two `ofNat`s), so the only
/// content is [`div_mod_identity_any`].
fn row_of_of(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let start = {
        let ofnat_n = d.of_nat(n);
        let q = NatOps::div(d, m, n);
        let ediv_ab = d.of_nat(q);
        let mul = d.imul(ofnat_n, ediv_ab);
        let r = NatOps::modulo(d, m, n);
        let emod_ab = d.of_nat(r);
        d.iadd(mul, emod_ab)
    };
    let nat_id = div_mod_identity_any(d, n, m);
    let sum = {
        let q = NatOps::div(d, m, n);
        let r = NatOps::modulo(d, m, n);
        let product = NatOps::mul(d, n, q);
        NatOps::add(d, product, r)
    };
    let end = d.of_nat(m);
    let step = d.nat_eq_to_int(sum, m, nat_id, &|d, x| d.of_nat(x));
    let (_, chained) = d.ichain(start, &[(end, step)]);
    chained
}

/// `ofNat m, negSucc n` branch: `Int.ediv`/`Int.emod` reduce to `negOfNat q`
/// and `ofNat r` (`q,r` at divisor `succ n`), but `Int.mul (negSucc n)
/// (negOfNat q)` is *stuck* (`negOfNat q` is not a literal constructor), so
/// `mul_neg_succ_neg_of_nat` is genuinely needed here — unlike the two
/// negative-dividend branches below, where the `Int.ediv` result already
/// lands on a literal constructor.
fn row_of_neg(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let succ_n = d.succ(n);
    let q = NatOps::div(d, m, succ_n);
    let r = NatOps::modulo(d, m, succ_n);
    let negsucc_n = d.neg_succ(n);
    let negofnat_q = d.neg_of_nat(q);
    let ofnat_r = d.of_nat(r);
    let mul = d.imul(negsucc_n, negofnat_q);
    let start = d.iadd(mul, ofnat_r);

    let scaled = NatOps::mul(d, succ_n, q);
    let ofnat_scaled = d.of_nat(scaled);
    let mid = d.iadd(ofnat_scaled, ofnat_r);
    let step1 = {
        let h1 = {
            let name = d.int().mul_neg_succ_neg_of_nat;
            d.const_app(name, &[n, q])
        };
        d.icongr(mul, ofnat_scaled, h1, &|d, x| d.iadd(x, ofnat_r))
    };

    let sum = NatOps::add(d, scaled, r);
    let end = d.of_nat(m);
    let step2 = {
        let nat_id = div_mod_identity_succ(d, n, m);
        d.nat_eq_to_int(sum, m, nat_id, &|d, x| d.of_nat(x))
    };

    let (_, chained) = d.ichain(start, &[(mid, step1), (end, step2)]);
    chained
}

/// The permutation identity both negative-dividend branches close on: with
/// `K := succ divisor_pred`, `A := K * (dv/K)`, `r := dv%K`,
///
/// ```text
/// Nat.eq (succ r + K*(succ (dv/K))) (K + succ dv)
/// ```
///
/// `K*(succ q) ≡ A+K` definitionally (`Nat.mul_succ`), and `succ(A+r) ≡
/// A+succ r` definitionally (`Nat.add_succ`), so the only *propositional*
/// content is `Nat.div_mod_exec` (`A+r=dv`, via [`div_mod_identity_succ`])
/// and re-associating/commuting the three summands `{succ r, A, K}` into the
/// order `K + (A + succ r)`.
fn negative_dividend_permutation(d: &mut IntDev<'_>, divisor_pred: ExprId, dv: ExprId) -> ExprId {
    let k = d.succ(divisor_pred);
    let q = NatOps::div(d, dv, k);
    let r = NatOps::modulo(d, dv, k);
    let a = NatOps::mul(d, k, q);
    let succ_r = d.succ(r);
    let succ_dv = d.succ(dv);

    // h1 : A + succ_r = succ dv   (defeq to `succ (A+r) = succ dv`)
    let h1 = {
        let dv_eq = div_mod_identity_succ(d, divisor_pred, dv);
        let a_plus_r = NatOps::add(d, a, r);
        d.congr(a_plus_r, dv, dv_eq, &|d, x| d.succ(x))
    };
    let a_plus_succ_r = NatOps::add(d, a, succ_r);
    // h2 : K + (A+succ_r) = K + succ_dv
    let h2 = d.congr(a_plus_succ_r, succ_dv, h1, &|d, x| NatOps::add(d, k, x));
    let m1 = NatOps::add(d, k, a_plus_succ_r);
    let rhs = NatOps::add(d, k, succ_dv);

    // LHS: succ_r + (A+K) = (succ_r+A)+K = (A+succ_r)+K = K+(A+succ_r).
    let a_plus_k = NatOps::add(d, a, k);
    let lhs = NatOps::add(d, succ_r, a_plus_k);
    let step_a_mid = {
        let succ_r_plus_a = NatOps::add(d, succ_r, a);
        NatOps::add(d, succ_r_plus_a, k)
    };
    let step_a = {
        let name = d.int().nat.add_assoc;
        let fwd = d.const_app(name, &[succ_r, a, k]);
        d.symm(step_a_mid, lhs, fwd)
    };
    let step_b_mid = NatOps::add(d, a_plus_succ_r, k);
    let step_b = {
        let succ_r_plus_a = NatOps::add(d, succ_r, a);
        let h = {
            let name = d.int().nat.add_comm;
            d.const_app(name, &[succ_r, a])
        };
        d.congr(succ_r_plus_a, a_plus_succ_r, h, &|d, x| {
            NatOps::add(d, x, k)
        })
    };
    let step_c = {
        let name = d.int().nat.add_comm;
        d.const_app(name, &[a_plus_succ_r, k])
    };

    let (_, lhs_to_m1) = d.chain(
        lhs,
        &[(step_a_mid, step_a), (step_b_mid, step_b), (m1, step_c)],
    );
    d.trans(lhs, m1, rhs, lhs_to_m1, h2)
}

/// The common tail of `Int.ediv_add_emod`'s `negSucc _, ofNat (succ _)` and
/// `negSucc _, negSucc _` branches: both reduce `Int.mul b (Int.ediv a b)` to
/// `negOfNat (K * succ q)` (by different, but analogous, branches of
/// `Int.mul`'s own definition — `Int.mul (ofNat (succ np)) (negSucc q)` on one
/// side, `Int.mul (negSucc n) (ofNat (succ q))` on the other) and `Int.emod a
/// b` to `subNatNat K (succ r)`, for `K := succ divisor_pred`.
fn close_negative_dividend_row(d: &mut IntDev<'_>, divisor_pred: ExprId, dv: ExprId) -> ExprId {
    let k = d.succ(divisor_pred);
    let q = NatOps::div(d, dv, k);
    let r = NatOps::modulo(d, dv, k);
    let succ_q = d.succ(q);
    let succ_r = d.succ(r);
    let mag = NatOps::mul(d, k, succ_q);

    let negative = d.neg_of_nat(mag);
    let borrowed = d.sub_nat_nat(k, succ_r);
    let start = d.iadd(negative, borrowed);

    let shifted = NatOps::add(d, succ_r, mag);
    let mid = d.sub_nat_nat(k, shifted);
    let step1 = {
        let name = d.int().neg_of_nat_add_sub_nat_nat;
        d.const_app(name, &[mag, k, succ_r])
    };

    let succ_dv = d.succ(dv);
    let reindexed = NatOps::add(d, k, succ_dv);
    let mid2 = d.sub_nat_nat(k, reindexed);
    let step2 = {
        let permuted = negative_dividend_permutation(d, divisor_pred, dv);
        d.nat_eq_to_int(shifted, reindexed, permuted, &|d, x| d.sub_nat_nat(k, x))
    };

    let end = d.neg_succ(dv);
    let step3 = {
        let name = d.int().sub_nat_nat_add_right;
        d.const_app(name, &[k, succ_dv])
    };

    let (_, chained) = d.ichain(start, &[(mid, step1), (mid2, step2), (end, step3)]);
    chained
}

/// `negSucc dv, ofNat n` branch: split `n`. At `n=0`, `Int.ediv`/`Int.mul`
/// collapse to `ofNat 0`/`ofNat 0` and `Int.emod` to `negSucc (dv%0)`, so the
/// whole branch is `Nat.mod_zero` lifted through `negSucc`. At `n=succ np`,
/// [`close_negative_dividend_row`].
fn row_neg_of(d: &mut IntDev<'_>, dv: ExprId, n: ExprId) -> ExprId {
    let goal = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let negsucc_dv = d.neg_succ(dv);
        let ofnat_x = d.of_nat(x);
        let ediv_ab = d.iediv(negsucc_dv, ofnat_x);
        let emod_ab = d.iemod(negsucc_dv, ofnat_x);
        let mul = d.imul(ofnat_x, ediv_ab);
        let sum = d.iadd(mul, emod_ab);
        d.ieq(sum, negsucc_dv)
    };
    d.induct(
        &goal,
        &|d| {
            let zero = d.zero();
            let modded = NatOps::modulo(d, dv, zero);
            let h = {
                let name = d.int().nat.mod_zero;
                d.const_app(name, &[dv])
            };
            d.nat_eq_to_int(modded, dv, h, &|d, x| d.neg_succ(x))
        },
        &|d, np, _ih| close_negative_dividend_row(d, np, dv),
        n,
    )
}

/// `negSucc dv, negSucc n` branch: [`close_negative_dividend_row`] directly —
/// the divisor's magnitude `succ n` is positive by construction, so there is
/// no zero case to split.
fn row_neg_neg(d: &mut IntDev<'_>, dv: ExprId, n: ExprId) -> ExprId {
    close_negative_dividend_row(d, n, dv)
}

/// `Int.ediv_add_emod : ∀ a b, b * (a / b) + a % b = a`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_ediv_add_emod(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ediv_add_emod, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let stmt = {
            let ediv_ab = d.iediv(a, b);
            let emod_ab = d.iemod(a, b);
            let mul = d.imul(b, ediv_ab);
            let sum = d.iadd(mul, emod_ab);
            d.ieq(sum, a)
        };
        let proof = case_split(
            d,
            &[a, b],
            &|d, args| {
                let (a, b) = (args[0], args[1]);
                let ediv_ab = d.iediv(a, b);
                let emod_ab = d.iemod(a, b);
                let mul = d.imul(b, ediv_ab);
                let sum = d.iadd(mul, emod_ab);
                d.ieq(sum, a)
            },
            &|d, branches| {
                let (a_shape, m) = branches[0];
                let (b_shape, n) = branches[1];
                match (a_shape, b_shape) {
                    (Shape::OfNat, Shape::OfNat) => row_of_of(d, m, n),
                    (Shape::OfNat, Shape::NegSucc) => row_of_neg(d, m, n),
                    (Shape::NegSucc, Shape::OfNat) => row_neg_of(d, m, n),
                    (Shape::NegSucc, Shape::NegSucc) => row_neg_neg(d, m, n),
                }
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.emod_nonneg` — the remainder is non-negative whenever the divisor
// isn't zero.
// ---------------------------------------------------------------------------
//
// Three of the four `Int.rec` branches land the remainder on a literal
// `ofNat`, which is unconditionally `≥ 0`; the hypothesis is only load-bearing
// in the fourth (`negSucc _, ofNat _`), where a zero divisor is exactly the
// case `Int.emod (negSucc m) (ofNat 0) = negSucc m`, negative.
//
// Every branch below proves the FULL implication `Not (Eq Int b 0) → 0 ≤
// a%b`, not just the conclusion, and (re-)introduces its own hypothesis
// variable internally. This is not stylistic: the hypothesis has to be bound
// *after* the case split that fixes `b`'s shape (and, for the one branch that
// needs a further `Nat.rec` on the shape's own field, *after* that split
// too), or its stated type keeps referring to the pre-split `b`/`n` and says
// nothing about the concrete value the branch is actually proving over.

/// `Nat.le b a → Int.le Int.zero (Int.subNatNat a b)` — the borrow does not
/// fire when the second argument is at most the first, so the result lands on
/// the non-negative side. Proved by `sub_nat_nat_elim`: the positive case is
/// unconditional (`ofNat i ≥ 0`); the negative case's own hypothesis
/// (`a+(i+1)=b`) contradicts `Nat.le b a` via `le_of_add_le_add_left` and
/// `Nat.not_succ_le_zero`.
fn sub_nat_nat_nonneg_of_le(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hba: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, z: ExprId| {
        let zero = d.izero();
        d.ile(zero, z)
    };
    by_borrow(
        d,
        a,
        b,
        &motive,
        &|d, i, _hi| {
            let name = d.int().nat.zero_le;
            d.const_app(name, &[i])
        },
        &|d, i, hi| {
            // hi : a + succ i = b.  hba : Nat.le b a.
            let succ_i = d.succ(i);
            let sum = NatOps::add(d, a, succ_i);
            let flipped = d.symm(sum, b, hi);
            let hba_sum = d.nat_rewrite(b, sum, flipped, hba, &|d, x| NatOps::le(d, x, a));
            // hba_sum : Nat.le sum a ≡defeq Nat.le (a+succ_i) (a+0).
            let zero = d.zero();
            let contradiction_hyp = {
                let name = d.int().nat.le_of_add_le_add_left;
                d.const_app(name, &[a, succ_i, zero, hba_sum])
            };
            // contradiction_hyp : Nat.le (succ i) zero.
            let false_proof = {
                let name = d.int().nat.not_succ_le_zero;
                let not_succ = d.const_app(name, &[i]);
                d.apply(not_succ, &[contradiction_hyp])
            };
            let zero_int = d.izero();
            let target = d.neg_succ(i);
            let goal_ty = d.ile(zero_int, target);
            d.absurd(goal_ty, false_proof)
        },
    )
}

/// `Int.le Int.zero (Int.subNatNat (succ divisor_pred) (succ (m % succ
/// divisor_pred)))` — the shared closing argument for both branches where a
/// negative-dividend `Int.emod` lands on a `subNatNat`: the remainder is
/// strictly below the (positive) divisor (`Nat.mod_lt`), so the borrow does
/// not fire ([`sub_nat_nat_nonneg_of_le`]).
fn nonneg_subnatnat_mod(d: &mut IntDev<'_>, m: ExprId, divisor_pred: ExprId) -> ExprId {
    let k = d.succ(divisor_pred);
    let r = NatOps::modulo(d, m, k);
    let succ_r = d.succ(r);
    let positive = {
        let zero = d.zero();
        let base = {
            let name = d.int().nat.zero_le;
            d.const_app(name, &[divisor_pred])
        };
        let name = d.int().nat.le_succ_succ;
        d.const_app(name, &[zero, divisor_pred, base])
    };
    let bound = {
        let name = d.int().nat.mod_lt;
        d.const_app(name, &[m, k, positive])
    };
    // bound : Nat.lt r k ≡defeq Nat.le succ_r k.
    sub_nat_nat_nonneg_of_le(d, k, succ_r, bound)
}

/// `ofNat m, ofNat n` branch: `Int.emod` is a literal `ofNat`, unconditionally
/// non-negative; the hypothesis is bound and discarded.
fn row_emod_nonneg_of_of(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let ofnat_n = d.of_nat(n);
    let zero = d.izero();
    let hyp_ty = {
        let eq_ty = d.ieq(ofnat_n, zero);
        d.not(eq_ty)
    };
    let h_fv = d.fresh_fvar();
    let body = {
        let r = NatOps::modulo(d, m, n);
        let name = d.int().nat.zero_le;
        d.const_app(name, &[r])
    };
    d.lam_fv(h_fv, hyp_ty, body)
}

/// `ofNat m, negSucc n` branch: `Int.emod` is again a literal `ofNat`; the
/// hypothesis is trivially true (`negSucc n` is never `Int.zero`) and unused.
fn row_emod_nonneg_of_neg(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let negsucc_n = d.neg_succ(n);
    let zero = d.izero();
    let hyp_ty = {
        let eq_ty = d.ieq(negsucc_n, zero);
        d.not(eq_ty)
    };
    let h_fv = d.fresh_fvar();
    let body = {
        let succ_n = d.succ(n);
        let r = NatOps::modulo(d, m, succ_n);
        let name = d.int().nat.zero_le;
        d.const_app(name, &[r])
    };
    d.lam_fv(h_fv, hyp_ty, body)
}

/// `negSucc m, negSucc n` branch: [`nonneg_subnatnat_mod`] directly — the
/// divisor's magnitude `succ n` is positive by construction, and (as in the
/// row above) the hypothesis is unused.
fn row_emod_nonneg_neg_neg(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let negsucc_n = d.neg_succ(n);
    let zero = d.izero();
    let hyp_ty = {
        let eq_ty = d.ieq(negsucc_n, zero);
        d.not(eq_ty)
    };
    let h_fv = d.fresh_fvar();
    let body = nonneg_subnatnat_mod(d, m, n);
    d.lam_fv(h_fv, hyp_ty, body)
}

/// `negSucc m, ofNat n` branch: the one place a zero divisor is actually
/// possible, so `n` is split again — generalized over `n`, so the hypothesis
/// can be freshly re-bound (with the right type) inside *each* of the two
/// resulting sub-branches, rather than reused from one bound before the
/// split (whose type would still name the pre-split `n`).
///
/// At `n = 0`: `Int.emod (negSucc m) (ofNat 0)` is `negSucc m` — but
/// `ofNat 0` is `Int.zero` by `Eq.refl`, so the (locally rebound) hypothesis
/// applied to that reflexivity proof is already `False`.
/// At `n = succ np`: [`nonneg_subnatnat_mod`].
fn row_emod_nonneg_neg_of(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let full_goal = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let ofnat_x = d.of_nat(x);
        let zero = d.izero();
        let hyp = {
            let eq_ty = d.ieq(ofnat_x, zero);
            d.not(eq_ty)
        };
        let negsucc_m = d.neg_succ(m);
        let emod_ab = d.iemod(negsucc_m, ofnat_x);
        let goal = d.ile(zero, emod_ab);
        d.arrow(hyp, goal)
    };
    d.induct(
        &full_goal,
        &|d| {
            let zero_nat = d.zero();
            let ofnat_zero = d.of_nat(zero_nat);
            let zero_int = d.izero();
            let hyp_ty = {
                let eq_ty = d.ieq(ofnat_zero, zero_int);
                d.not(eq_ty)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq_proof = d.irefl(zero_int);
            let false_proof = d.apply(h, &[eq_proof]);
            let negsucc_m = d.neg_succ(m);
            let emod_ab = d.iemod(negsucc_m, ofnat_zero);
            let target = d.ile(zero_int, emod_ab);
            let body = d.absurd(target, false_proof);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, np, _ih| {
            let succ_np = d.succ(np);
            let ofnat_succ_np = d.of_nat(succ_np);
            let zero_int = d.izero();
            let hyp_ty = {
                let eq_ty = d.ieq(ofnat_succ_np, zero_int);
                d.not(eq_ty)
            };
            let h_fv = d.fresh_fvar();
            let body = nonneg_subnatnat_mod(d, m, np);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    )
}

/// `Int.emod_nonneg : ∀ a b, Not (Eq Int b Int.zero) → Int.le Int.zero
/// (Int.emod a b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_nonneg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_nonneg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let full_stmt_at = |d: &mut IntDev<'_>, aa: ExprId, bb: ExprId| -> ExprId {
            let zero = d.izero();
            let hyp = {
                let eq_ty = d.ieq(bb, zero);
                d.not(eq_ty)
            };
            let emod_ab = d.iemod(aa, bb);
            let goal = d.ile(zero, emod_ab);
            d.arrow(hyp, goal)
        };
        let stmt = full_stmt_at(d, a, b);
        let proof = case_split(
            d,
            &[a, b],
            &|d, args| full_stmt_at(d, args[0], args[1]),
            &|d, branches| {
                let (a_shape, m) = branches[0];
                let (b_shape, n) = branches[1];
                match (a_shape, b_shape) {
                    (Shape::OfNat, Shape::OfNat) => row_emod_nonneg_of_of(d, m, n),
                    (Shape::OfNat, Shape::NegSucc) => row_emod_nonneg_of_neg(d, m, n),
                    (Shape::NegSucc, Shape::OfNat) => row_emod_nonneg_neg_of(d, m, n),
                    (Shape::NegSucc, Shape::NegSucc) => row_emod_nonneg_neg_neg(d, m, n),
                }
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.emod_lt_of_pos` — the remainder is strictly below a positive divisor.
// ---------------------------------------------------------------------------
//
// `0 < b` already pins `b`'s shape down to `ofNat (succ n)` — `Int.lt_dest`
// plus `Nat.zero_add` gets there exactly the way
// [`super::euclid::declare_decomposition`] pins `k` down from `0 < k` — so
// only `a` needs an `Int.rec` case split (two branches, not four).

/// `Int.lt (Int.subNatNat a (succ r)) (Int.ofNat a)` — when the borrow does
/// not fire the result is `ofNat i` with `succ(r)+i=a`, hence `i < a` (since
/// `succ r ≥ 1`); when it fires the result is a `negSucc`, and
/// `Int.lt (negSucc _) (ofNat _)` is `True` outright.
fn sub_nat_nat_lt_ofnat(d: &mut IntDev<'_>, a: ExprId, r: ExprId) -> ExprId {
    let b = d.succ(r);
    let motive = |d: &mut IntDev<'_>, z: ExprId| {
        let ofnat_a = d.of_nat(a);
        d.ilt(z, ofnat_a)
    };
    by_borrow(
        d,
        a,
        b,
        &motive,
        &|d, i, hi| {
            // hi : Eq Nat (b+i) a, with b = succ r.
            let sum = NatOps::add(d, r, i);
            let succ_sum = d.succ(sum);
            let b_plus_i = NatOps::add(d, b, i);
            let shift = {
                let name = d.int().nat.succ_add;
                d.const_app(name, &[r, i])
            };
            // shift : Eq Nat (b+i) (succ (r+i)).
            let hi_symm = d.symm(b_plus_i, a, hi);
            let a_eq = d.trans(a, b_plus_i, succ_sum, hi_symm, shift);
            // a_eq : Eq Nat a (succ (r+i)).

            let i_plus_r = NatOps::add(d, i, r);
            let base = {
                let name = d.int().nat.le_add_right;
                d.const_app(name, &[i, r])
            };
            // base : Nat.le i (i+r).
            let commuted = {
                let name = d.int().nat.add_comm;
                d.const_app(name, &[i, r])
            };
            let base_r_i =
                d.nat_rewrite(i_plus_r, sum, commuted, base, &|d, x| NatOps::le(d, i, x));
            // base_r_i : Nat.le i (r+i).
            let stepped = {
                let name = d.int().nat.le_succ_succ;
                d.const_app(name, &[i, sum, base_r_i])
            };
            // stepped : Nat.le (succ i) (succ (r+i)).
            let succ_i = d.succ(i);
            let a_eq_symm = d.symm(a, succ_sum, a_eq);
            d.nat_rewrite(succ_sum, a, a_eq_symm, stepped, &|d, x| {
                NatOps::le(d, succ_i, x)
            })
            // : Nat.le (succ i) a ≡defeq Nat.lt i a.
        },
        &|d, _i, _hi| d.true_intro(),
    )
}

/// `ofNat m, ofNat (succ n)` branch: `Int.emod` is a literal `ofNat`, and
/// `Nat.mod_lt` is exactly the bound.
fn row_emod_lt_of_pos_of(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let succ_n = d.succ(n);
    let positive = {
        let zero = d.zero();
        let base = {
            let name = d.int().nat.zero_le;
            d.const_app(name, &[n])
        };
        let name = d.int().nat.le_succ_succ;
        d.const_app(name, &[zero, n, base])
    };
    let name = d.int().nat.mod_lt;
    d.const_app(name, &[m, succ_n, positive])
}

/// `negSucc m, ofNat (succ n)` branch: [`sub_nat_nat_lt_ofnat`] directly.
fn row_emod_lt_of_pos_neg(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let succ_n = d.succ(n);
    let r = NatOps::modulo(d, m, succ_n);
    sub_nat_nat_lt_ofnat(d, succ_n, r)
}

/// `Int.emod_lt_of_pos : ∀ a b, Int.lt Int.zero b → Int.lt (Int.emod a b) b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_lt_of_pos(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    d.int_theorem(p.emod_lt_of_pos, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let goal = {
            let emod_ab = d.iemod(a, b);
            d.ilt(emod_ab, b)
        };
        let stmt = d.arrow(pos_ty, goal);

        // `Int.lt_dest 0 b h : ∃ i, b = 0 + ofNat (succ i)`, exactly the
        // shape `Int.euclidean_decomposition` pins its divisor to.
        let dest = d.const_app(p.lt_dest, &[zero, b, h]);
        let shift_body = |d: &mut IntDev<'_>, i: ExprId| {
            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(zero, value);
            d.ieq(b, shifted)
        };
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = shift_body(d, i);
            d.lam_fv(i_fv, nat, body)
        };

        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = shift_body(d, i);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);

            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(zero, value);

            let nat_zero = d.zero();
            let sum_nat = NatOps::add(d, nat_zero, si);
            let zero_add = d.const_app(p.nat.zero_add, &[si]);
            let normalise = d.nat_eq_to_int(sum_nat, si, zero_add, &|d, x| d.of_nat(x));
            let b_eq = d.itrans(b, shifted, value, hi, normalise);

            // With the divisor pinned to `ofNat (succ i)`, `Int.rec` on `a`
            // selects one of the two row builders.
            let branch = case_split(
                d,
                &[a],
                &|d, args| {
                    let emod_ab = d.iemod(args[0], value);
                    d.ilt(emod_ab, value)
                },
                &|d, br| {
                    let field = br[0].1;
                    match br[0].0 {
                        Shape::OfNat => row_emod_lt_of_pos_of(d, field, i),
                        Shape::NegSucc => row_emod_lt_of_pos_neg(d, field, i),
                    }
                },
            );

            let back = d.isymm(b, value, b_eq);
            let transported = d.int_eq_rewrite(value, b, back, branch, &|d, x| {
                let emod_ab = d.iemod(a, x);
                d.ilt(emod_ab, x)
            });
            let with_h = d.lam_fv(hi_fv, hi_ty, transported);
            d.lam_fv(i_fv, nat, with_h)
        };

        let body = exists_elim(d, predicate, goal, dest, minor);
        let proof = d.lam_fv(h_fv, pos_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}
