//! The multiplicative order of a unit mod `n`, and primitive roots.
//!
//! Roadmap item W1-7 (`docs/math-department/00-roadmap.md`), the number
//! theorist's first request (`docs/math-department/01-number-theory.md`): the
//! structure of `(ℤ/n)*`. ADR-1598 records the design.
//!
//! ## Step 0 — what already existed
//!
//! `shape_search` (fresh build, `declarations=2674`, positive control
//! `Nat.Finset.pigeonhole`, landed the same day) reports **ABSENT** for
//! `--name-like primitiveroot`, `--name-like multorder` and `--name-like
//! ordn`; `--name-like order` returns only the `Alg.OrderedRing` family
//! (order in the *relational* sense, unrelated). So nothing here is a
//! re-derivation.
//!
//! Everything this file consumes already existed and is reused rather than
//! rebuilt:
//!
//! - `Int.pow`/`Int.pow_zero`/`Int.pow_succ`/`Int.pow_add`/`Int.pow_mul`
//!   (`defs.rs`, `ring.rs`) — the exponent is a `Nat` and `Int.pow` recurses
//!   on it, so `pow a (succ j) ≡ mul (pow a j) a` is `Eq.refl`.
//! - The `Int.ModEq` family (`modeq.rs`): `modEq_refl`/`symm`/`trans`,
//!   `modEq_pow`, `modEq_mul_general` (unconditional in `n`), `modEq_cancel`,
//!   `mod_eq_dvd`.
//! - `Int.euler_totient_theorem` (`euler_assembly.rs`) — `0 < n` and
//!   `Coprime a (ofNat n)` give `a^φ(n) ≡ 1`, which is what makes the search
//!   for the order BOUNDED.
//! - `Nat.lnp_bounded_search` (`nat_prelude/least_number.rs`) — the bounded
//!   least-element search, WITH its decidability hypothesis, discharged here
//!   by `Int.eq_em` (`Int.ModEq n x y` unfolds to `Eq Int (emod x n)
//!   (emod y n)`, so deciding it IS deciding an `Int` equation).
//! - `Nat.div_mod_exists : ∀ d n, Le one d → ∃ q r, divMod d n q r` with
//!   `divMod d n q r := n = d*q+r ∧ r<d` (`nat_prelude`) — the division
//!   algorithm behind `order_dvd_of_pow_modeq_one`.
//! - `Nat.totient` and `Nat.totient_eq_zero` (`nat_prelude/totient.rs`,
//!   `totient_lemmas.rs`).
//!
//! ## Why a bounded search rather than an abstract group order
//!
//! An abstract `orderOf` over a group structure would need `(ℤ/n)*` as a
//! *carrier*, which needs quotients — `Quot.sound`, the blocker
//! `01-number-theory.md` names and W0-1 has not decided. The whole point of
//! this file is that the elementary material does **not** wait on that
//! decision: `Int.ModEq` is an explicit relation on `ℤ`, and "the least
//! positive `k` with `a^k ≡ 1`" is a statement about naturals that
//! `Nat.lnp_bounded_search` already decides. See ADR-1598.
//!
//! ## What lands here
//!
//! - [`declare_one_pow`] — `Int.one_pow : ∀ k, pow one k = one`. The one
//!   `Int.pow` law this needed that did not exist.
//! - [`declare_is_order`] — the predicate `Int.IsOrder n a k`.
//! - [`declare_pow_modeq_one_of_dvd`] — the forward half of item 3.
//! - [`declare_order_dvd_of_pow_modeq_one`] — the backward half.
//! - [`declare_pow_modeq_one_iff_order_dvd`] — the two packaged as an `Iff`.
//! - [`declare_order_unique`] — two orders of the same unit are equal.
//! - [`declare_order_exists`] — item 1: the order EXISTS for every unit.
//! - [`declare_order_dvd_totient`] — item 2, Lagrange in the concrete case.
//! - [`declare_is_primitive_root`] / [`declare_primitive_root_pow_injective`]
//!   — item 4.
//!
//! What does NOT land here: existence of a primitive root modulo a prime
//! (item 5). The obstruction is measured and recorded in ADR-1598 and in
//! `docs/plan/status/520-primitive-roots.md`.

use super::defs::DERIVED_HEIGHT;
use super::modeq::imodeq;
use super::ops::{IntDev, exists_elim};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// Local term builders.
// ---------------------------------------------------------------------------

/// `Int.IsOrder n a k`.
pub(super) fn is_order(d: &mut IntDev<'_>, n: ExprId, a: ExprId, k: ExprId) -> ExprId {
    let f = d.int().is_order;
    d.const_app(f, &[n, a, k])
}

/// `Int.IsPrimitiveRoot n a` (`n : Nat`, `a : Int`).
fn is_primitive_root(d: &mut IntDev<'_>, n: ExprId, a: ExprId) -> ExprId {
    let f = d.int().is_primitive_root;
    d.const_app(f, &[n, a])
}

/// `ModEq n (pow a k) one` — "`k` is an exponent that kills `a`".
fn kills(d: &mut IntDev<'_>, n: ExprId, a: ExprId, k: ExprId) -> ExprId {
    let pow_ak = d.ipow(a, k);
    let one_i = d.ione();
    imodeq(d, n, pow_ak, one_i)
}

/// The minimality conjunct of [`is_order`]:
/// `∀ j, 0 < j → j < k → Not (ModEq n (pow a j) one)`.
fn minimality(d: &mut IntDev<'_>, n: ExprId, a: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let zero_nat = NatOps::zero(d);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hit = kills(d, n, a, j);
    let miss = d.not(hit);
    let j_lt_k = d.lt(j, k);
    let inner = d.arrow(j_lt_k, miss);
    let j_pos = d.lt(zero_nat, j);
    let with_pos = d.arrow(j_pos, inner);
    d.pi_fv(j_fv, nat, with_pos)
}

/// `Nat.dvd a b` (`b = a * q` for some `q`).
fn ndvd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    NatOps::dvd(d, a, b)
}

/// `Exists Nat pred`.
fn exists_nat(d: &mut IntDev<'_>, pred: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let e = d.kernel().const_(name, vec![one]);
    d.apply(e, &[nat, pred])
}

/// `Exists.intro Nat pred w proof`.
fn exists_intro_nat(d: &mut IntDev<'_>, pred: ExprId, w: ExprId, proof: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(name, vec![one]);
    d.apply(intro, &[nat, pred, w, proof])
}

/// `And.intro p q hp hq`.
fn and_intro(d: &mut IntDev<'_>, p: ExprId, q: ExprId, hp: ExprId, hq: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[p, q, hp, hq])
}

/// `False.rec (fun _ => target) contradiction : target`.
fn ex_falso(d: &mut IntDev<'_>, target: ExprId, contradiction: ExprId) -> ExprId {
    let zero = d.kernel().level_zero();
    let name = d.int().logic.false_rec;
    let rec = d.kernel().const_(name, vec![zero]);
    let false_ty = d.false_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    d.apply(rec, &[motive, contradiction])
}

// ---------------------------------------------------------------------------
// `Int.one_pow`
// ---------------------------------------------------------------------------

/// `Int.one_pow : ∀ (k : Nat), Eq Int (pow one k) one`
///
/// Induction on `k`. `Int.pow` recurses on its `Nat` exponent, so the step is
/// `pow_succ` followed by `mul_one` and the induction hypothesis. The one
/// `Int.pow` law this development needed and did not have — `pow_zero`,
/// `pow_succ`, `pow_add` and `pow_mul` all existed.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_one_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let one_i = d.ione();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let proof = d.induct(
        &|d, x| {
            let lhs = d.ipow(one_i, x);
            d.ieq(lhs, one_i)
        },
        &|d| d.lemma(p.pow_zero, &[one_i]),
        &|d, j, ih| {
            // pow one (succ j) = mul (pow one j) one = pow one j = one.
            let pow_j = d.ipow(one_i, j);
            let succ_j = d.succ(j);
            let pow_succ_j = d.ipow(one_i, succ_j);
            let mul_term = d.imul(pow_j, one_i);
            let step1 = d.lemma(p.pow_succ, &[one_i, j]);
            let step2 = d.lemma(p.mul_one, &[pow_j]);
            let half = d.itrans(pow_succ_j, mul_term, pow_j, step1, step2);
            d.itrans(pow_succ_j, pow_j, one_i, half, ih)
        },
        k,
    );

    let concl = {
        let lhs = d.ipow(one_i, k);
        d.ieq(lhs, one_i)
    };
    let ty = d.pi_fv(k_fv, nat, concl);
    let value = d.lam_fv(k_fv, nat, proof);
    NatOps::declare_theorem(d, p.one_pow, ty, value)
}

// ---------------------------------------------------------------------------
// `Int.IsOrder`
// ---------------------------------------------------------------------------

/// Admit
/// `Int.IsOrder : Int → Int → Nat → Prop :=
///  fun n a k => 0 < k ∧ (ModEq n (pow a k) one ∧
///                        ∀ j, 0 < j → j < k → ¬ ModEq n (pow a j) one)`
///
/// "`k` is *the* multiplicative order of `a` mod `n`": positive, an exponent
/// that kills `a`, and the least such. Stated as a predicate rather than a
/// `Nat`-valued function on purpose — see ADR-1598.
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
pub(super) fn declare_is_order(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let zero_nat = NatOps::zero(d);
    let pos = d.lt(zero_nat, k);
    let hit = kills(d, n, a, k);
    let least = minimality(d, n, a, k);
    let tail = d.and(hit, least);
    let body = d.and(pos, tail);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_a = d.lam_fv(a_fv, int_ty, with_k);
        d.lam_fv(n_fv, int_ty, with_a)
    };
    let ty = {
        let with_k = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        let with_a = d.kernel().pi(anon, int_ty, with_k, BinderInfo::Default);
        d.kernel().pi(anon, int_ty, with_a, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_order,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
    })
}

/// The three projections out of an `IsOrder` witness.
///
/// `IsOrder n a k` is a `Definition` whose body is an `And`, so a witness is
/// *definitionally* an `And` and `And.left`/`And.right` apply directly.
fn order_pos(d: &mut IntDev<'_>, n: ExprId, a: ExprId, k: ExprId, h: ExprId) -> ExprId {
    let zero_nat = NatOps::zero(d);
    let pos = d.lt(zero_nat, k);
    let hit = kills(d, n, a, k);
    let least = minimality(d, n, a, k);
    let tail = d.and(hit, least);
    d.and_left(pos, tail, h)
}

fn order_kills(d: &mut IntDev<'_>, n: ExprId, a: ExprId, k: ExprId, h: ExprId) -> ExprId {
    let zero_nat = NatOps::zero(d);
    let pos = d.lt(zero_nat, k);
    let hit = kills(d, n, a, k);
    let least = minimality(d, n, a, k);
    let tail = d.and(hit, least);
    let rest = d.and_right(pos, tail, h);
    d.and_left(hit, least, rest)
}

fn order_least(d: &mut IntDev<'_>, n: ExprId, a: ExprId, k: ExprId, h: ExprId) -> ExprId {
    let zero_nat = NatOps::zero(d);
    let pos = d.lt(zero_nat, k);
    let hit = kills(d, n, a, k);
    let least = minimality(d, n, a, k);
    let tail = d.and(hit, least);
    let rest = d.and_right(pos, tail, h);
    d.and_right(hit, least, rest)
}

// ---------------------------------------------------------------------------
// Item 3, forward: `k ∣ m → a^m ≡ 1`
// ---------------------------------------------------------------------------

/// `Int.pow_modeq_one_of_dvd : ∀ (n a : Int) (k m : Nat), 0 < n →
/// ModEq n (pow a k) one → Nat.dvd k m → ModEq n (pow a m) one`
///
/// Stated with the bare congruence rather than with `IsOrder`, because
/// minimality plays no role in this direction and the general form is what the
/// primitive-root argument reuses.
///
/// Route: `dvd k m` unpacks to `m = k * q`; `Int.pow_mul` turns `pow a (k*q)`
/// into `pow (pow a k) q`; `Int.modEq_pow` raises `pow a k ≡ 1` to the `q`-th
/// power; [`declare_one_pow`] collapses `pow one q` to `one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_pow_modeq_one_of_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let izero = d.izero();
    let pos_ty = d.ilt(izero, n);
    let pos_fv = d.fresh_fvar();
    let pos = d.kernel().fvar(pos_fv);

    let hit_ty = kills(d, n, a, k);
    let hit_fv = d.fresh_fvar();
    let hit = d.kernel().fvar(hit_fv);

    let dvd_ty = ndvd(d, k, m);
    let dvd_fv = d.fresh_fvar();
    let dvd = d.kernel().fvar(dvd_fv);

    let goal = kills(d, n, a, m);

    // `Nat.dvd k m` is `∃ q, m = k * q`; that predicate as a lambda.
    let dvd_pred = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let prod = d.mul(k, q);
        let body = d.eq(m, prod);
        d.lam_fv(q_fv, nat, body)
    };

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let prod = d.mul(k, q);
        let heq_ty = d.eq(m, prod);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // `ModEq n (pow (pow a k) q) (pow one q)`.
        let pow_ak = d.ipow(a, k);
        let one_i = d.ione();
        let raised = d.lemma(p.mod_eq_pow, &[n, pow_ak, one_i, q, pos, hit]);
        // `pow one q = one`.
        let one_pow = d.lemma(p.one_pow, &[q]);
        let pow_one_q = d.ipow(one_i, q);
        let outer = d.ipow(pow_ak, q);
        let collapsed = d.int_eq_rewrite(pow_one_q, one_i, one_pow, raised, &|d, x| {
            imodeq(d, n, outer, x)
        });
        // `pow a (k*q) = pow (pow a k) q`, used right-to-left.
        let pow_mul = d.lemma(p.pow_mul, &[a, k, q]);
        let pow_a_prod = d.ipow(a, prod);
        let back = d.isymm(pow_a_prod, outer, pow_mul);
        let at_prod = d.int_eq_rewrite(outer, pow_a_prod, back, collapsed, &|d, x| {
            let one_i = d.ione();
            imodeq(d, n, x, one_i)
        });
        // Transport the exponent `k*q` back to `m` along `heq : m = k*q`.
        let back_eq = d.symm(m, prod, heq);
        let at_m = d.nat_rewrite(prod, m, back_eq, at_prod, &|d, x| kills(d, n, a, x));
        let with_heq = d.lam_fv(heq_fv, heq_ty, at_m);
        d.lam_fv(q_fv, nat, with_heq)
    };

    let proof = exists_elim(d, dvd_pred, goal, dvd, minor);

    let value = {
        let b0 = d.lam_fv(dvd_fv, dvd_ty, proof);
        let b1 = d.lam_fv(hit_fv, hit_ty, b0);
        let b2 = d.lam_fv(pos_fv, pos_ty, b1);
        let b3 = d.lam_fv(m_fv, nat, b2);
        let b4 = d.lam_fv(k_fv, nat, b3);
        let b5 = d.lam_fv(a_fv, int_ty, b4);
        d.lam_fv(n_fv, int_ty, b5)
    };
    let ty = {
        let t0 = d.arrow(dvd_ty, goal);
        let t1 = d.arrow(hit_ty, t0);
        let t2 = d.arrow(pos_ty, t1);
        let t3 = d.pi_fv(m_fv, nat, t2);
        let t4 = d.pi_fv(k_fv, nat, t3);
        let t5 = d.pi_fv(a_fv, int_ty, t4);
        d.pi_fv(n_fv, int_ty, t5)
    };
    NatOps::declare_theorem(d, p.pow_modeq_one_of_dvd, ty, value)
}

// ---------------------------------------------------------------------------
// Item 3, backward: `a^m ≡ 1 → k ∣ m`
// ---------------------------------------------------------------------------

/// `Int.order_dvd_of_pow_modeq_one : ∀ (n a : Int) (k m : Nat), 0 < n →
/// IsOrder n a k → ModEq n (pow a m) one → Nat.dvd k m`
///
/// The division algorithm against minimality. `Nat.div_mod_exists k m` (whose
/// `Le one k` hypothesis IS `IsOrder`'s `Lt zero k`, definitionally, since
/// `Nat.lt a b := Le (succ a) b`) gives `m = k*q + r` with `r < k`. Then
/// `pow_add` splits `a^m` as `a^(k*q) · a^r`, [`declare_pow_modeq_one_of_dvd`]
/// kills the first factor, and `Int.one_mul` leaves `a^r ≡ a^m ≡ 1`. If `r`
/// were a successor it would be a positive exponent below `k` that kills `a`,
/// which minimality refutes; so `r = 0` and `q` is the divisibility witness.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_order_dvd_of_pow_modeq_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let izero = d.izero();
    let pos_ty = d.ilt(izero, n);
    let pos_fv = d.fresh_fvar();
    let pos = d.kernel().fvar(pos_fv);

    let ord_ty = is_order(d, n, a, k);
    let ord_fv = d.fresh_fvar();
    let ord = d.kernel().fvar(ord_fv);

    let hm_ty = kills(d, n, a, m);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);

    let goal = ndvd(d, k, m);

    // `fun x => Eq Nat m (mul k x)` — the body of `Nat.dvd k m`.
    let dvd_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let prod = d.mul(k, x);
        let eq = d.eq(m, prod);
        d.lam_fv(x_fv, nat, eq)
    };

    let hk_pos = order_pos(d, n, a, k, ord);
    let hkill = order_kills(d, n, a, k, ord);
    let hleast = order_least(d, n, a, k, ord);

    // `∃ q r, divMod k m q r`.
    let dm = {
        let f = d.int().nat.div_mod_exists;
        d.const_app(f, &[k, m, hk_pos])
    };
    let inner_pred = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let dmr = d.div_mod(k, m, q, r);
        let over_r = d.lam_fv(r_fv, nat, dmr);
        let ex = exists_nat(d, over_r);
        d.lam_fv(q_fv, nat, ex)
    };

    let outer_minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let r_pred = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let dmr = d.div_mod(k, m, q, r);
            d.lam_fv(r_fv, nat, dmr)
        };
        let ex_r_ty = exists_nat(d, r_pred);
        let ex_r_fv = d.fresh_fvar();
        let ex_r = d.kernel().fvar(ex_r_fv);

        let inner_minor = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let hdm_ty = d.div_mod(k, m, q, r);
            let hdm_fv = d.fresh_fvar();
            let hdm = d.kernel().fvar(hdm_fv);

            let kq = d.mul(k, q);
            let sum = d.add(kq, r);
            let left_ty = d.eq(m, sum);
            let right_ty = d.lt(r, k);
            let hme = d.and_left(left_ty, right_ty, hdm);
            let hrk = d.and_right(left_ty, right_ty, hdm);

            // `k ∣ k*q`, witness `q`.
            let hdvd = {
                let pred = {
                    let x_fv = d.fresh_fvar();
                    let x = d.kernel().fvar(x_fv);
                    let prod = d.mul(k, x);
                    let eq = d.eq(kq, prod);
                    d.lam_fv(x_fv, nat, eq)
                };
                let refl = d.refl(kq);
                exists_intro_nat(d, pred, q, refl)
            };
            let hkq = d.lemma(p.pow_modeq_one_of_dvd, &[n, a, k, kq, pos, hkill, hdvd]);

            let one_i = d.ione();
            let pow_ar = d.ipow(a, r);
            let pow_akq = d.ipow(a, kq);
            let refl_r = d.lemma(p.mod_eq_refl, &[n, pow_ar]);
            let prod_me = d.lemma(
                p.mod_eq_mul_general,
                &[n, pow_akq, one_i, pow_ar, pow_ar, hkq, refl_r],
            );
            // `ModEq n (pow_akq * pow_ar) (one * pow_ar)`.
            let lhs_mul = d.imul(pow_akq, pow_ar);
            let rhs_mul = d.imul(one_i, pow_ar);
            let one_mul_pf = d.lemma(p.one_mul, &[pow_ar]);
            let step_a = d.int_eq_rewrite(rhs_mul, pow_ar, one_mul_pf, prod_me, &|d, x| {
                imodeq(d, n, lhs_mul, x)
            });
            // `ModEq n (pow_akq * pow_ar) pow_ar`.
            let pow_a_sum = d.ipow(a, sum);
            let pow_add_pf = d.lemma(p.pow_add, &[a, kq, r]);
            let back = d.isymm(pow_a_sum, lhs_mul, pow_add_pf);
            let step_b = d.int_eq_rewrite(lhs_mul, pow_a_sum, back, step_a, &|d, x| {
                imodeq(d, n, x, pow_ar)
            });
            // `ModEq n (pow a (k*q + r)) pow_ar`; move the exponent to `m`.
            let hme_back = d.symm(m, sum, hme);
            let step_c = d.nat_rewrite(sum, m, hme_back, step_b, &|d, x| {
                let pa = d.ipow(a, x);
                imodeq(d, n, pa, pow_ar)
            });
            // `ModEq n (pow a m) pow_ar`; flip and compose with `hm`.
            let pow_am = d.ipow(a, m);
            let flipped = d.lemma(p.mod_eq_symm, &[n, pow_am, pow_ar, step_c]);
            let hr = d.lemma(p.mod_eq_trans, &[n, pow_ar, pow_am, one_i, flipped, hm]);

            // `r = 0` or `r = succ p`.
            let zero_nat = NatOps::zero(d);
            let dich = {
                let f = d.int().nat.zero_or_succ;
                d.const_app(f, &[r])
            };
            let left_case = d.eq(r, zero_nat);
            let succ_pred = {
                let pv_fv = d.fresh_fvar();
                let pv = d.kernel().fvar(pv_fv);
                let sp = d.succ(pv);
                let eq = d.eq(r, sp);
                d.lam_fv(pv_fv, nat, eq)
            };
            let right_case = exists_nat(d, succ_pred);

            let decided = d.or_elim(
                left_case,
                right_case,
                goal,
                dich,
                &|d, hr0| {
                    // `m = k*q + r` with `r = 0`, i.e. `m = k*q` up to defeq.
                    let motive = d.eq_motive(r, &|d, x| {
                        let s = d.add(kq, x);
                        d.eq(m, s)
                    });
                    let at_zero = d.transport(r, motive, hme, zero_nat, hr0);
                    exists_intro_nat(d, dvd_pred, q, at_zero)
                },
                &|d, hex| {
                    let minor = {
                        let pv_fv = d.fresh_fvar();
                        let pv = d.kernel().fvar(pv_fv);
                        let sp = d.succ(pv);
                        let hrp_ty = d.eq(r, sp);
                        let hrp_fv = d.fresh_fvar();
                        let hrp = d.kernel().fvar(hrp_fv);
                        // `0 < succ pv`, transported back along `r = succ pv`.
                        let pos_succ = d.zero_lt_succ(pv);
                        let back = d.symm(r, sp, hrp);
                        let mot = d.eq_motive(sp, &|d, x| {
                            let z = NatOps::zero(d);
                            d.lt(z, x)
                        });
                        let r_pos = d.transport(sp, mot, pos_succ, r, back);
                        let refuted = d.apply(hleast, &[r, r_pos, hrk]);
                        let contra = d.apply(refuted, &[hr]);
                        let out = ex_falso(d, goal, contra);
                        let with_hrp = d.lam_fv(hrp_fv, hrp_ty, out);
                        d.lam_fv(pv_fv, nat, with_hrp)
                    };
                    exists_elim(d, succ_pred, goal, hex, minor)
                },
            );

            let with_hdm = d.lam_fv(hdm_fv, hdm_ty, decided);
            d.lam_fv(r_fv, nat, with_hdm)
        };

        let elim_r = exists_elim(d, r_pred, goal, ex_r, inner_minor);
        let with_ex = d.lam_fv(ex_r_fv, ex_r_ty, elim_r);
        d.lam_fv(q_fv, nat, with_ex)
    };

    let proof = exists_elim(d, inner_pred, goal, dm, outer_minor);

    let value = {
        let b0 = d.lam_fv(hm_fv, hm_ty, proof);
        let b1 = d.lam_fv(ord_fv, ord_ty, b0);
        let b2 = d.lam_fv(pos_fv, pos_ty, b1);
        let b3 = d.lam_fv(m_fv, nat, b2);
        let b4 = d.lam_fv(k_fv, nat, b3);
        let b5 = d.lam_fv(a_fv, int_ty, b4);
        d.lam_fv(n_fv, int_ty, b5)
    };
    let ty = {
        let t0 = d.arrow(hm_ty, goal);
        let t1 = d.arrow(ord_ty, t0);
        let t2 = d.arrow(pos_ty, t1);
        let t3 = d.pi_fv(m_fv, nat, t2);
        let t4 = d.pi_fv(k_fv, nat, t3);
        let t5 = d.pi_fv(a_fv, int_ty, t4);
        d.pi_fv(n_fv, int_ty, t5)
    };
    NatOps::declare_theorem(d, p.order_dvd_of_pow_modeq_one, ty, value)
}

// ---------------------------------------------------------------------------
// Item 3, packaged
// ---------------------------------------------------------------------------

/// `Int.pow_modeq_one_iff_order_dvd : ∀ (n a : Int) (k m : Nat), 0 < n →
/// IsOrder n a k → Iff (ModEq n (pow a m) one) (Nat.dvd k m)`
///
/// The two halves above as one `Iff` — the form that makes the order usable.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_pow_modeq_one_iff_order_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let izero = d.izero();
    let pos_ty = d.ilt(izero, n);
    let pos_fv = d.fresh_fvar();
    let pos = d.kernel().fvar(pos_fv);

    let ord_ty = is_order(d, n, a, k);
    let ord_fv = d.fresh_fvar();
    let ord = d.kernel().fvar(ord_fv);

    let hit_ty = kills(d, n, a, m);
    let dvd_ty = ndvd(d, k, m);

    let forward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.order_dvd_of_pow_modeq_one, &[n, a, k, m, pos, ord, h]);
        d.lam_fv(h_fv, hit_ty, body)
    };
    let backward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hkill = order_kills(d, n, a, k, ord);
        let body = d.lemma(p.pow_modeq_one_of_dvd, &[n, a, k, m, pos, hkill, h]);
        d.lam_fv(h_fv, dvd_ty, body)
    };
    let iff_intro = d.int().logic.iff_intro;
    let proof = d.const_app(iff_intro, &[hit_ty, dvd_ty, forward, backward]);
    let goal = {
        let iff = d.int().logic.iff;
        d.const_app(iff, &[hit_ty, dvd_ty])
    };

    let value = {
        let b1 = d.lam_fv(ord_fv, ord_ty, proof);
        let b2 = d.lam_fv(pos_fv, pos_ty, b1);
        let b3 = d.lam_fv(m_fv, nat, b2);
        let b4 = d.lam_fv(k_fv, nat, b3);
        let b5 = d.lam_fv(a_fv, int_ty, b4);
        d.lam_fv(n_fv, int_ty, b5)
    };
    let ty = {
        let t1 = d.arrow(ord_ty, goal);
        let t2 = d.arrow(pos_ty, t1);
        let t3 = d.pi_fv(m_fv, nat, t2);
        let t4 = d.pi_fv(k_fv, nat, t3);
        let t5 = d.pi_fv(a_fv, int_ty, t4);
        d.pi_fv(n_fv, int_ty, t5)
    };
    NatOps::declare_theorem(d, p.pow_modeq_one_iff_order_dvd, ty, value)
}

// ---------------------------------------------------------------------------
// Build sequence
// ---------------------------------------------------------------------------

/// Admit every declaration this module owns, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection at the first declaration it refuses.
pub(super) fn declare_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_one_pow(d)?;
    declare_is_order(d)?;
    declare_pow_modeq_one_of_dvd(d)?;
    declare_order_dvd_of_pow_modeq_one(d)?;
    declare_pow_modeq_one_iff_order_dvd(d)?;
    Ok(())
}
