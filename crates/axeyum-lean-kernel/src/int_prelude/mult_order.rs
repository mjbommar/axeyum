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
//!   `modEq_pow`, `modEq_mul_general` (the multiplicative congruence that is
//!   unconditional in `n`), and `modEq_cancel`.
//! - [`super::euler_totient::coprime_of_modeq_inverse`], already `pub(super)`
//!   for exactly this reason: it turns a modular inverse into a coprimality
//!   via the Bezout certificate the inverse already carries.
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
// Uniqueness
// ---------------------------------------------------------------------------

/// `Int.order_unique : ∀ (n a : Int) (k k' : Nat), IsOrder n a k →
/// IsOrder n a k' → Eq Nat k k'`
///
/// Each witness's minimality refutes the other being strictly smaller, so
/// trichotomy leaves only equality. Needs no positivity hypothesis: nothing
/// here touches the modulus.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_order_unique(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let h1_ty = is_order(d, n, a, k);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = is_order(d, n, a, k2);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let goal = d.eq(k, k2);

    let pos1 = order_pos(d, n, a, k, h1);
    let kill1 = order_kills(d, n, a, k, h1);
    let least1 = order_least(d, n, a, k, h1);
    let pos2 = order_pos(d, n, a, k2, h2);
    let kill2 = order_kills(d, n, a, k2, h2);
    let least2 = order_least(d, n, a, k2, h2);

    let lt_k_k2 = d.lt(k, k2);
    let le_k2_k = d.le(k2, k);
    let disj = {
        let f = d.int().nat.lt_or_ge;
        d.const_app(f, &[k, k2])
    };

    let proof = d.or_elim(
        lt_k_k2,
        le_k2_k,
        goal,
        disj,
        &|d, hlt| {
            let refuted = d.apply(least2, &[k, pos1, hlt]);
            let contra = d.apply(refuted, &[kill1]);
            ex_falso(d, goal, contra)
        },
        &|d, hle| {
            let lt_k2_k = d.lt(k2, k);
            let eq_k2_k = d.eq(k2, k);
            let disj2 = {
                let f = d.int().nat.lt_or_eq_of_le;
                d.const_app(f, &[k2, k, hle])
            };
            d.or_elim(
                lt_k2_k,
                eq_k2_k,
                goal,
                disj2,
                &|d, hlt2| {
                    let refuted = d.apply(least1, &[k2, pos2, hlt2]);
                    let contra = d.apply(refuted, &[kill2]);
                    ex_falso(d, goal, contra)
                },
                &|d, heq| d.symm(k2, k, heq),
            )
        },
    );

    let value = {
        let b0 = d.lam_fv(h2_fv, h2_ty, proof);
        let b1 = d.lam_fv(h1_fv, h1_ty, b0);
        let b2 = d.lam_fv(k2_fv, nat, b1);
        let b3 = d.lam_fv(k_fv, nat, b2);
        let b4 = d.lam_fv(a_fv, int_ty, b3);
        d.lam_fv(n_fv, int_ty, b4)
    };
    let ty = {
        let t0 = d.arrow(h2_ty, goal);
        let t1 = d.arrow(h1_ty, t0);
        let t2 = d.pi_fv(k2_fv, nat, t1);
        let t3 = d.pi_fv(k_fv, nat, t2);
        let t4 = d.pi_fv(a_fv, int_ty, t3);
        d.pi_fv(n_fv, int_ty, t4)
    };
    NatOps::declare_theorem(d, p.order_unique, ty, value)
}

// ---------------------------------------------------------------------------
// Item 1: the order exists
// ---------------------------------------------------------------------------

/// `Nat.totient n`.
fn totient(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let f = d.int().nat.totient;
    d.const_app(f, &[n])
}

/// `Not p`, spelled through the same `Not` constant the least-number search
/// uses.
fn nnot(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    d.not(q)
}

/// `∀ j, Lt j bound → Not (Q j)` — `least_number.rs`'s `none_below`, rebuilt
/// here because that helper is private to its own module.
fn none_below(d: &mut IntDev<'_>, q: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let lt = d.lt(j, bound);
    let qj = d.apply(q, &[j]);
    let nqj = nnot(d, qj);
    let imp = d.arrow(lt, nqj);
    d.pi_fv(j_fv, nat, imp)
}

/// `fun m => And (Lt m bound) (And (Q m) (NoneBelow Q m))` — `least_number.rs`'s
/// `bounded_pred`, rebuilt for the same reason.
fn bounded_pred(d: &mut IntDev<'_>, q: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let lt = d.lt(m, bound);
    let qm = d.apply(q, &[m]);
    let nb = none_below(d, q, m);
    let core = d.and(qm, nb);
    let body = d.and(lt, core);
    d.lam_fv(m_fv, nat, body)
}

/// `Int.order_exists : ∀ (n : Nat) (a : Int), Nat.lt 0 n →
/// Coprime a (ofNat n) → ∃ k, IsOrder (ofNat n) a k`
///
/// Item 1 of the task. `Nat.lnp_bounded_search` at `Q j := ModEq (ofNat n)
/// (pow a (succ j)) one` and bound `totient n`:
///
/// - The **decidability** hypothesis is `Int.eq_em`. `ModEq n x y` is a
///   `Definition` unfolding to `Eq Int (emod x n) (emod y n)`, so deciding it
///   IS deciding an integer equation — no excluded middle enters.
/// - The **bound** is Euler's theorem. `Int.euler_totient_theorem` gives
///   `a^φ(n) ≡ 1`, and `Nat.totient_eq_zero` makes `φ(n)` a successor once
///   `0 < n`, so the exponent `φ(n)` is `succ pv` for a `pv` strictly below the
///   bound. That is what makes the left ("nothing below the bound works")
///   disjunct impossible.
/// - The search returns `mm`; the order is `succ mm`, which is positive by
///   construction. Its minimality clause is the search's own, re-indexed:
///   a positive `j` below `succ mm` is `succ i` with `i < mm`.
///
/// The `succ`-shift is why `Q` is stated at `succ j` rather than at `j` — the
/// search's `Q 0` would otherwise be the vacuous `a^0 ≡ 1`, which every `a`
/// satisfies, and the search would always return `0`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_order_exists(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let zero_nat = NatOps::zero(d);
    let hn_ty = d.lt(zero_nat, n);
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);

    let big_n = d.of_nat(n);
    let hcop_ty = d.const_app(p.coprime, &[a, big_n]);
    let hcop_fv = d.fresh_fvar();
    let hcop = d.kernel().fvar(hcop_fv);

    let order_pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = is_order(d, big_n, a, k);
        d.lam_fv(k_fv, nat, body)
    };
    let goal = exists_nat(d, order_pred);

    let t = totient(d, n);

    // `Q := fun j => ModEq (ofNat n) (pow a (succ j)) one`.
    let q_fn = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let body = kills(d, big_n, a, sj);
        d.lam_fv(j_fv, nat, body)
    };

    // `∀ j, Or (Q j) (Not (Q j))`, from `Int.eq_em` on the two `emod`s.
    let hdec = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let pow_asj = d.ipow(a, sj);
        let one_i = d.ione();
        let lhs = d.iemod(pow_asj, big_n);
        let rhs = d.iemod(one_i, big_n);
        let body = d.lemma(p.eq_em, &[lhs, rhs]);
        d.lam_fv(j_fv, nat, body)
    };

    // `totient n = 0` or `totient n = succ pv`.
    let t_zero = d.eq(t, zero_nat);
    let t_succ_pred = {
        let pv_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(pv_fv);
        let sp = d.succ(pv);
        let eq = d.eq(t, sp);
        d.lam_fv(pv_fv, nat, eq)
    };
    let t_succ = exists_nat(d, t_succ_pred);
    let t_dich = {
        let f = d.int().nat.zero_or_succ;
        d.const_app(f, &[t])
    };

    let proof = d.or_elim(
        t_zero,
        t_succ,
        goal,
        t_dich,
        &|d, ht0| {
            // `totient n = 0` forces `n = 0`, contradicting `0 < n`.
            let n_zero = d.eq(n, zero_nat);
            let iff_ty = {
                let f = d.int().nat.totient_eq_zero;
                d.const_app(f, &[n])
            };
            let mp = d.const_app(d.int().logic.iff_mp, &[t_zero, n_zero, iff_ty]);
            let hn0 = d.apply(mp, &[ht0]);
            let mot = d.eq_motive(n, &|d, x| {
                let z = NatOps::zero(d);
                d.lt(z, x)
            });
            let bad = d.transport(n, mot, hn, zero_nat, hn0);
            let f = d.int().nat.lt_irrefl;
            let contra = d.const_app(f, &[zero_nat, bad]);
            ex_falso(d, goal, contra)
        },
        &|d, htex| {
            let minor = {
                let pv_fv = d.fresh_fvar();
                let pv = d.kernel().fvar(pv_fv);
                let sp = d.succ(pv);
                let hpv_ty = d.eq(t, sp);
                let hpv_fv = d.fresh_fvar();
                let hpv = d.kernel().fvar(hpv_fv);

                // Euler: `a^φ(n) ≡ 1`, re-indexed at `succ pv`.
                let he = d.const_app(p.euler_totient_theorem, &[n, a, hn, hcop]);
                let hq_pv = d.nat_rewrite(t, sp, hpv, he, &|d, x| kills(d, big_n, a, x));

                // `pv < totient n`, from `pv < succ pv` and `totient n = succ pv`.
                let lt_self = {
                    let f = d.int().nat.lt_succ_self;
                    d.const_app(f, &[pv])
                };
                let back = d.symm(t, sp, hpv);
                let mot = d.eq_motive(sp, &|d, x| d.lt(pv, x));
                let hpv_lt = d.transport(sp, mot, lt_self, t, back);

                let search = {
                    let f = d.int().nat.lnp_bounded_search;
                    d.const_app(f, &[q_fn, hdec, t])
                };
                let none = none_below(d, q_fn, t);
                let found_pred = bounded_pred(d, q_fn, t);
                let found = exists_nat(d, found_pred);

                let decided = d.or_elim(
                    none,
                    found,
                    goal,
                    search,
                    &|d, hnone| {
                        let refuted = d.apply(hnone, &[pv, hpv_lt]);
                        let contra = d.apply(refuted, &[hq_pv]);
                        ex_falso(d, goal, contra)
                    },
                    &|d, hfound| {
                        let inner = {
                            let mm_fv = d.fresh_fvar();
                            let mm = d.kernel().fvar(mm_fv);
                            let lt_mm = d.lt(mm, t);
                            let q_mm = d.apply(q_fn, &[mm]);
                            let nb_mm = none_below(d, q_fn, mm);
                            let core = d.and(q_mm, nb_mm);
                            let hw_ty = d.and(lt_mm, core);
                            let hw_fv = d.fresh_fvar();
                            let hw = d.kernel().fvar(hw_fv);

                            let rest = d.and_right(lt_mm, core, hw);
                            let h_q = d.and_left(q_mm, nb_mm, rest);
                            let h_nb = d.and_right(q_mm, nb_mm, rest);

                            let k = d.succ(mm);
                            let k_pos = d.zero_lt_succ(mm);

                            // Minimality at `succ mm`.
                            let least = {
                                let j_fv = d.fresh_fvar();
                                let j = d.kernel().fvar(j_fv);
                                let j_pos_ty = d.lt(zero_nat, j);
                                let j_pos_fv = d.fresh_fvar();
                                let j_pos = d.kernel().fvar(j_pos_fv);
                                let j_lt_ty = d.lt(j, k);
                                let j_lt_fv = d.fresh_fvar();
                                let j_lt = d.kernel().fvar(j_lt_fv);
                                let target = {
                                    let hit = kills(d, big_n, a, j);
                                    nnot(d, hit)
                                };

                                let j_zero = d.eq(j, zero_nat);
                                let j_succ_pred = {
                                    let i_fv = d.fresh_fvar();
                                    let i = d.kernel().fvar(i_fv);
                                    let si = d.succ(i);
                                    let eq = d.eq(j, si);
                                    d.lam_fv(i_fv, nat, eq)
                                };
                                let j_succ = exists_nat(d, j_succ_pred);
                                let j_dich = {
                                    let f = d.int().nat.zero_or_succ;
                                    d.const_app(f, &[j])
                                };
                                let body = d.or_elim(
                                    j_zero,
                                    j_succ,
                                    target,
                                    j_dich,
                                    &|d, hj0| {
                                        let mot = d.eq_motive(j, &|d, x| {
                                            let z = NatOps::zero(d);
                                            d.lt(z, x)
                                        });
                                        let bad = d.transport(j, mot, j_pos, zero_nat, hj0);
                                        let f = d.int().nat.lt_irrefl;
                                        let contra = d.const_app(f, &[zero_nat, bad]);
                                        ex_falso(d, target, contra)
                                    },
                                    &|d, hjex| {
                                        let m2 = {
                                            let i_fv = d.fresh_fvar();
                                            let i = d.kernel().fvar(i_fv);
                                            let si = d.succ(i);
                                            let hji_ty = d.eq(j, si);
                                            let hji_fv = d.fresh_fvar();
                                            let hji = d.kernel().fvar(hji_fv);

                                            // `j < succ mm` at `j = succ i`
                                            // gives `succ i < succ mm`, hence
                                            // `i < mm`.
                                            let mot = d.eq_motive(j, &|d, x| d.lt(x, k));
                                            let si_lt = d.transport(j, mot, j_lt, si, hji);
                                            let f = d.int().nat.le_of_succ_le_succ;
                                            let i_lt_mm = d.const_app(f, &[si, mm, si_lt]);
                                            let not_q_i = d.apply(h_nb, &[i, i_lt_mm]);
                                            // `Not (Q i)` is `Not (kills … (succ i))`;
                                            // move it back to `j`.
                                            let back = d.symm(j, si, hji);
                                            let out =
                                                d.nat_rewrite(si, j, back, not_q_i, &|d, x| {
                                                    let hit = kills(d, big_n, a, x);
                                                    nnot(d, hit)
                                                });
                                            let with_h = d.lam_fv(hji_fv, hji_ty, out);
                                            d.lam_fv(i_fv, nat, with_h)
                                        };
                                        exists_elim(d, j_succ_pred, target, hjex, m2)
                                    },
                                );
                                let b0 = d.lam_fv(j_lt_fv, j_lt_ty, body);
                                let b1 = d.lam_fv(j_pos_fv, j_pos_ty, b0);
                                d.lam_fv(j_fv, nat, b1)
                            };

                            let hit_k = kills(d, big_n, a, k);
                            let least_ty = minimality(d, big_n, a, k);
                            let tail = and_intro(d, hit_k, least_ty, h_q, least);
                            let pos_ty = d.lt(zero_nat, k);
                            let core2 = d.and(hit_k, least_ty);
                            let witness = and_intro(d, pos_ty, core2, k_pos, tail);
                            let out = exists_intro_nat(d, order_pred, k, witness);
                            let with_hw = d.lam_fv(hw_fv, hw_ty, out);
                            d.lam_fv(mm_fv, nat, with_hw)
                        };
                        exists_elim(d, found_pred, goal, hfound, inner)
                    },
                );

                let with_hpv = d.lam_fv(hpv_fv, hpv_ty, decided);
                d.lam_fv(pv_fv, nat, with_hpv)
            };
            exists_elim(d, t_succ_pred, goal, htex, minor)
        },
    );

    let value = {
        let b0 = d.lam_fv(hcop_fv, hcop_ty, proof);
        let b1 = d.lam_fv(hn_fv, hn_ty, b0);
        let b2 = d.lam_fv(a_fv, int_ty, b1);
        d.lam_fv(n_fv, nat, b2)
    };
    let ty = {
        let t0 = d.arrow(hcop_ty, goal);
        let t1 = d.arrow(hn_ty, t0);
        let t2 = d.pi_fv(a_fv, int_ty, t1);
        d.pi_fv(n_fv, nat, t2)
    };
    NatOps::declare_theorem(d, p.order_exists, ty, value)
}

// ---------------------------------------------------------------------------
// Item 2: the order divides the totient
// ---------------------------------------------------------------------------

/// `Int.order_dvd_totient : ∀ (n : Nat) (a : Int) (k : Nat), Nat.lt 0 n →
/// Coprime a (ofNat n) → IsOrder (ofNat n) a k → Nat.dvd k (totient n)`
///
/// Lagrange's theorem in the concrete case, and a one-liner once
/// [`declare_order_dvd_of_pow_modeq_one`] is in hand: Euler's theorem supplies
/// the killing exponent `φ(n)` and the characterization says the order divides
/// every such exponent.
///
/// `Nat.lt zero n` is passed where `Int.lt zero (ofNat n)` is expected — the
/// two are definitionally the same proposition, exactly as
/// `euler_assembly.rs` already relies on when it feeds this same hypothesis to
/// `Int.modEq_cancel`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_order_dvd_totient(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let zero_nat = NatOps::zero(d);
    let hn_ty = d.lt(zero_nat, n);
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);

    let big_n = d.of_nat(n);
    let hcop_ty = d.const_app(p.coprime, &[a, big_n]);
    let hcop_fv = d.fresh_fvar();
    let hcop = d.kernel().fvar(hcop_fv);

    let hord_ty = is_order(d, big_n, a, k);
    let hord_fv = d.fresh_fvar();
    let hord = d.kernel().fvar(hord_fv);

    let t = totient(d, n);
    let goal = ndvd(d, k, t);

    let euler = d.const_app(p.euler_totient_theorem, &[n, a, hn, hcop]);
    let proof = d.lemma(
        p.order_dvd_of_pow_modeq_one,
        &[big_n, a, k, t, hn, hord, euler],
    );

    let value = {
        let b0 = d.lam_fv(hord_fv, hord_ty, proof);
        let b1 = d.lam_fv(hcop_fv, hcop_ty, b0);
        let b2 = d.lam_fv(hn_fv, hn_ty, b1);
        let b3 = d.lam_fv(k_fv, nat, b2);
        let b4 = d.lam_fv(a_fv, int_ty, b3);
        d.lam_fv(n_fv, nat, b4)
    };
    let ty = {
        let t0 = d.arrow(hord_ty, goal);
        let t1 = d.arrow(hcop_ty, t0);
        let t2 = d.arrow(hn_ty, t1);
        let t3 = d.pi_fv(k_fv, nat, t2);
        let t4 = d.pi_fv(a_fv, int_ty, t3);
        d.pi_fv(n_fv, nat, t4)
    };
    NatOps::declare_theorem(d, p.order_dvd_totient, ty, value)
}

// ---------------------------------------------------------------------------
// Item 4: primitive roots
// ---------------------------------------------------------------------------

/// Admit
/// `Int.IsPrimitiveRoot : Nat → Int → Prop :=
///  fun n a => IsOrder (ofNat n) a (totient n)`
///
/// A unit whose order is exactly `φ(n)` — the largest it can be, by
/// [`declare_order_dvd_totient`].
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
pub(super) fn declare_is_primitive_root(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let big_n = d.of_nat(n);
    let t = totient(d, n);
    let body = is_order(d, big_n, a, t);

    let value = {
        let with_a = d.lam_fv(a_fv, int_ty, body);
        d.lam_fv(n_fv, nat, with_a)
    };
    let ty = {
        let with_a = d.kernel().pi(anon, int_ty, prop, BinderInfo::Default);
        d.kernel().pi(anon, nat, with_a, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_primitive_root,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 2),
    })
}

/// `Int.order_pow_eq_of_le : ∀ (n a : Int) (t i j : Nat), 0 < n →
/// IsOrder n a t → Nat.le i j → Nat.lt j t → ModEq n (pow a i) (pow a j) →
/// Eq Nat i j`
///
/// The one-sided half of "the powers below the order are pairwise
/// incongruent". Writing `j = i + e` and `t = i + f` (both by `Nat.le_dest`):
///
/// - `a^t = a^i · a^f ≡ 1` makes `a^f` an inverse of `a^i` mod `n`, and
///   [`super::euler_totient::coprime_of_modeq_inverse`] turns that inverse into
///   `Coprime (a^i) n`. This is the step that would otherwise need a
///   `Coprime`-is-multiplicative lemma the development does not have — the
///   Bézout certificate is already sitting inside the order relation.
/// - `a^i · 1 ≡ a^i · a^e` then cancels (`Int.modEq_cancel`) to `a^e ≡ 1`, so
///   `t ∣ e` by [`declare_order_dvd_of_pow_modeq_one`].
/// - `e ≤ i + e = j < t`, and a positive divisor is bounded below by nothing
///   smaller than itself (`Nat.le_of_dvd`), so `e = 0` and `j = i + 0 = i`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_order_pow_eq_of_le(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let izero = d.izero();
    let pos_ty = d.ilt(izero, n);
    let pos_fv = d.fresh_fvar();
    let pos = d.kernel().fvar(pos_fv);

    let ord_ty = is_order(d, n, a, t);
    let ord_fv = d.fresh_fvar();
    let ord = d.kernel().fvar(ord_fv);

    let hle_ty = d.le(i, j);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let hjt_ty = d.lt(j, t);
    let hjt_fv = d.fresh_fvar();
    let hjt = d.kernel().fvar(hjt_fv);

    let pow_ai = d.ipow(a, i);
    let pow_aj = d.ipow(a, j);
    let hij_ty = imodeq(d, n, pow_ai, pow_aj);
    let hij_fv = d.fresh_fvar();
    let hij = d.kernel().fvar(hij_fv);

    let goal = d.eq(i, j);

    let hkill = order_kills(d, n, a, t, ord);

    // `i ≤ t`, hence `∃ f, i + f = t`.
    let hit = {
        let f = d.int().nat.lt_of_le_of_lt;
        d.const_app(f, &[i, j, t, hle, hjt])
    };
    let hile = {
        let si = d.succ(i);
        let le_succ = {
            let f = d.int().nat.le_succ;
            d.const_app(f, &[i])
        };
        let f = d.int().nat.le_trans;
        d.const_app(f, &[i, si, t, le_succ, hit])
    };
    let f_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let sum = d.add(i, x);
        let eq = d.eq(sum, t);
        d.lam_fv(x_fv, nat, eq)
    };
    let hex_f = {
        let f = d.int().nat.le_dest;
        d.const_app(f, &[i, t, hile])
    };

    let e_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let sum = d.add(i, x);
        let eq = d.eq(sum, j);
        d.lam_fv(x_fv, nat, eq)
    };
    let hex_e = {
        let f = d.int().nat.le_dest;
        d.const_app(f, &[i, j, hle])
    };

    let outer = {
        let fv_fv = d.fresh_fvar();
        let fexp = d.kernel().fvar(fv_fv);
        let sum_if = d.add(i, fexp);
        let hif_ty = d.eq(sum_if, t);
        let hif_fv = d.fresh_fvar();
        let hif = d.kernel().fvar(hif_fv);

        // `a^i · a^f ≡ 1`, hence `Coprime (a^i) n`.
        let hif_back = d.symm(sum_if, t, hif);
        let at_sum = d.nat_rewrite(t, sum_if, hif_back, hkill, &|d, x| kills(d, n, a, x));
        let pow_af = d.ipow(a, fexp);
        let mul_if = d.imul(pow_ai, pow_af);
        let pow_a_sum_if = d.ipow(a, sum_if);
        let pow_add_if = d.lemma(p.pow_add, &[a, i, fexp]);
        let split = d.int_eq_rewrite(pow_a_sum_if, mul_if, pow_add_if, at_sum, &|d, x| {
            let one_i = d.ione();
            imodeq(d, n, x, one_i)
        });
        let hcop = super::euler_totient::coprime_of_modeq_inverse(d, n, pow_ai, pow_af, pos, split);

        let inner = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let sum_ie = d.add(i, e);
            let hie_ty = d.eq(sum_ie, j);
            let hie_fv = d.fresh_fvar();
            let hie = d.kernel().fvar(hie_fv);

            // `a^i ≡ a^(i+e) = a^i · a^e`.
            let hie_back = d.symm(sum_ie, j, hie);
            let g1 = d.nat_rewrite(j, sum_ie, hie_back, hij, &|d, x| {
                let pax = d.ipow(a, x);
                imodeq(d, n, pow_ai, pax)
            });
            let pow_ae = d.ipow(a, e);
            let mul_ie = d.imul(pow_ai, pow_ae);
            let pow_a_sum_ie = d.ipow(a, sum_ie);
            let pow_add_ie = d.lemma(p.pow_add, &[a, i, e]);
            let g2 = d.int_eq_rewrite(pow_a_sum_ie, mul_ie, pow_add_ie, g1, &|d, x| {
                imodeq(d, n, pow_ai, x)
            });
            // `a^i · 1 ≡ a^i · a^e`.
            let one_i = d.ione();
            let mul_i_one = d.imul(pow_ai, one_i);
            let mul_one_pf = d.lemma(p.mul_one, &[pow_ai]);
            let back = d.isymm(mul_i_one, pow_ai, mul_one_pf);
            let g3 = d.int_eq_rewrite(pow_ai, mul_i_one, back, g2, &|d, x| imodeq(d, n, x, mul_ie));
            let cancelled = d.lemma(p.mod_eq_cancel, &[n, pow_ai, one_i, pow_ae, pos, hcop, g3]);
            let he1 = d.lemma(p.mod_eq_symm, &[n, one_i, pow_ae, cancelled]);
            let hdvd = d.lemma(p.order_dvd_of_pow_modeq_one, &[n, a, t, e, pos, ord, he1]);

            // `e ≤ i + e = j < t`.
            let sum_ei = d.add(e, i);
            let le_ei = {
                let f = d.int().nat.le_add_right;
                d.const_app(f, &[e, i])
            };
            let comm = {
                let f = d.int().nat.add_comm;
                d.const_app(f, &[e, i])
            };
            let mot_comm = d.eq_motive(sum_ei, &|d, x| d.le(e, x));
            let le_ie = d.transport(sum_ei, mot_comm, le_ei, sum_ie, comm);
            let mot_j = d.eq_motive(sum_ie, &|d, x| d.le(e, x));
            let le_ej = d.transport(sum_ie, mot_j, le_ie, j, hie);
            let het = {
                let f = d.int().nat.lt_of_le_of_lt;
                d.const_app(f, &[e, j, t, le_ej, hjt])
            };

            // `t ∣ e` and `e < t` force `e = 0`.
            let zero_nat = NatOps::zero(d);
            let e_zero = d.eq(e, zero_nat);
            let e_succ_pred = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let sc = d.succ(c);
                let eq = d.eq(e, sc);
                d.lam_fv(c_fv, nat, eq)
            };
            let e_succ = exists_nat(d, e_succ_pred);
            let e_dich = {
                let f = d.int().nat.zero_or_succ;
                d.const_app(f, &[e])
            };
            let decided = d.or_elim(
                e_zero,
                e_succ,
                goal,
                e_dich,
                &|d, he0| {
                    // `i + e = j` at `e = 0` is `i + 0 = j`, i.e. `i = j`.
                    let mot = d.eq_motive(e, &|d, x| {
                        let s = d.add(i, x);
                        d.eq(s, j)
                    });
                    d.transport(e, mot, hie, zero_nat, he0)
                },
                &|d, hex| {
                    let m2 = {
                        let c_fv = d.fresh_fvar();
                        let c = d.kernel().fvar(c_fv);
                        let sc = d.succ(c);
                        let hec_ty = d.eq(e, sc);
                        let hec_fv = d.fresh_fvar();
                        let hec = d.kernel().fvar(hec_fv);
                        let pos_succ = d.zero_lt_succ(c);
                        let back = d.symm(e, sc, hec);
                        let mot = d.eq_motive(sc, &|d, x| {
                            let z = NatOps::zero(d);
                            d.lt(z, x)
                        });
                        let e_pos = d.transport(sc, mot, pos_succ, e, back);
                        let hte = {
                            let f = d.int().nat.le_of_dvd;
                            d.const_app(f, &[t, e, e_pos, hdvd])
                        };
                        let bad = {
                            let f = d.int().nat.lt_of_le_of_lt;
                            d.const_app(f, &[t, e, t, hte, het])
                        };
                        let contra = {
                            let f = d.int().nat.lt_irrefl;
                            d.const_app(f, &[t, bad])
                        };
                        let out = ex_falso(d, goal, contra);
                        let with_hec = d.lam_fv(hec_fv, hec_ty, out);
                        d.lam_fv(c_fv, nat, with_hec)
                    };
                    exists_elim(d, e_succ_pred, goal, hex, m2)
                },
            );

            let with_hie = d.lam_fv(hie_fv, hie_ty, decided);
            d.lam_fv(e_fv, nat, with_hie)
        };

        let body = exists_elim(d, e_pred, goal, hex_e, inner);
        let with_hif = d.lam_fv(hif_fv, hif_ty, body);
        d.lam_fv(fv_fv, nat, with_hif)
    };

    let proof = exists_elim(d, f_pred, goal, hex_f, outer);

    let value = {
        let b0 = d.lam_fv(hij_fv, hij_ty, proof);
        let b1 = d.lam_fv(hjt_fv, hjt_ty, b0);
        let b2 = d.lam_fv(hle_fv, hle_ty, b1);
        let b3 = d.lam_fv(ord_fv, ord_ty, b2);
        let b4 = d.lam_fv(pos_fv, pos_ty, b3);
        let b5 = d.lam_fv(j_fv, nat, b4);
        let b6 = d.lam_fv(i_fv, nat, b5);
        let b7 = d.lam_fv(t_fv, nat, b6);
        let b8 = d.lam_fv(a_fv, int_ty, b7);
        d.lam_fv(n_fv, int_ty, b8)
    };
    let ty = {
        let t0 = d.arrow(hij_ty, goal);
        let t1 = d.arrow(hjt_ty, t0);
        let t2 = d.arrow(hle_ty, t1);
        let t3 = d.arrow(ord_ty, t2);
        let t4 = d.arrow(pos_ty, t3);
        let t5 = d.pi_fv(j_fv, nat, t4);
        let t6 = d.pi_fv(i_fv, nat, t5);
        let t7 = d.pi_fv(t_fv, nat, t6);
        let t8 = d.pi_fv(a_fv, int_ty, t7);
        d.pi_fv(n_fv, int_ty, t8)
    };
    NatOps::declare_theorem(d, p.order_pow_eq_of_le, ty, value)
}

/// `Int.primitive_root_pow_injective : ∀ (n : Nat) (a : Int) (i j : Nat),
/// Nat.lt 0 n → IsPrimitiveRoot n a → Nat.lt i (totient n) →
/// Nat.lt j (totient n) → ModEq (ofNat n) (pow a i) (pow a j) → Eq Nat i j`
///
/// The `φ(n)` powers `a^0, …, a^(φ(n)-1)` of a primitive root are pairwise
/// incongruent mod `n` — i.e. they enumerate the units without repetition,
/// which is the reason primitive roots are worth naming. `Nat.le_total`
/// reduces this to [`declare_order_pow_eq_of_le`] in either order.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_primitive_root_pow_injective(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_nat = NatOps::zero(d);
    let hn_ty = d.lt(zero_nat, n);
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);

    let hpr_ty = is_primitive_root(d, n, a);
    let hpr_fv = d.fresh_fvar();
    let hpr = d.kernel().fvar(hpr_fv);

    let t = totient(d, n);
    let hi_ty = d.lt(i, t);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hj_ty = d.lt(j, t);
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);

    let big_n = d.of_nat(n);
    let pow_ai = d.ipow(a, i);
    let pow_aj = d.ipow(a, j);
    let hij_ty = imodeq(d, big_n, pow_ai, pow_aj);
    let hij_fv = d.fresh_fvar();
    let hij = d.kernel().fvar(hij_fv);

    let goal = d.eq(i, j);

    let le_ij = d.le(i, j);
    let le_ji = d.le(j, i);
    let disj = {
        let f = d.int().nat.le_total;
        d.const_app(f, &[i, j])
    };

    let proof = d.or_elim(
        le_ij,
        le_ji,
        goal,
        disj,
        &|d, hle| {
            d.lemma(
                p.order_pow_eq_of_le,
                &[big_n, a, t, i, j, hn, hpr, hle, hj, hij],
            )
        },
        &|d, hle| {
            let flipped = d.lemma(p.mod_eq_symm, &[big_n, pow_ai, pow_aj, hij]);
            let hji = d.lemma(
                p.order_pow_eq_of_le,
                &[big_n, a, t, j, i, hn, hpr, hle, hi, flipped],
            );
            d.symm(j, i, hji)
        },
    );

    let value = {
        let b0 = d.lam_fv(hij_fv, hij_ty, proof);
        let b1 = d.lam_fv(hj_fv, hj_ty, b0);
        let b2 = d.lam_fv(hi_fv, hi_ty, b1);
        let b3 = d.lam_fv(hpr_fv, hpr_ty, b2);
        let b4 = d.lam_fv(hn_fv, hn_ty, b3);
        let b5 = d.lam_fv(j_fv, nat, b4);
        let b6 = d.lam_fv(i_fv, nat, b5);
        let b7 = d.lam_fv(a_fv, int_ty, b6);
        d.lam_fv(n_fv, nat, b7)
    };
    let ty = {
        let t0 = d.arrow(hij_ty, goal);
        let t1 = d.arrow(hj_ty, t0);
        let t2 = d.arrow(hi_ty, t1);
        let t3 = d.arrow(hpr_ty, t2);
        let t4 = d.arrow(hn_ty, t3);
        let t5 = d.pi_fv(j_fv, nat, t4);
        let t6 = d.pi_fv(i_fv, nat, t5);
        let t7 = d.pi_fv(a_fv, int_ty, t6);
        d.pi_fv(n_fv, nat, t7)
    };
    NatOps::declare_theorem(d, p.primitive_root_pow_injective, ty, value)
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
    declare_order_unique(d)?;
    declare_order_exists(d)?;
    declare_order_dvd_totient(d)?;
    declare_is_primitive_root(d)?;
    declare_order_pow_eq_of_le(d)?;
    declare_primitive_root_pow_injective(d)?;
    Ok(())
}
