//! Order and additive facts about `Nat.bit` closing five `ml430` mirrors:
//! `bit_le`, `bit_lt_bit`, `bit_ne_zero`, `bit_add` (both associativity
//! orders), and `bit_false_zero`. A NEW module rather than an addition to
//! `bits.rs` (already a dense, self-contained theorem set) so a merge
//! conflict there is never necessary for these.
//!
//! `Nat.bit test n ≡ add (mul 2 n) (bool_select_nat test 1 0)` (`bits.rs`'s
//! own doc comment). Every proof below either shares the SAME selector term
//! between both sides (`bit_le`, `bit_add`) — so no case split on the `Bool`
//! argument is ever needed — or bounds the selector abstractly by `Le _ 1`
//! (`bit_lt_bit`) via one small `Bool.rec` case split
//! ([`sel_le_one`]), rather than fully case-splitting the outer goal on the
//! `Bool` argument(s) the way the "bound to `{0,1}`" idiom elsewhere in this
//! prelude usually does — the abstract selector bound is enough here because
//! every conclusion is itself already stated in terms of `add`/`mul`, not a
//! `Bool`-valued function.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;

/// `Nat.bit test n`.
fn bit(d: &mut NatDev<'_>, p: &NatPrelude, test: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.bit, &[test, n])
}

/// `bool_select_nat test 1 0` — the raw selector `Nat.bit` is built from.
fn sel(d: &mut NatDev<'_>, test: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    d.bool_select_nat(test, one, zero)
}

/// `Le (bool_select_nat test 1 0) 1`, for an arbitrary (possibly free)
/// `Bool` `test` — a `Bool.rec` case split, since `bool_select_nat` only
/// reduces at a literal constructor and `test` here is a bound variable.
/// `false` gives `Le 0 1` ([`NatPrelude::zero_le`]); `true` gives `Le 1 1`
/// ([`NatPrelude::le_refl`]).
fn sel_le_one(d: &mut NatDev<'_>, p: &NatPrelude, test: ExprId) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let motive = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let sel_t = sel(d, t);
        let one = d.num(1);
        let body = d.le(sel_t, one);
        d.lam_fv(t_fv, bool_ty, body)
    };
    let case_false = {
        let one = d.num(1);
        d.lemma(p.zero_le, &[one])
    };
    let case_true = {
        let one = d.num(1);
        d.lemma(p.le_refl, &[one])
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, test])
}

/// `Nat.bit_false_zero : Eq (bit false 0) 0` — `refl`: `bit false 0` unfolds
/// (delta+iota) to `add (mul 2 0) 0`, and `Nat.mul`/`Nat.add` each reduce on
/// a literal `0` right argument (their shared base case).
pub(super) fn declare_bit_false_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.bit_false_zero, 0, &|d, _v| {
        let zero = d.zero();
        let false_ = d.bool_false();
        let lhs = bit(d, &p, false_, zero);
        (d.eq(lhs, zero), d.refl(zero))
    })?;
    Ok(())
}

/// `Nat.bit_le : ∀ (b : Bool) {m n}, Le m n → Le (bit b m) (bit b n)`.
///
/// `bit b m ≡ add (mul 2 m) (sel b)` and `bit b n ≡ add (mul 2 n) (sel b)`
/// share the SAME selector term (same `b`), so this is
/// [`NatPrelude::mul_le_mul_left`] on the doubled halves composed with
/// [`NatPrelude::add_le_add_right`] on the shared selector — no case split
/// on `b` needed.
pub(super) fn declare_bit_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hyp_ty = d.le(m, n);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let two = d.num(2);
    let mul_le = d.lemma(p.mul_le_mul_left, &[two, m, n, hyp]);
    let mul2m = d.mul(two, m);
    let mul2n = d.mul(two, n);
    let selb = sel(d, b);
    let add_le = d.lemma(p.add_le_add_right, &[selb, mul2m, mul2n, mul_le]);

    let lhs = bit(d, &p, b, m);
    let rhs = bit(d, &p, b, n);
    let concl = d.le(lhs, rhs);
    let stmt = d.arrow(hyp_ty, concl);
    let proof = d.lam_fv(hyp_fv, hyp_ty, add_le);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        d.pi_fv(b_fv, bool_ty, over_m)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        d.lam_fv(b_fv, bool_ty, over_m)
    };
    d.declare_theorem(p.bit_le, ty, value)
}

/// `Nat.bit_ne_zero : ∀ (b : Bool) {n}, n ≠ 0 → bit b n ≠ 0`.
///
/// Route: `n ≠ 0 → 0 < n` ([`NatPrelude::zero_lt_of_ne_zero`]) `→ 0 < mul 2
/// n` ([`NatPrelude::mul_lt_mul_left`]'s `mpr`, instantiated at the base
/// point `mul 2 0` which is `refl`-`0`) `→ 0 < add (sel b) (mul 2 n)`
/// ([`NatPrelude::add_pos_right`]) `→ 0 < bit b n` (commute the sum via
/// [`NatPrelude::add_comm`]). Assuming `bit b n = 0` and transporting that
/// positivity fact along the assumption gives `0 < 0`, refuted by
/// [`NatPrelude::lt_irrefl`].
pub(super) fn declare_bit_ne_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero = d.zero();
    let ne_hyp_ty = {
        let e = d.eq(n, zero);
        d.arrow(e, false_ty)
    };
    let ne_fv = d.fresh_fvar();
    let ne_h = d.kernel().fvar(ne_fv);

    // 0 < n
    let pos_n = d.lemma(p.zero_lt_of_ne_zero, &[n, ne_h]);

    // 0 < mul 2 n, via mul_lt_mul_left(2, 0, n, 0<2).mpr pos_n
    let one = d.num(1);
    let two = d.succ(one);
    let pos2 = d.zero_lt_succ(one);
    let iff_ty = d.lemma(p.mul_lt_mul_left, &[two, zero, n, pos2]);
    let mul2_0 = d.mul(two, zero);
    let mul2_n = d.mul(two, n);
    let lt_a = d.lt(mul2_0, mul2_n);
    let lt_b = d.lt(zero, n);
    let mul2n_pos = d.lemma(p.logic.iff_mpr, &[lt_a, lt_b, iff_ty, pos_n]);

    // 0 < add (sel b) (mul 2 n), via add_pos_right(mul2_n, sel b, mul2n_pos)
    let selb = sel(d, b);
    let add_pos = d.lemma(p.add_pos_right, &[mul2_n, selb, mul2n_pos]);
    let add_sel_mul2n = d.add(selb, mul2_n);
    let add_mul2n_sel = d.add(mul2_n, selb);
    let comm_eq = d.lemma(p.add_comm, &[selb, mul2_n]);
    let motive_comm = d.eq_motive(add_sel_mul2n, &|d, x| {
        let zero = d.zero();
        d.lt(zero, x)
    });
    let bit_pos = d.transport(add_sel_mul2n, motive_comm, add_pos, add_mul2n_sel, comm_eq);

    // Assume bit b n = 0, derive False.
    let bit_bn = bit(d, &p, b, n);
    let heq_ty = d.eq(bit_bn, zero);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let motive2 = d.eq_motive(bit_bn, &|d, x| {
        let zero = d.zero();
        d.lt(zero, x)
    });
    let lt_zero_zero = d.transport(bit_bn, motive2, bit_pos, zero, heq);
    let contra = d.lemma(p.lt_irrefl, &[zero, lt_zero_zero]);

    let inner_stmt = d.arrow(heq_ty, false_ty);
    let inner_proof = d.lam_fv(heq_fv, heq_ty, contra);

    let full_stmt = d.arrow(ne_hyp_ty, inner_stmt);
    let full_proof = d.lam_fv(ne_fv, ne_hyp_ty, inner_proof);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, full_stmt);
        d.pi_fv(b_fv, bool_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, full_proof);
        d.lam_fv(b_fv, bool_ty, over_n)
    };
    d.declare_theorem(p.bit_ne_zero, ty, value)
}

/// `Nat.bit_lt_bit : ∀ {m n} (a b : Bool), Lt m n → Lt (bit a m) (bit b n)`.
///
/// Fully abstract in `a`/`b` — no case split on either `Bool` — via
/// [`sel_le_one`] bounding each selector by `Le _ 1`:
///
/// `bit a m = add (mul 2 m) (sel a) ≤ add (mul 2 m) 1 = succ (mul 2 m)`
/// (`add_le_add_left` + `sel_le_one a`).
///
/// `Lt m n` gives `Le (succ m) n`, so `mul_le_mul_left` at `2` gives
/// `Le (mul 2 (succ m)) (mul 2 n)`, and `mul 2 (succ m)` is `refl`-
/// `succ (succ (mul 2 m))` (`Nat.mul`/`Nat.add` both recurse on the right
/// argument, so `mul_succ`'s own reduction plus `add`'s `succ` case fire by
/// iota alone — no lemma). `lt_succ_self (mul 2 m) : Lt (succ (mul 2 m))
/// (succ (succ (mul 2 m)))` composed with that bound via `lt_of_lt_of_le`
/// gives `Lt (succ (mul 2 m)) (mul 2 n)`.
///
/// `mul 2 n = add (mul 2 n) 0 ≤ add (mul 2 n) (sel b) = bit b n`
/// (`le_add_right`, since `sel b` needs no positivity here).
///
/// Chaining `bit a m ≤ succ (mul 2 m)`, `Lt (succ (mul 2 m)) (mul 2 n)`,
/// `mul 2 n ≤ bit b n` via `lt_of_le_of_lt` then `lt_of_lt_of_le` closes it.
pub(super) fn declare_bit_lt_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hyp_ty = d.lt(m, n);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let two = d.num(2);
    let one = d.num(1);
    let mul2m = d.mul(two, m);
    let mul2n = d.mul(two, n);
    let sela = sel(d, a);
    let selb = sel(d, b);

    // bit a m <= succ(mul2m)
    let sela_le_one = sel_le_one(d, &p, a);
    let step_upper = d.lemma(p.add_le_add_left, &[mul2m, sela, one, sela_le_one]);
    // step_upper : Le (add mul2m sela) (add mul2m one)  ==  Le (bit a m) (succ mul2m)
    let succ_mul2m = d.succ(mul2m);

    // Lt m n -> Le (succ m) n -> Le (mul 2 (succ m)) (mul 2 n)
    let succ_m = d.succ(m);
    let mul2_succm_le_mul2n = d.lemma(p.mul_le_mul_left, &[two, succ_m, n, hyp]);
    // mul 2 (succ m) is refl `succ (succ mul2m)` (mul_succ + add's succ case, both iota)
    let succ_succ_mul2m = d.succ(succ_mul2m);

    // Lt succ_mul2m succ_succ_mul2m
    let lt_succ_step = d.lemma(p.lt_succ_self, &[mul2m]);
    // Lt succ_mul2m mul2n
    let lt_succ_mul2n = d.lemma(
        p.lt_of_lt_of_le,
        &[succ_mul2m, succ_succ_mul2m, mul2n, lt_succ_step, mul2_succm_le_mul2n],
    );

    // mul2n <= bit b n
    let mul2n_le_bit_b_n = d.lemma(p.le_add_right, &[mul2n, selb]);

    // bit a m <= succ_mul2m  <  mul2n  <=  bit b n
    let bit_a_m = bit(d, &p, a, m);
    let bit_b_n = bit(d, &p, b, n);
    let combined1 = d.lemma(
        p.lt_of_le_of_lt,
        &[bit_a_m, succ_mul2m, mul2n, step_upper, lt_succ_mul2n],
    );
    let combined2 = d.lemma(
        p.lt_of_lt_of_le,
        &[bit_a_m, mul2n, bit_b_n, combined1, mul2n_le_bit_b_n],
    );

    let concl = d.lt(bit_a_m, bit_b_n);
    let stmt = d.arrow(hyp_ty, concl);
    let proof = d.lam_fv(hyp_fv, hyp_ty, combined2);

    let ty = {
        let over_b = d.pi_fv(b_fv, bool_ty, stmt);
        let over_a = d.pi_fv(a_fv, bool_ty, over_b);
        let over_n = d.pi_fv(n_fv, nat, over_a);
        d.pi_fv(m_fv, nat, over_n)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, bool_ty, proof);
        let over_a = d.lam_fv(a_fv, bool_ty, over_b);
        let over_n = d.lam_fv(n_fv, nat, over_a);
        d.lam_fv(m_fv, nat, over_n)
    };
    d.declare_theorem(p.bit_lt_bit, ty, value)
}

/// `Nat.bit_add_left : ∀ (b : Bool) (n m), bit b (n + m) = bit false n + bit
/// b m`.
///
/// `bit b (n+m) = add (mul 2 (n+m)) (sel b) = add (add (mul 2 n) (mul 2 m))
/// (sel b)` ([`NatPrelude::left_distrib`]) `= add (mul 2 n) (add (mul 2 m)
/// (sel b))` ([`NatPrelude::add_assoc`]) `= bit false n + bit b m` (both
/// summands already in `bit` form by `refl`).
fn declare_bit_add_left_shared(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    name: NameId,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let two = d.num(2);
    let n_plus_m = d.add(n, m);
    let selb = sel(d, b);
    let start = {
        let mul2_sum = d.mul(two, n_plus_m);
        d.add(mul2_sum, selb)
    };

    let mul2n = d.mul(two, n);
    let mul2m = d.mul(two, m);
    let mul2n_plus_mul2m = d.add(mul2n, mul2m);
    let distrib_eq = d.lemma(p.left_distrib, &[two, n, m]);
    // distrib_eq : Eq (mul 2 (n+m)) (add mul2n mul2m)
    let mul2_sum = d.mul(two, n_plus_m);
    let step1 = d.congr(mul2_sum, mul2n_plus_mul2m, distrib_eq, &|d, x| {
        d.add(x, selb)
    });
    let mid = d.add(mul2n_plus_mul2m, selb);

    let assoc_eq = d.lemma(p.add_assoc, &[mul2n, mul2m, selb]);
    // assoc_eq : Eq (add (add mul2n mul2m) selb) (add mul2n (add mul2m selb))
    let mul2m_plus_selb = d.add(mul2m, selb);
    let target = d.add(mul2n, mul2m_plus_selb);

    let (_e, proof) = d.chain(start, &[(mid, step1), (target, assoc_eq)]);

    let false_ = d.bool_false();
    let bit_false_n = bit(d, &p, false_, n);
    let bit_b_m = bit(d, &p, b, m);
    let bit_b_sum = bit(d, &p, b, n_plus_m);
    let rhs = d.add(bit_false_n, bit_b_m);
    let stmt = d.eq(bit_b_sum, rhs);

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        d.pi_fv(b_fv, bool_ty, over_n)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_m);
        d.lam_fv(b_fv, bool_ty, over_n)
    };
    d.declare_theorem(name, ty, value)
}

/// `Nat.bit_add_right : ∀ (b : Bool) (n m), bit b (n + m) = bit b n + bit
/// false m`.
///
/// Same setup as [`declare_bit_add_left_shared`], but the final rearrangement
/// step is [`NatPrelude::add_right_comm`] (`add (add x y) z = add (add x z)
/// y`) instead of `add_assoc`, landing on `add (add mul2n selb) mul2m = bit b
/// n + bit false m`.
fn declare_bit_add_right_shared(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    name: NameId,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let two = d.num(2);
    let n_plus_m = d.add(n, m);
    let selb = sel(d, b);
    let start = {
        let mul2_sum = d.mul(two, n_plus_m);
        d.add(mul2_sum, selb)
    };

    let mul2n = d.mul(two, n);
    let mul2m = d.mul(two, m);
    let mul2n_plus_mul2m = d.add(mul2n, mul2m);
    let distrib_eq = d.lemma(p.left_distrib, &[two, n, m]);
    let mul2_sum = d.mul(two, n_plus_m);
    let step1 = d.congr(mul2_sum, mul2n_plus_mul2m, distrib_eq, &|d, x| {
        d.add(x, selb)
    });
    let mid = d.add(mul2n_plus_mul2m, selb);

    let rc_eq = d.lemma(p.add_right_comm, &[mul2n, mul2m, selb]);
    // rc_eq : Eq (add (add mul2n mul2m) selb) (add (add mul2n selb) mul2m)
    let mul2n_plus_selb = d.add(mul2n, selb);
    let target = d.add(mul2n_plus_selb, mul2m);

    let (_e, proof) = d.chain(start, &[(mid, step1), (target, rc_eq)]);

    let false_ = d.bool_false();
    let bit_b_n = bit(d, &p, b, n);
    let bit_false_m = bit(d, &p, false_, m);
    let bit_b_sum = bit(d, &p, b, n_plus_m);
    let rhs = d.add(bit_b_n, bit_false_m);
    let stmt = d.eq(bit_b_sum, rhs);

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        d.pi_fv(b_fv, bool_ty, over_n)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_m);
        d.lam_fv(b_fv, bool_ty, over_n)
    };
    d.declare_theorem(name, ty, value)
}

pub(super) fn declare_bit_add_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let name = p.bit_add_left;
    declare_bit_add_left_shared(d, p, name)
}

pub(super) fn declare_bit_add_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let name = p.bit_add_right;
    declare_bit_add_right_shared(d, p, name)
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_bit_extra_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_bit_false_zero(d, p)?;
    declare_bit_le(d, p)?;
    declare_bit_ne_zero(d, p)?;
    declare_bit_lt_bit(d, p)?;
    declare_bit_add_left(d, p)?;
    declare_bit_add_right(d, p)?;
    Ok(())
}
