//! The floor-counting family — ADR-1260's residue 1, and the bridge from its
//! division-free rectangle partition to the floor language Eisenstein's lemma
//! is classically stated in.
//!
//! # Why this does NOT fight the stuck `Nat.div`
//!
//! `Nat.div`/`Nat.mod` are stuck at symbolic arguments, and this prelude's
//! standing rule is to prefer a lemma that EMITS a shape over a hypothesis
//! about a residue. The floor-counting family looks like the worst case for
//! that rule, and it is not, because the emitter already exists:
//!
//! - [`NatPrelude::div_mod`] is the RELATIONAL Euclidean specification,
//!   `divMod d n q r := n = d*q + r ∧ r < d`, with `q` and `r` ordinary bound
//!   variables. Nothing in it is a projection, so nothing in it can be stuck.
//! - [`NatPrelude::div_mod_mul_le_iff`] is the floor adjunction stated against
//!   that relation: `divMod d n q r → (d*s ≤ n ↔ s ≤ q)`. This is
//!   `Nat.le_div_iff_mul_le` with the quotient EMITTED as a variable rather
//!   than named by `div`.
//! - [`NatPrelude::div_mod_exec`] closes the loop the other way: the
//!   executable projections satisfy the relation, at a divisor given
//!   constructively as `succ ap`.
//!
//! So the whole family is proved with `div` appearing nowhere, and the
//! executable form is one instantiation at the end. That is the same shape as
//! `Nat.even_or_odd` (which produces `m = h + h` with `h := div m 2` already
//! computed, so no division ever reduces), one level of generality up.
//!
//! # The three declarations
//!
//! 1. [`declare_count_range_succ_le_eq_min`] — the counting core, with no
//!    division in the statement at all:
//!    `countRange (fun y => ble (succ y) c) n = Min.min n c`. Structural
//!    induction on `n`, `Min.min` decided at each step by the `Nat.ble` cut
//!    `minmax_lemmas.rs` documents.
//! 2. [`declare_count_range_mul_succ_le_eq_min`] — the same count with the
//!    bound moved across the adjunction:
//!    `divMod a B q r → countRange (fun j => ble (mul a (succ j)) B) n
//!     = Min.min n q`. One `countRange_congr` over a pointwise `Bool`
//!    equation, itself one `div_mod_mul_le_iff`.
//! 3. [`declare_count_range_mul_succ_le_eq_floor`] — the executable corollary,
//!    `countRange (fun j => ble (mul (succ ap) (succ j)) B) n
//!     = Min.min n (div B (succ ap))`, by `div_mod_exec`.
//!
//! # Why `Min.min` and not `Nat.sub`
//!
//! The count saturates: once `c` many indices below `n` satisfy the predicate,
//! raising `n` adds nothing. `Nat.sub`'s truncation is the usual way that shape
//! is written and the usual source of trouble inside an induction (ADR-0970/
//! ADR-0985 took a disjunctive statement precisely to avoid it). `Min.min` says
//! the same thing with no truncation anywhere, and both of its branch lemmas
//! (`min_eq_left`, `min_eq_right`) are already proved.
//!
//! Eisenstein's own consumer never sees the `min` bind — `⌊q·x/p⌋ ≤ (q−1)/2`
//! for `1 ≤ x ≤ (p−1)/2` — but that is a fact about primes, not about counting,
//! and it belongs to the consumer rather than to this lemma. Check `M8` of
//! `docs/research/09-decisions/adr-1290-floor-count-checks.py` records that
//! dropping the `min` from the assembled lattice identity SURVIVES numerically
//! for exactly that reason.

use super::NatPrelude;
use super::helpers::{iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local term builders (this prelude's house style: each file keeps its own).
// ============================================================================

/// `countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `Min.min a b`.
fn min_of(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.min_min, &[a, b])
}

/// `fun y : Nat => ble (succ y) c` — the predicate "`y < c`", spelled with the
/// `succ` shift because `Nat.ble` computes `≤` directly.
fn lt_pred(d: &mut NatDev<'_>, c: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let sy = d.succ(y);
    let body = d.ble(sy, c);
    d.lam_fv(y_fv, nat, body)
}

/// `fun j : Nat => ble (mul a (succ j)) bound` — the predicate
/// "`a·(j+1) ≤ bound`", i.e. one row of Eisenstein's lattice rectangle.
fn mul_le_pred(d: &mut NatDev<'_>, a: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let prod = d.mul(a, sj);
    let body = d.ble(prod, bound);
    d.lam_fv(j_fv, nat, body)
}

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)` — the Bool-domain, Nat-codomain
/// congruence [`NatOps::congr`] does not provide (it is hardcoded to a `Nat`
/// domain). Same recipe as `totient.rs`'s private `bool_congr_nat`.
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Or`-elimination into an arbitrary goal. Mirrors `gauss_lemma.rs`'s
/// `or_elim2`.
#[allow(clippy::too_many_arguments)]
fn or_elim2(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    scrutinee: ExprId,
    left_branch: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    right_branch: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let h_fv1 = d.fresh_fvar();
    let h1 = d.kernel().fvar(h_fv1);
    let lb_body = left_branch(d, h1);
    let lb = d.lam_fv(h_fv1, left_ty, lb_body);
    let h_fv2 = d.fresh_fvar();
    let h2 = d.kernel().fvar(h_fv2);
    let rb_body = right_branch(d, h2);
    let rb = d.lam_fv(h_fv2, right_ty, rb_body);
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let or_motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(or_rec, &[left_ty, right_ty, or_motive, lb, rb, scrutinee])
}

/// `iff : Iff (Le x y) (Le u v) ⊢ Eq Bool (ble x y) (ble u v)`.
///
/// Two order splits, both through `Nat.lt_or_ge`, so no negated `Prop` and no
/// `Not` elimination is ever formed:
///
/// - `Le x y`: both booleans are `true` (`ble_eq_true_of_le` on each side,
///   the right one via the `Iff`'s forward direction).
/// - `Lt y x`: the left boolean is `false` (`ble_eq_false_of_lt`). A second
///   split decides the right one — either directly, or through the impossible
///   branch where `Le u v` transports back across the `Iff` to contradict
///   `Lt y x` at `lt_of_lt_of_le` + `lt_irrefl`.
#[allow(clippy::too_many_arguments)]
fn ble_eq_of_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    y: ExprId,
    u: ExprId,
    v: ExprId,
    iff_proof: ExprId,
) -> ExprId {
    let p = *p;
    let ble_xy = d.ble(x, y);
    let ble_uv = d.ble(u, v);
    let goal = d.bool_eq(ble_xy, ble_uv);

    let le_xy_ty = d.le(x, y);
    let le_uv_ty = d.le(u, v);
    let lt_yx_ty = d.lt(y, x);
    let split = d.lemma(p.lt_or_ge, &[y, x]);

    or_elim2(
        d,
        &p,
        lt_yx_ty,
        le_xy_ty,
        goal,
        split,
        // Lt y x: the left boolean is false.
        &|d, hlt| {
            let false_v = d.bool_false();
            let left_false = d.lemma(p.ble_eq_false_of_lt, &[x, y, hlt]);
            let lt_vu_ty = d.lt(v, u);
            let inner_split = d.lemma(p.lt_or_ge, &[v, u]);
            let right_false_ty = d.bool_eq(ble_uv, false_v);
            let right_false = or_elim2(
                d,
                &p,
                lt_vu_ty,
                le_uv_ty,
                right_false_ty,
                inner_split,
                &|d, hlt2| d.lemma(p.ble_eq_false_of_lt, &[u, v, hlt2]),
                // Le u v would give Le x y, contradicting Lt y x.
                &|d, hle2| {
                    let back = iff_reverse(d, le_xy_ty, le_uv_ty, iff_proof);
                    let hxy = d.apply(back, &[hle2]);
                    let loop_ = d.lemma(p.lt_of_lt_of_le, &[y, x, y, hlt, hxy]);
                    let irrefl = d.lemma(p.lt_irrefl, &[y]);
                    let absurd = d.apply(irrefl, &[loop_]);
                    let target = right_false_ty;
                    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                    let anon = d.anon_name();
                    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                    let level_zero = d.kernel().level_zero();
                    let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                    d.apply(false_rec, &[motive, absurd])
                },
            );
            let flipped = d.bool_symm(ble_uv, false_v, right_false);
            d.bool_trans(ble_xy, false_v, ble_uv, left_false, flipped)
        },
        // Le x y: both booleans are true.
        &|d, hle| {
            let true_v = d.bool_true();
            let left_true = d.lemma(p.ble_eq_true_of_le, &[x, y, hle]);
            let forward = iff_forward(d, le_xy_ty, le_uv_ty, iff_proof);
            let huv = d.apply(forward, &[hle]);
            let right_true = d.lemma(p.ble_eq_true_of_le, &[u, v, huv]);
            let flipped = d.bool_symm(ble_uv, true_v, right_true);
            d.bool_trans(ble_xy, true_v, ble_uv, left_true, flipped)
        },
    )
}

// ============================================================================
// 1. The counting core: no division anywhere.
// ============================================================================

/// `Nat.countRange_succ_le_eq_min : ∀ c n,
/// Eq (countRange (fun y => ble (succ y) c) n) (Min.min n c)`.
///
/// Induction on `n` with `c` an outer parameter. `countRange_zero` /
/// `countRange_succ` are both `Eq.refl`, so the step's left-hand side is
/// definitionally `add (countRange f j) (bool_select_nat (ble (succ j) c) 1 0)`
/// and the whole proof is deciding that one boolean:
///
/// | `lt_or_ge j c` | boolean | `Min.min j c` | `Min.min (succ j) c` |
/// |---|---|---|---|
/// | `Lt j c` (i.e. `Le (succ j) c`) | `true`, so the increment is `1` | `j` | `succ j` |
/// | `Le c j` | `false`, so the increment is `0` | `c` | `c` |
///
/// Both `bool_select_nat` applications iota-reduce at the literal boolean, and
/// `add t 1 ≡ succ t` / `add t 0 ≡ t` hold definitionally because `Nat.add`
/// recurses on its RIGHT argument — so neither branch forms a numeral or needs
/// an arithmetic lemma.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_succ_le_eq_min(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.count_range_succ_le_eq_min, 2, &|d, v| {
        let (c, n) = (v[0], v[1]);
        let f = lt_pred(d, c);

        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = count_range(d, &p, f, x);
            let rhs = min_of(d, &p, x, c);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);

        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let base = d.lemma(p.count_range_zero, &[f]);
                let zero_le_c = d.lemma(p.zero_le, &[c]);
                let min_zero = d.lemma(p.min_eq_left, &[zero, c, zero_le_c]);
                let min_term = min_of(d, &p, zero, c);
                let flipped = d.symm(min_term, zero, min_zero);
                let lhs = count_range(d, &p, f, zero);
                d.trans(lhs, zero, min_term, base, flipped)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let cj = count_range(d, &p, f, j);
                let start = count_range(d, &p, f, sj);
                let goal = {
                    let rhs = min_of(d, &p, sj, c);
                    d.eq(start, rhs)
                };
                let lt_jc_ty = d.lt(j, c);
                let le_cj_ty = d.le(c, j);
                let split = d.lemma(p.lt_or_ge, &[j, c]);

                or_elim2(
                    d,
                    &p,
                    lt_jc_ty,
                    le_cj_ty,
                    goal,
                    split,
                    // `Lt j c` is definitionally `Le (succ j) c`.
                    &|d, hlt| {
                        let ble_true = d.lemma(p.ble_eq_true_of_le, &[sj, c, hlt]);
                        let scrutinee = d.ble(sj, c);
                        let true_v = d.bool_true();
                        let bumped =
                            bool_congr_nat(d, scrutinee, true_v, ble_true, &|d, x| {
                                let one = d.num(1);
                                let zero = d.zero();
                                let sel = d.bool_select_nat(x, one, zero);
                                d.add(cj, sel)
                            });
                        // `Le j c` for the inductive hypothesis's `Min.min j c`.
                        let j_le_sj = d.lemma(p.le_succ, &[j]);
                        let j_le_c = d.lemma(p.le_trans, &[j, sj, c, j_le_sj, hlt]);
                        let min_jc = min_of(d, &p, j, c);
                        let min_jc_eq_j = d.lemma(p.min_eq_left, &[j, c, j_le_c]);
                        let cj_eq_j = d.trans(cj, min_jc, j, ih, min_jc_eq_j);
                        let succ_cj = d.succ(cj);
                        let bump = d.congr(cj, j, cj_eq_j, &|d, t| d.succ(t));
                        let min_sjc = min_of(d, &p, sj, c);
                        let min_sjc_eq = d.lemma(p.min_eq_left, &[sj, c, hlt]);
                        let flipped = d.symm(min_sjc, sj, min_sjc_eq);
                        let (_end, chained) = d.chain(
                            start,
                            &[(succ_cj, bumped), (sj, bump), (min_sjc, flipped)],
                        );
                        chained
                    },
                    // `Le c j`: the predicate is already false at `j`.
                    &|d, hle| {
                        let c_lt_sj = d.lemma(p.le_succ_succ, &[c, j, hle]);
                        let ble_false = d.lemma(p.ble_eq_false_of_lt, &[sj, c, c_lt_sj]);
                        let scrutinee = d.ble(sj, c);
                        let false_v = d.bool_false();
                        let dropped =
                            bool_congr_nat(d, scrutinee, false_v, ble_false, &|d, x| {
                                let one = d.num(1);
                                let zero = d.zero();
                                let sel = d.bool_select_nat(x, one, zero);
                                d.add(cj, sel)
                            });
                        let min_jc = min_of(d, &p, j, c);
                        let min_jc_eq_c = d.lemma(p.min_eq_right, &[j, c, hle]);
                        let cj_eq_c = d.trans(cj, min_jc, c, ih, min_jc_eq_c);
                        let j_le_sj = d.lemma(p.le_succ, &[j]);
                        let c_le_sj = d.lemma(p.le_trans, &[c, j, sj, hle, j_le_sj]);
                        let min_sjc = min_of(d, &p, sj, c);
                        let min_sjc_eq = d.lemma(p.min_eq_right, &[sj, c, c_le_sj]);
                        let flipped = d.symm(min_sjc, c, min_sjc_eq);
                        let (_end, chained) =
                            d.chain(start, &[(cj, dropped), (c, cj_eq_c), (min_sjc, flipped)]);
                        chained
                    },
                )
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// 2. The relational bridge: `div` appears nowhere.
// ============================================================================

/// `Nat.countRange_mul_succ_le_eq_min : ∀ a B q r n, divMod a B q r →
/// Eq (countRange (fun j => ble (mul a (succ j)) B) n) (Min.min n q)`.
///
/// ADR-1260's residue 1, in the form that never reduces a division. The whole
/// content is one pointwise `Bool` equation,
/// `ble (mul a (succ j)) B = ble (succ j) q`, which is
/// [`NatPrelude::div_mod_mul_le_iff`] at `s := succ j` pushed through
/// [`ble_eq_of_iff`]; `countRange_congr` then moves it under the count and
/// [`declare_count_range_succ_le_eq_min`] finishes.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_mul_succ_le_eq_min(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.count_range_mul_succ_le_eq_min, 5, &|d, v| {
        let (a, bound, q, r, n) = (v[0], v[1], v[2], v[3], v[4]);
        let nat = d.nat_ty();
        let relation_ty = d.div_mod(a, bound, q, r);
        let f = mul_le_pred(d, a, bound);
        let g = lt_pred(d, q);
        let lhs = count_range(d, &p, f, n);
        let rhs = min_of(d, &p, n, q);
        let target = d.eq(lhs, rhs);
        let stmt = d.arrow(relation_ty, target);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);

        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let si = d.succ(i);
            let prod = d.mul(a, si);
            let adjunction = d.lemma(p.div_mod_mul_le_iff, &[a, bound, q, r, si, relation]);
            let body = ble_eq_of_iff(d, &p, prod, bound, si, q, adjunction);
            d.lam_fv(i_fv, nat, body)
        };
        let congr = d.lemma(p.count_range_congr, &[f, g, n, pointwise]);
        let mid = count_range(d, &p, g, n);
        let core = d.lemma(p.count_range_succ_le_eq_min, &[q, n]);
        let body = d.trans(lhs, mid, rhs, congr, core);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// 3. The executable corollary.
// ============================================================================

/// `Nat.countRange_mul_succ_le_eq_floor : ∀ ap B n,
/// Eq (countRange (fun j => ble (mul (succ ap) (succ j)) B) n)
///    (Min.min n (div B (succ ap)))`.
///
/// [`declare_count_range_mul_succ_le_eq_min`] instantiated at the canonical
/// witness [`NatPrelude::div_mod_exec`]. Positivity of the divisor arrives
/// constructively as `succ ap`, matching that theorem's own shape, so no
/// `Lt zero a` hypothesis is formed and no consumer has to discharge one.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_mul_succ_le_eq_floor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.count_range_mul_succ_le_eq_floor, 3, &|d, v| {
        let (ap, bound, n) = (v[0], v[1], v[2]);
        let divisor = d.succ(ap);
        let quotient = d.div(bound, divisor);
        let remainder = d.modulo(bound, divisor);
        let f = mul_le_pred(d, divisor, bound);
        let lhs = count_range(d, &p, f, n);
        let rhs = min_of(d, &p, n, quotient);
        let stmt = d.eq(lhs, rhs);

        let witness = d.lemma(p.div_mod_exec, &[ap, bound]);
        let proof = d.lemma(
            p.count_range_mul_succ_le_eq_min,
            &[divisor, bound, quotient, remainder, n, witness],
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare the whole floor-counting family, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_floor_count_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_count_range_succ_le_eq_min(d, p)?;
    declare_count_range_mul_succ_le_eq_min(d, p)?;
    declare_count_range_mul_succ_le_eq_floor(d, p)?;
    Ok(())
}
