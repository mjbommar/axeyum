//! **ADR-1260's step 1, assembled: the lattice-point count as a sum of
//! floors.** Every input existed before this file and nobody had run them
//! together (ADR-1540's residue 4).
//!
//! # What is declared
//!
//! - [`declare_ble_select_add_of_ne`] — `Nat.ble_select_add_of_ne : ∀ a b,
//!   Not (Eq a b) → add (bool_select_nat (ble a b) 1 0)
//!   (bool_select_nat (ble b a) 1 0) = 1`. Two distinct naturals are compared
//!   one way or the other and never both: exactly the shape
//!   `Nat.countRectangle_partition` asks its consumer for, with the "no
//!   lattice point on the line" side condition as its only hypothesis.
//! - [`declare_eisenstein_floor_sum`] — the headline:
//!
//!   ```text
//!   Nat.eisenstein_floor_sum : ∀ ap aq m n,
//!     Eq (gcd (succ ap) (succ aq)) 1 → Lt m (succ ap) →
//!     Eq (add (sumRange (fun x => Min.min n (div (mul (succ aq) (succ x)) (succ ap))) m)
//!             (sumRange (fun y => Min.min m (div (mul (succ ap) (succ y)) (succ aq))) n))
//!        (mul n m)
//!   ```
//!
//! # How this differs from the way ADR-1260 and ADR-1540 state it
//!
//! Three deliberate restatements, none of which weakens the theorem:
//!
//! 1. **Coprimality and a bound, not primality.** ADR-1260 sizes step 1 at two
//!    distinct odd primes `p`, `q` with `m = (p−1)/2`, `n = (q−1)/2`. Nothing
//!    in the argument uses primality or the specific `m`, `n`: what it uses is
//!    `gcd p q = 1` (through
//!    [`mul_succ_ne_mul_succ_of_coprime`](NatPrelude::mul_succ_ne_mul_succ_of_coprime),
//!    ADR-1540) and `m < p` (to feed that lemma's `Lt (succ x) pp` at every
//!    `x < m`). Both hold at Eisenstein's instance — distinct primes are
//!    coprime and `(p−1)/2 < p` — so the consumer is not asked for anything it
//!    does not have, and the statement additionally covers coprime composites.
//!    `n` is unconstrained: the side condition bounds only the coordinate
//!    paired with `q`, which is the asymmetry ADR-1540 pinned.
//! 2. **The divisors are given constructively as `succ ap`, `succ aq`.** That
//!    is how [`count_range_mul_succ_le_eq_floor`](NatPrelude::count_range_mul_succ_le_eq_floor)
//!    (ADR-1290) supplies positivity, so no `Lt zero p` hypothesis is formed
//!    anywhere.
//! 3. **The row counts are `Min.min n ⌊·⌋`, not bare floors.** The `min` is
//!    what the floor lemma produces, and dropping it is a separate fact about
//!    Eisenstein's particular `m`, `n` (`⌊q·x/p⌋ ≤ (q−1)/2` for `1 ≤ x ≤
//!    (p−1)/2`) that is FALSE at general coprime `p`, `q` with unconstrained
//!    `n`. ADR-1290's check `M8` records that the min-free reading survives
//!    numerically **at prime pairs**; it is not the statement this theorem
//!    makes. See "what this does not prove" below.
//!
//! # Why the internal predicates are `≤` and not `<`
//!
//! ADR-1260 and ADR-1540 both describe the two half-planes as the STRICT
//! `p·(y+1) < q·(x+1)` and `q·(x+1) < p·(y+1)`. This file uses the non-strict
//! `ble (p·(y+1)) (q·(x+1))` and `ble (q·(x+1)) (p·(y+1))` instead, for one
//! reason: `Nat.countRange_mul_succ_le_eq_floor` is stated at
//! `ble (mul (succ ap) (succ j)) B`, so the non-strict predicate IS the floor
//! lemma's own shape and needs no bridging step, while the strict one is
//! `ble (succ (mul p (succ y))) (…)` and would.
//!
//! **The headline statement is unchanged by the choice**, because the
//! predicates appear nowhere in it — only the floors do. And the two readings
//! agree pointwise exactly where the side condition holds, which is the same
//! place `countRectangle_partition`'s hypothesis is discharged: with
//! `a ≠ b`, `a ≤ b` and `a < b` are the same proposition. Under `≤` the
//! complementarity hypothesis is precisely "`a` and `b` are distinct" —
//! [`declare_ble_select_add_of_ne`] — whereas under `<` it would additionally
//! need the trichotomy's `a = b` case to be ruled out on both sides. Same side
//! condition, one fewer step.
//!
//! # What this does NOT prove
//!
//! **Eisenstein's lemma is not proved and neither is quadratic reciprocity.**
//! This is step 1's counting identity and nothing else. In particular:
//!
//! - The `min` is not eliminated. Doing so needs `div (mul q (succ x)) pp ≤ n`
//!   for `x < m` under `pp = succ (2m)`, `q = succ (2n)` — true, but an
//!   arithmetic fact about those specific shapes, not about counting.
//! - Nothing here mentions [`gaussFold`](NatPrelude::gauss_fold),
//!   `gaussNegCount`, `leastResidue`, or any congruence mod 2. ADR-1540's
//!   residues 1–3 are untouched by this file.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_lt_or_ge};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Local term builders.
// ---------------------------------------------------------------------------

/// `bool_select_nat b 1 0` — `countRange`'s per-index contribution, spelled
/// exactly as `lattice_count.rs` spells it so the hypothesis matches.
fn sel(d: &mut NatDev<'_>, b: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    d.bool_select_nat(b, one, zero)
}

/// `countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `Min.min a b`.
fn min_of(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.min_min, &[a, b])
}

/// `False.rec (fun _ => target) false_proof : target`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// From `h_ab : Eq Bool (ble a b) ab_value` and `h_ba : Eq Bool (ble b a)
/// ba_value`, with `ab_value`/`ba_value` the two distinct `Bool` constructors,
/// build `Eq (add (sel (ble a b)) (sel (ble b a))) 1`.
///
/// The value at the two constructors is `1` by ι-reduction alone
/// (`add 1 0 ≡ 1` and `add 0 1 ≡ 1`; `Nat.add` recurses on its RIGHT
/// argument, so both are `Eq.refl`), so the whole step is two `Eq.rec`
/// transports over `Bool` carrying that single `refl`.
fn selector_sum_from_values(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    ab_value: ExprId,
    h_ab: ExprId,
    ba_value: ExprId,
    h_ba: ExprId,
) -> ExprId {
    let ab = d.ble(a, b);
    let ba = d.ble(b, a);
    let one = d.num(1);

    // `Eq (add (sel ab_value) (sel ba_value)) 1`, by `Eq.refl 1` — the two
    // sides are definitionally equal.
    let base = d.refl(one);

    // Replace `ba_value` by `ble b a`.
    let motive_right = d.bool_eq_motive(ba_value, &|d, value| {
        let s1 = sel(d, ab_value);
        let s2 = sel(d, value);
        let total = d.add(s1, s2);
        d.eq(total, one)
    });
    let flip_ba = d.bool_symm(ba, ba_value, h_ba);
    let step_right = d.bool_transport(ba_value, motive_right, base, ba, flip_ba);

    // Replace `ab_value` by `ble a b`.
    let motive_left = d.bool_eq_motive(ab_value, &|d, value| {
        let s1 = sel(d, value);
        let s2 = sel(d, ba);
        let total = d.add(s1, s2);
        d.eq(total, one)
    });
    let flip_ab = d.bool_symm(ab, ab_value, h_ab);
    d.bool_transport(ab_value, motive_left, step_right, ab, flip_ab)
}

// ---------------------------------------------------------------------------
// `Nat.ble_select_add_of_ne`.
// ---------------------------------------------------------------------------

/// `Nat.ble_select_add_of_ne : ∀ a b, Not (Eq a b) →
/// Eq (add (bool_select_nat (ble a b) 1 0) (bool_select_nat (ble b a) 1 0)) 1`
///
/// The complementarity witness `Nat.countRectangle_partition` asks for, at the
/// pair of non-strict comparisons this module's rectangle uses.
///
/// One [`cases_lt_or_ge`](super::ops::cases_lt_or_ge) at `a`, `b`:
///
/// - `a < b`: `ble a b = true` from `Le a b` (`le_trans` through `le_succ`,
///   since `Lt a b` IS `Le (succ a) b`), and `ble b a = false` from
///   `ble_eq_false_of_lt` at the same witness. The hypothesis is unused here.
/// - `b ≤ a`: `ble b a = true` directly, and `ble a b = false` once `Le b a`
///   is upgraded to `Lt b a` — which is where `Not (Eq a b)` is spent,
///   refuting `lt_or_eq_of_le`'s equality branch.
///
/// The hypothesis is load-bearing on exactly one side, and that is why the
/// negative control in `eisenstein_lattice_tests.rs` has to instantiate the
/// `a = b` case rather than a generic false witness: at `a = b` both
/// selectors are `1` and the sum is `2`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_ble_select_add_of_ne(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.ble_select_add_of_ne, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);

        let one = d.num(1);
        let ab = d.ble(a, b);
        let ba = d.ble(b, a);
        let goal = {
            let s1 = sel(d, ab);
            let s2 = sel(d, ba);
            let total = d.add(s1, s2);
            d.eq(total, one)
        };

        let eq_ty = d.eq(a, b);
        let ne_ty = d.const_app(p.logic.not, &[eq_ty]);
        let ne_fv = d.fresh_fvar();
        let ne = d.kernel().fvar(ne_fv);

        let true_ = d.bool_true();
        let false_ = d.bool_false();

        let body = cases_lt_or_ge(
            d,
            &p,
            a,
            b,
            &|_d, _n| goal,
            // `Lt a b`.
            &|d, _n, hlt| {
                let sa = d.succ(a);
                let le_a_sa = d.lemma(p.le_succ, &[a]);
                let le_ab = d.lemma(p.le_trans, &[a, sa, b, le_a_sa, hlt]);
                let h_ab = d.lemma(p.ble_eq_true_of_le, &[a, b, le_ab]);
                let h_ba = d.lemma(p.ble_eq_false_of_lt, &[b, a, hlt]);
                selector_sum_from_values(d, a, b, true_, h_ab, false_, h_ba)
            },
            // `Le b a`.
            &|d, _n, hle| {
                let h_ba = d.lemma(p.ble_eq_true_of_le, &[b, a, hle]);

                // `Lt b a`, by refuting `lt_or_eq_of_le`'s equality branch.
                let lt_ty = d.lt(b, a);
                let eq_ba_ty = d.eq(b, a);
                let disjunction = d.lemma(p.lt_or_eq_of_le, &[b, a, hle]);
                let left_branch = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    d.lam_fv(h_fv, lt_ty, h)
                };
                let right_branch = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let eq_ab = d.symm(b, a, h);
                    let contradiction = d.apply(ne, &[eq_ab]);
                    let absurd = ex_falso(d, &p, lt_ty, contradiction);
                    d.lam_fv(h_fv, eq_ba_ty, absurd)
                };
                let anon = d.anon_name();
                let or_ty = d.const_app(p.logic.or, &[lt_ty, eq_ba_ty]);
                let or_motive = d.kernel().lam(anon, or_ty, lt_ty, BinderInfo::Default);
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let lt_ba = d.apply(
                    or_rec,
                    &[
                        lt_ty,
                        eq_ba_ty,
                        or_motive,
                        left_branch,
                        right_branch,
                        disjunction,
                    ],
                );

                let h_ab = d.lemma(p.ble_eq_false_of_lt, &[a, b, lt_ba]);
                selector_sum_from_values(d, a, b, false_, h_ab, true_, h_ba)
            },
        );

        let proof = d.lam_fv(ne_fv, ne_ty, body);
        let stmt = d.arrow(ne_ty, goal);
        (stmt, proof)
    })?;

    Ok(())
}

// ---------------------------------------------------------------------------
// `Nat.eisenstein_floor_sum`.
// ---------------------------------------------------------------------------

/// `fun y => ble (mul pp (succ y)) bound` — one ROW's predicate, in exactly
/// the shape `Nat.countRange_mul_succ_le_eq_floor` is stated at.
fn row_predicate(d: &mut NatDev<'_>, pp: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let sy = d.succ(y);
    let prod = d.mul(pp, sy);
    let body = d.ble(prod, bound);
    d.lam_fv(y_fv, nat, body)
}

/// `Nat.eisenstein_floor_sum` — see this module's doc for the statement and
/// for the three ways it restates ADR-1260's step 1.
///
/// The assembly, in the order the terms are built:
///
/// 1. `Nat.countRectangle_partition` at `Q x y := ble (p·(y+1)) (q·(x+1))`
///    and `R x y := ble (q·(x+1)) (p·(y+1))`, whose per-point hypothesis is
///    [`declare_ble_select_add_of_ne`] fed
///    `Nat.mul_succ_ne_mul_succ_of_coprime` — the coprimality side condition
///    (ADR-1540) — at `Lt (succ x) pp`, which `lt_of_le_of_lt` gets from
///    `Lt x m` (definitionally `Le (succ x) m`) and the theorem's `Lt m pp`.
/// 2. `Nat.countRange_mul_succ_le_eq_floor` (ADR-1290) twice, once per axis,
///    lifted across the outer sum by `Nat.sumRange_congr_lt`. The row bound
///    is `mul q (succ x)` and the column bound `mul pp (succ y)`; both
///    instantiations are the floor lemma verbatim, with no congruence step
///    between the predicate this file builds and the one it is stated at.
/// 3. One `congr` per summand to rewrite the partition's counting form into
///    the floor form, then `trans`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
fn declare_eisenstein_floor_sum(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.eisenstein_floor_sum, 4, &|d, v| {
        let (ap, aq, m, n) = (v[0], v[1], v[2], v[3]);
        let nat = d.nat_ty();

        let pp = d.succ(ap);
        let q = d.succ(aq);

        let one = d.num(1);
        let g = d.gcd(pp, q);
        let cop_ty = d.eq(g, one);
        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);

        let bound_ty = d.lt(m, pp);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        // --- the two predicates ------------------------------------------
        // `Q x y := ble (mul pp (succ y)) (mul q (succ x))`.
        let qq = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let sx = d.succ(x);
            let sy = d.succ(y);
            let left = d.mul(pp, sy);
            let right = d.mul(q, sx);
            let body = d.ble(left, right);
            let inner = d.lam_fv(y_fv, nat, body);
            d.lam_fv(x_fv, nat, inner)
        };
        // `R x y := ble (mul q (succ x)) (mul pp (succ y))`.
        let rr = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let sx = d.succ(x);
            let sy = d.succ(y);
            let left = d.mul(q, sx);
            let right = d.mul(pp, sy);
            let body = d.ble(left, right);
            let inner = d.lam_fv(y_fv, nat, body);
            d.lam_fv(x_fv, nat, inner)
        };

        // --- the per-point hypothesis -------------------------------------
        let hc = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hx_ty = d.lt(x, m);
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let hy_ty = d.lt(y, n);
            let hy_fv = d.fresh_fvar();

            let sx = d.succ(x);
            let sy = d.succ(y);
            // `Lt (succ x) pp` — `Lt x m` is `Le (succ x) m` definitionally.
            let sx_lt_pp = d.lemma(p.lt_of_le_of_lt, &[sx, m, pp, hx, bound]);
            let ne = d.lemma(
                p.mul_succ_ne_mul_succ_of_coprime,
                &[pp, q, x, y, cop, sx_lt_pp],
            );
            let left = d.mul(pp, sy);
            let right = d.mul(q, sx);
            let witness = d.lemma(p.ble_select_add_of_ne, &[left, right, ne]);

            let with_hy = d.lam_fv(hy_fv, hy_ty, witness);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_hy);
            let over_y = d.lam_fv(y_fv, nat, with_hx);
            d.lam_fv(x_fv, nat, over_y)
        };

        let partition = d.lemma(p.count_rectangle_partition, &[qq, rr, m, n, hc]);

        // --- the four aggregates ------------------------------------------
        // `fun x => countRange (fun y => ble (pp*(y+1)) (q*(x+1))) n`.
        let count_rows = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let bnd = d.mul(q, sx);
            let pred = row_predicate(d, pp, bnd);
            let body = count_range(d, &p, pred, n);
            d.lam_fv(x_fv, nat, body)
        };
        // `fun y => countRange (fun x => ble (q*(x+1)) (pp*(y+1))) m`.
        let count_cols = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let sy = d.succ(y);
            let bnd = d.mul(pp, sy);
            let pred = row_predicate(d, q, bnd);
            let body = count_range(d, &p, pred, m);
            d.lam_fv(y_fv, nat, body)
        };
        // `fun x => Min.min n (div (mul q (succ x)) pp)`.
        let floor_rows = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let bnd = d.mul(q, sx);
            let quotient = d.div(bnd, pp);
            let body = min_of(d, &p, n, quotient);
            d.lam_fv(x_fv, nat, body)
        };
        // `fun y => Min.min m (div (mul pp (succ y)) q)`.
        let floor_cols = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let sy = d.succ(y);
            let bnd = d.mul(pp, sy);
            let quotient = d.div(bnd, q);
            let body = min_of(d, &p, m, quotient);
            d.lam_fv(y_fv, nat, body)
        };

        let sum_count_rows = d.sum_range(count_rows, m);
        let sum_count_cols = d.sum_range(count_cols, n);
        let sum_floor_rows = d.sum_range(floor_rows, m);
        let sum_floor_cols = d.sum_range(floor_cols, n);

        // --- the floor lemma on each axis ---------------------------------
        let pointwise_rows = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_ty = d.lt(x, m);
            let hx_fv = d.fresh_fvar();
            let sx = d.succ(x);
            let bnd = d.mul(q, sx);
            let step = d.lemma(p.count_range_mul_succ_le_eq_floor, &[ap, bnd, n]);
            let with_hx = d.lam_fv(hx_fv, hx_ty, step);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let rows_eq = d.lemma(
            p.sum_range_congr_lt,
            &[count_rows, floor_rows, m, pointwise_rows],
        );

        let pointwise_cols = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hy_ty = d.lt(y, n);
            let hy_fv = d.fresh_fvar();
            let sy = d.succ(y);
            let bnd = d.mul(pp, sy);
            let step = d.lemma(p.count_range_mul_succ_le_eq_floor, &[aq, bnd, m]);
            let with_hy = d.lam_fv(hy_fv, hy_ty, step);
            d.lam_fv(y_fv, nat, with_hy)
        };
        let cols_eq = d.lemma(
            p.sum_range_congr_lt,
            &[count_cols, floor_cols, n, pointwise_cols],
        );

        // --- assemble ------------------------------------------------------
        let floor_lhs = d.add(sum_floor_rows, sum_floor_cols);
        let mixed = d.add(sum_count_rows, sum_floor_cols);
        let count_lhs = d.add(sum_count_rows, sum_count_cols);
        let rhs = d.mul(n, m);

        let back_rows = d.symm(sum_count_rows, sum_floor_rows, rows_eq);
        let step_one = d.congr(sum_floor_rows, sum_count_rows, back_rows, &|d, t| {
            d.add(t, sum_floor_cols)
        });
        let back_cols = d.symm(sum_count_cols, sum_floor_cols, cols_eq);
        let step_two = d.congr(sum_floor_cols, sum_count_cols, back_cols, &|d, t| {
            d.add(sum_count_rows, t)
        });

        let (_end, body) = d.chain(
            floor_lhs,
            &[(mixed, step_one), (count_lhs, step_two), (rhs, partition)],
        );

        let proof = d.lam_fv(bound_fv, bound_ty, body);
        let proof = d.lam_fv(cop_fv, cop_ty, proof);

        let concl = d.eq(floor_lhs, rhs);
        let stmt = d.arrow(bound_ty, concl);
        let stmt = d.arrow(cop_ty, stmt);
        (stmt, proof)
    })?;

    Ok(())
}

// ---------------------------------------------------------------------------
// Build order.
// ---------------------------------------------------------------------------

/// Declare everything this module owns, in dependency order.
///
/// Must run after `Nat.countRectangle_partition` (`lattice_count.rs`),
/// `Nat.countRange_mul_succ_le_eq_floor` (`floor_count.rs`) and
/// `Nat.mul_succ_ne_mul_succ_of_coprime` (`eisenstein_side.rs`).
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_eisenstein_lattice_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_ble_select_add_of_ne(d, p)?;
    declare_eisenstein_floor_sum(d, p)?;
    Ok(())
}
