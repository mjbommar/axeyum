//! Counting a rectangle of lattice points, without a set of lattice points.
//!
//! # What this is for
//!
//! Eisenstein's route to the law of quadratic reciprocity counts the lattice
//! points of the rectangle `[1,m] x [1,n]` (with `m = (p-1)/2`, `n = (q-1)/2`)
//! two ways: row by row below the line `p*y = q*x`, and column by column
//! above it. The classical write-up treats `{(x,y) : 1<=x<=m, 1<=y<=n}` as a
//! SET and partitions it.
//!
//! This kernel has no `Finset`, no `List` and no `Prod`, and
//! `docs/research/09-decisions/adr-1135-…` measured that absence as the wall
//! the determinant's multiplicativity runs into (Leibniz over permutations,
//! Cauchy-Binet over functions `[0,n) -> [0,n)`). The question this module
//! answers is whether Eisenstein hits the same wall.
//!
//! **It does not.** A finite family here is a function plus a bound, and the
//! rectangle argument never needs the set of lattice points as an object: it
//! needs a DOUBLE `sumRange`, a `countRange` on the inside, and a pointwise
//! trichotomy. All three are expressible. What was missing was the Fubini
//! swap over `Nat` -- `Rat.sumRange_swap` has existed since the Laplace
//! expansion work, `Nat.sumRange_swap` did not -- and the bridge identifying
//! `countRange` with the `sumRange` of its own selector.
//!
//! # What is declared
//!
//! - [`declare_sum_range_const`] -- `Nat.sumRange_const : ∀ c n,
//!   sumRange (fun _ => c) n = mul c n`. The orientation is forced:
//!   `Nat.mul` recurses on its RIGHT argument, so `mul c (succ j)` reduces to
//!   `add (mul c j) c`, which is exactly `sumRange (fun _ => c) (succ j)`'s
//!   own reduct. `mul n c` would need a commutation step that buys nothing.
//! - [`declare_count_range_eq_sum_range`] -- `Nat.countRange_eq_sumRange :
//!   ∀ f n, countRange f n = sumRange (fun k => bool_select_nat (f k) 1 0) n`,
//!   by `Eq.refl`. `Nat.countRange` (`totient.rs`) and `Nat.sumRange`
//!   (`defs.rs`) are the SAME `Nat.rec`, base `zero` and step
//!   `fun j ih => add ih (g j)`, differing only in what `g` is -- so the
//!   bridge is free, and stating it by name is what lets a proof move
//!   between the counting and the summing worlds.
//! - [`declare_sum_range_swap`] -- `Nat.sumRange_swap : ∀ F m n,
//!   sumRange (fun i => sumRange (fun j => F i j) n) m
//!     = sumRange (fun j => sumRange (fun i => F i j) m) n`. Fubini over ℕ,
//!   by induction on the OUTER bound `m` with `n` held fixed.
//! - [`declare_count_rectangle_partition`] -- the headline:
//!
//!   ```text
//!   Nat.countRectangle_partition : ∀ Q R m n,
//!     (∀ x y, Lt x m → Lt y n →
//!        add (bool_select_nat (Q x y) 1 0) (bool_select_nat (R x y) 1 0) = 1) →
//!     add (sumRange (fun x => countRange (fun y => Q x y) n) m)
//!         (sumRange (fun y => countRange (fun x => R x y) m) n)
//!       = mul n m
//!   ```
//!
//! # Why the hypothesis is a pair of predicates and not `setCompl`
//!
//! `Nat.countRange_compl` (`finite_set.rs`) already gives
//! `countRange p n + countRange (setCompl p) n = n`, and stating the
//! partition over `Q` and `setCompl Q` would need no hypothesis at all. That
//! form is unusable by the consumer this module exists for. Eisenstein's two
//! predicates are `p*(y+1) < q*(x+1)` and `q*(x+1) < p*(y+1)` -- two STRICT
//! inequalities, complementary only because no lattice point sits on the line
//! `p*y = q*x`, which is true only for `1 <= x <= (p-1)/2`, `1 <= y <= (q-1)/2`
//! and distinct primes `p`, `q`. Forcing the consumer to prove `R = setCompl Q`
//! would ask it for a `Bool` equation it cannot have unconditionally.
//!
//! So the complementarity arrives as a BOUNDED hypothesis on the selectors,
//! which a consumer discharges by one `Bool` case split per point, and the
//! side condition (`p*y ≠ q*x`) stays where it belongs -- in the consumer.
//!
//! # What this module does NOT do
//!
//! It proves no arithmetic. The partition is pure counting: no primality, no
//! division, no `Nat.div` and no `Nat.mod` appear anywhere in it. Identifying
//! the row count `#{y < n : p*(y+1) < q*(x+1)}` with the floor `q*(x+1)/p`,
//! and Eisenstein's lemma relating `Nat.gaussNegCount` to a sum of floors mod
//! 2, are separate and are NOT proved here. See ADR-1260.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Local devices.
// ---------------------------------------------------------------------------

/// `countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `bool_select_nat b 1 0` — `countRange`'s per-index contribution.
fn sel(d: &mut NatDev<'_>, b: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    d.bool_select_nat(b, one, zero)
}

/// `fun _ : Nat => c`.
fn const_fn(d: &mut NatDev<'_>, c: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    d.lam_fv(k_fv, nat, c)
}

/// `fun i => add (f i) (g i)` — the summand shape `Nat.sumRange_add` is
/// stated at, rebuilt here so a chain can name it as a target.
fn combined_fn(d: &mut NatDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = d.add(fi, gi);
    d.lam_fv(i_fv, nat, body)
}

/// `fun j => F i j`, one ROW of a doubly-indexed family.
fn row_inner(d: &mut NatDev<'_>, ff: ExprId, i: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let body = d.apply(ff, &[i, j]);
    d.lam_fv(j_fv, nat, body)
}

/// `fun i => F i j`, one COLUMN of a doubly-indexed family.
fn col_inner(d: &mut NatDev<'_>, ff: ExprId, j: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.apply(ff, &[i, j]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => sumRange (fun j => F i j) n` — the row sums.
fn row_sum_fn(d: &mut NatDev<'_>, ff: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = row_inner(d, ff, i);
    let s = d.sum_range(inner, n);
    d.lam_fv(i_fv, nat, s)
}

/// `fun j => sumRange (fun i => F i j) m` — the column sums.
fn col_sum_fn(d: &mut NatDev<'_>, ff: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let inner = col_inner(d, ff, j);
    let s = d.sum_range(inner, m);
    d.lam_fv(j_fv, nat, s)
}

/// `Nat → Nat → Nat` — the type of a doubly-indexed `Nat` family.
fn family_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let inner = d.arrow(nat, nat);
    d.arrow(nat, inner)
}

/// `Nat → Nat → Bool` — the type of a doubly-indexed predicate.
fn pred2_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let inner = d.arrow(nat, bool_ty);
    d.arrow(nat, inner)
}

/// `fun x y => bool_select_nat (Q x y) 1 0` — a `Bool` family's selector
/// family, the `Nat`-valued object `Nat.sumRange_swap` consumes.
fn sel_family(d: &mut NatDev<'_>, qq: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let b = d.apply(qq, &[x, y]);
    let s = sel(d, b);
    let inner = d.lam_fv(y_fv, nat, s);
    d.lam_fv(x_fv, nat, inner)
}

// ---------------------------------------------------------------------------
// `Nat.sumRange_const`.
// ---------------------------------------------------------------------------

/// `Nat.sumRange_const : ∀ c n, sumRange (fun _ => c) n = mul c n`.
///
/// Induction on `n`. The step is a single congruence: both sides reduce to
/// `add _ c` by their own ι-rules (`sumRange`'s, and `Nat.mul`'s — which
/// recurses on its RIGHT argument, so `mul c (succ j) ≡ add (mul c j) c`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_sum_range_const(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let _p = *p;
    d.theorem(p.sum_range_const, 2, &|d, v| {
        let (c, n) = (v[0], v[1]);
        let f = const_fn(d, c);
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let lhs = d.sum_range(f, x);
            let rhs = d.mul(c, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let sum_j = d.sum_range(f, j);
                let mul_j = d.mul(c, j);
                d.congr(sum_j, mul_j, ih, &|d, t| d.add(t, c))
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Nat.countRange_eq_sumRange`.
// ---------------------------------------------------------------------------

/// `Nat.countRange_eq_sumRange : ∀ f n,
///   countRange f n = sumRange (fun k => bool_select_nat (f k) 1 0) n`.
///
/// `Eq.refl`. Both sides are the same `Nat.rec` — see this module's doc.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_range_eq_sum_range(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let selector = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = sel(d, fk);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = count_range(d, &p, f, n);
    let rhs = d.sum_range(selector, n);
    let stmt = d.eq(lhs, rhs);
    let proof = d.refl(lhs);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, pred_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    d.declare_theorem(p.count_range_eq_sum_range, ty, value)
}

// ---------------------------------------------------------------------------
// `Nat.sumRange_swap`.
// ---------------------------------------------------------------------------

/// `Nat.sumRange_swap : ∀ F m n,
///   sumRange (fun i => sumRange (fun j => F i j) n) m
///     = sumRange (fun j => sumRange (fun i => F i j) m) n`.
///
/// Fubini over ℕ, by induction on the OUTER bound `m` with `n` held fixed.
///
/// The base case is not `refl`: the left side reduces to `zero` on its own,
/// but the right side is `sumRange (fun j => sumRange (col j) zero) n` — a sum
/// of `n` zeros, which needs [`NatPrelude::sum_range_const_zero`] after a
/// pointwise congruence collapses each inner sum.
///
/// The step case is one congruence by the induction hypothesis followed by
/// `Nat.sumRange_add` read backwards: peeling `i = j` off the outer sum leaves
/// `Σ_j (Σ_{i<j} F i j) + Σ_j F j j`… no — leaves
/// `(Σ_{j<n} Σ_{i<k} F i j) + (Σ_{j<n} F k j)`, and `sumRange_add` fuses those
/// two into `Σ_{j<n} (Σ_{i<k} F i j + F k j)`, which is `Σ_{j<n} Σ_{i<succ k}`
/// by `sumRange`'s own ι-rule.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_sum_range_swap(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fam_ty = family_ty(d);

    let ff_fv = d.fresh_fvar();
    let ff = d.kernel().fvar(ff_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let rows = row_sum_fn(d, ff, n);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.sum_range(rows, x);
        let cols = col_sum_fn(d, ff, x);
        let rhs = d.sum_range(cols, n);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // Right side at `x := zero`: every inner sum is empty.
            let zero = d.zero();
            let cols0 = col_sum_fn(d, ff, zero);
            let zero_fn = {
                let z = d.zero();
                const_fn(d, z)
            };
            let pointwise = {
                let j_fv = d.fresh_fvar();
                let z = d.zero();
                let body = d.refl(z);
                d.lam_fv(j_fv, nat, body)
            };
            let h_congr = d.lemma(p.sum_range_congr, &[cols0, zero_fn, n, pointwise]);
            // `Nat.sumRange_const_zero` says exactly this, but it lives in
            // `binary.rs` and is declared LATER in the build order than this
            // module; routing through `sumRange_const` (declared just above)
            // plus `zero_mul` keeps this module's dependencies behind it.
            let zero_c = d.zero();
            let h_const = d.lemma(p.sum_range_const, &[zero_c, n]);
            let mul_zero_n = d.mul(zero_c, n);
            let h_zero = d.lemma(p.zero_mul, &[n]);

            let start = d.sum_range(cols0, n);
            let mid = d.sum_range(zero_fn, n);
            let zero_end = d.zero();
            let (_e, forward) = d.chain(
                start,
                &[(mid, h_congr), (mul_zero_n, h_const), (zero_end, h_zero)],
            );
            // `Eq zero (sumRange cols0 n)`, and `zero` is `sumRange rows zero`.
            d.symm(start, zero_end, forward)
        },
        &|d, k, ih| {
            let cols_k = col_sum_fn(d, ff, k);
            let sum_rows_k = d.sum_range(rows, k);
            let sum_cols_k = d.sum_range(cols_k, n);
            let row_k = row_inner(d, ff, k);
            let sum_row_k = d.sum_range(row_k, n);

            // `sumRange rows (succ k)` ≡ `add (sumRange rows k) (rows k)`
            // ≡ `add sum_rows_k sum_row_k` (β).
            let start = d.add(sum_rows_k, sum_row_k);
            let mid = d.add(sum_cols_k, sum_row_k);
            let h1 = d.congr(sum_rows_k, sum_cols_k, ih, &|d, t| d.add(t, sum_row_k));

            // `sumRange_add cols_k row_k n` fuses the two sums.
            let fused_fn = combined_fn(d, cols_k, row_k);
            let fused = d.sum_range(fused_fn, n);
            let h_add = d.lemma(p.sum_range_add, &[cols_k, row_k, n]);
            let h2 = d.symm(fused, mid, h_add);

            // `fused` is defeq `sumRange (col_sum_fn ff (succ k)) n`.
            let sk = d.succ(k);
            let cols_sk = col_sum_fn(d, ff, sk);
            let target = d.sum_range(cols_sk, n);
            let h3 = d.refl(fused);

            let (_e, chained) = d.chain(start, &[(mid, h1), (fused, h2), (target, h3)]);
            chained
        },
        m,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(ff_fv, fam_ty, with_m)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(ff_fv, fam_ty, with_m)
    };
    d.declare_theorem(p.sum_range_swap, ty, value)
}

// ---------------------------------------------------------------------------
// `Nat.countRectangle_partition`.
// ---------------------------------------------------------------------------

/// `∀ x, Lt x m → Eq (add (countRange (Q x ·) n) (countRange (R x ·) n)) n`
/// — one ROW of the rectangle: the two counts partition its `n` cells.
///
/// Built from the caller's bounded selector hypothesis `hc`, via
/// `countRange_eq_sumRange` on both counts, `sumRange_add` backwards,
/// `sumRange_congr_lt` against the constant `1`, then `sumRange_const` and
/// `one_mul`.
#[allow(clippy::too_many_lines)]
fn row_partition(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    qq: ExprId,
    rr: ExprId,
    m: ExprId,
    n: ExprId,
    hc: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx_ty = d.lt(x, m);
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);

    let q_row = row_inner(d, qq, x);
    let r_row = row_inner(d, rr, x);
    let sel_q = sel_family(d, qq);
    let sel_r = sel_family(d, rr);
    let sel_q_row = row_inner(d, sel_q, x);
    let sel_r_row = row_inner(d, sel_r, x);

    let count_q = count_range(d, &p, q_row, n);
    let count_r = count_range(d, &p, r_row, n);
    let sum_q = d.sum_range(sel_q_row, n);
    let sum_r = d.sum_range(sel_r_row, n);

    let h_q = d.lemma(p.count_range_eq_sum_range, &[q_row, n]);
    let h_r = d.lemma(p.count_range_eq_sum_range, &[r_row, n]);

    let start = d.add(count_q, count_r);
    let step_a = d.add(sum_q, count_r);
    let h_a = d.congr(count_q, sum_q, h_q, &|d, t| d.add(t, count_r));
    let step_b = d.add(sum_q, sum_r);
    let h_b = d.congr(count_r, sum_r, h_r, &|d, t| d.add(sum_q, t));

    let fused_fn = combined_fn(d, sel_q_row, sel_r_row);
    let fused = d.sum_range(fused_fn, n);
    let h_add = d.lemma(p.sum_range_add, &[sel_q_row, sel_r_row, n]);
    let h_c = d.symm(fused, step_b, h_add);

    let one = d.num(1);
    let one_fn = const_fn(d, one);
    let pointwise = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hy_ty = d.lt(y, n);
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv);
        let applied = d.apply(hc, &[x, y, hx, hy]);
        let with_hy = d.lam_fv(hy_fv, hy_ty, applied);
        d.lam_fv(y_fv, nat, with_hy)
    };
    let ones = d.sum_range(one_fn, n);
    let h_d = d.lemma(p.sum_range_congr_lt, &[fused_fn, one_fn, n, pointwise]);

    let mul_one_n = d.mul(one, n);
    let h_e = d.lemma(p.sum_range_const, &[one, n]);
    let h_f = d.lemma(p.one_mul, &[n]);

    let (_e, body) = d.chain(
        start,
        &[
            (step_a, h_a),
            (step_b, h_b),
            (fused, h_c),
            (ones, h_d),
            (mul_one_n, h_e),
            (n, h_f),
        ],
    );

    let with_hx = d.lam_fv(hx_fv, hx_ty, body);
    d.lam_fv(x_fv, nat, with_hx)
}

/// `Nat.countRectangle_partition` — see this module's doc for the statement.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_count_rectangle_partition(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pred_ty = pred2_ty(d);

    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let rr_fv = d.fresh_fvar();
    let rr = d.kernel().fvar(rr_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `∀ x y, Lt x m → Lt y n → add (sel (Q x y)) (sel (R x y)) = 1`.
    let hc_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let qxy = d.apply(qq, &[x, y]);
        let rxy = d.apply(rr, &[x, y]);
        let sq = sel(d, qxy);
        let sr = sel(d, rxy);
        let total = d.add(sq, sr);
        let one = d.num(1);
        let concl = d.eq(total, one);
        let hy = d.lt(y, n);
        let inner = d.arrow(hy, concl);
        let hx = d.lt(x, m);
        let with_hx = d.arrow(hx, inner);
        let over_y = d.pi_fv(y_fv, nat, with_hx);
        d.pi_fv(x_fv, nat, over_y)
    };
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    // The three aggregates.
    let q_rows = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let q_row = row_inner(d, qq, x);
        let body = count_range(d, &p, q_row, n);
        d.lam_fv(x_fv, nat, body)
    };
    let r_rows = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let r_row = row_inner(d, rr, x);
        let body = count_range(d, &p, r_row, n);
        d.lam_fv(x_fv, nat, body)
    };
    let r_cols = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let r_col = col_inner(d, rr, y);
        let body = count_range(d, &p, r_col, m);
        d.lam_fv(y_fv, nat, body)
    };

    let sum_q_rows = d.sum_range(q_rows, m);
    let sum_r_rows = d.sum_range(r_rows, m);
    let sum_r_cols = d.sum_range(r_cols, n);
    let mul_n_m = d.mul(n, m);

    let concl = {
        let total = d.add(sum_q_rows, sum_r_cols);
        d.eq(total, mul_n_m)
    };
    let stmt = d.arrow(hc_ty, concl);

    // --- the proof ---------------------------------------------------------

    // (1) `sumRange r_cols n = sumRange r_rows m`, by Fubini.
    let sel_r = sel_family(d, rr);
    let sel_r_rows = row_sum_fn(d, sel_r, n);
    let sel_r_cols = col_sum_fn(d, sel_r, m);
    let sum_sel_r_rows = d.sum_range(sel_r_rows, m);
    let sum_sel_r_cols = d.sum_range(sel_r_cols, n);

    // `∀ x, Eq (r_rows x) (sel_r_rows x)` — `countRange_eq_sumRange` at each row.
    let pointwise_rows = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let r_row = row_inner(d, rr, x);
        let body = d.lemma(p.count_range_eq_sum_range, &[r_row, n]);
        d.lam_fv(x_fv, nat, body)
    };
    let h_rows = d.lemma(
        p.sum_range_congr,
        &[r_rows, sel_r_rows, m, pointwise_rows],
    );
    let h_swap = d.lemma(p.sum_range_swap, &[sel_r, m, n]);
    // `∀ y, Eq (sel_r_cols y) (r_cols y)` — the same bridge, backwards.
    let pointwise_cols = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let r_col = col_inner(d, rr, y);
        let count_y = count_range(d, &p, r_col, m);
        let sel_r_col = col_inner(d, sel_r, y);
        let sum_y = d.sum_range(sel_r_col, m);
        let fwd = d.lemma(p.count_range_eq_sum_range, &[r_col, m]);
        let body = d.symm(count_y, sum_y, fwd);
        d.lam_fv(y_fv, nat, body)
    };
    let h_cols = d.lemma(
        p.sum_range_congr,
        &[sel_r_cols, r_cols, n, pointwise_cols],
    );
    let (_e, h_fubini) = d.chain(
        sum_r_rows,
        &[
            (sum_sel_r_rows, h_rows),
            (sum_sel_r_cols, h_swap),
            (sum_r_cols, h_cols),
        ],
    );
    // `h_fubini : Eq (sumRange r_rows m) (sumRange r_cols n)`.

    // (2) `add (sumRange q_rows m) (sumRange r_rows m) = mul n m`.
    let fused_fn = combined_fn(d, q_rows, r_rows);
    let fused = d.sum_range(fused_fn, m);
    let h_add = d.lemma(p.sum_range_add, &[q_rows, r_rows, m]);
    let rows_sum = d.add(sum_q_rows, sum_r_rows);
    let h_fuse = d.symm(fused, rows_sum, h_add);

    let n_fn = const_fn(d, n);
    let pointwise_partition = row_partition(d, &p, qq, rr, m, n, hc);
    let ns = d.sum_range(n_fn, m);
    let h_row = d.lemma(
        p.sum_range_congr_lt,
        &[fused_fn, n_fn, m, pointwise_partition],
    );
    let h_const = d.lemma(p.sum_range_const, &[n, m]);

    // (3) assemble.
    let start = d.add(sum_q_rows, sum_r_cols);
    let h_back = {
        let fwd = h_fubini;
        d.symm(sum_r_rows, sum_r_cols, fwd)
    };
    let step_1 = d.add(sum_q_rows, sum_r_rows);
    let h_1 = d.congr(sum_r_cols, sum_r_rows, h_back, &|d, t| {
        d.add(sum_q_rows, t)
    });
    let (_e, body) = d.chain(
        start,
        &[
            (step_1, h_1),
            (fused, h_fuse),
            (ns, h_row),
            (mul_n_m, h_const),
        ],
    );
    let proof = d.lam_fv(hc_fv, hc_ty, body);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        let with_rr = d.pi_fv(rr_fv, pred_ty, with_m);
        d.pi_fv(qq_fv, pred_ty, with_rr)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        let with_rr = d.lam_fv(rr_fv, pred_ty, with_m);
        d.lam_fv(qq_fv, pred_ty, with_rr)
    };
    d.declare_theorem(p.count_rectangle_partition, ty, value)
}

// ---------------------------------------------------------------------------
// `Nat.countRectangle_partition_compl`.
// ---------------------------------------------------------------------------

/// `Nat.countRectangle_partition_compl : ∀ Q m n,
///   add (sumRange (fun x => countRange (fun y => Q x y) n) m)
///       (sumRange (fun y => countRange (setCompl (fun x => Q x y)) m) n)
///     = mul n m`
///
/// [`declare_count_rectangle_partition`] with the second predicate taken to
/// be the complement of the first, so **no hypothesis remains**.
///
/// It exists for two reasons and the second is the load-bearing one:
///
/// 1. It is the form a consumer wants whenever the two halves really are
///    complementary everywhere (as opposed to Eisenstein's, which are
///    complementary only inside the rectangle).
/// 2. **It proves the general theorem's hypothesis is satisfiable.** A
///    theorem whose hypothesis nothing can discharge is vacuous, and no
///    axiom-footprint check, prelude build or inventory sweep can see that.
///    Deriving this corollary constructs an actual inhabitant of that
///    hypothesis inside the kernel, at a genuinely free `Q`.
///
/// The per-point witness is `finite_set::compl_sum_eq`, which was already
/// built there for `Nat.countRange_compl`'s induction step and was private.
/// It is exported rather than re-derived: two proofs of one fact that must
/// stay in sync is exactly the cost this repository keeps paying for
/// re-derivation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_count_rectangle_partition_compl(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pred_ty = pred2_ty(d);

    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `R x y := setCompl (fun x' => Q x' y) x` — the COLUMN complement, so
    // that `fun x => R x y` is `setCompl (fun x' => Q x' y)` up to eta.
    let rr = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let q_col = col_inner(d, qq, y);
        let compl_col = d.const_app(p.set_compl, &[q_col]);
        let body = d.apply(compl_col, &[x]);
        let inner = d.lam_fv(y_fv, nat, body);
        d.lam_fv(x_fv, nat, inner)
    };

    // The hypothesis, discharged pointwise and unconditionally.
    let hc = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hx_ty = d.lt(x, m);
        let hx_fv = d.fresh_fvar();
        let hy_ty = d.lt(y, n);
        let hy_fv = d.fresh_fvar();
        let qxy = d.apply(qq, &[x, y]);
        let witness = super::finite_set::compl_sum_eq(d, &p, qxy);
        let with_hy = d.lam_fv(hy_fv, hy_ty, witness);
        let with_hx = d.lam_fv(hx_fv, hx_ty, with_hy);
        let over_y = d.lam_fv(y_fv, nat, with_hx);
        d.lam_fv(x_fv, nat, over_y)
    };

    let proof = d.lemma(p.count_rectangle_partition, &[qq, rr, m, n, hc]);

    // The statement, spelled with `setCompl` rather than with `R`.
    let q_rows = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let q_row = row_inner(d, qq, x);
        let body = count_range(d, &p, q_row, n);
        d.lam_fv(x_fv, nat, body)
    };
    let compl_cols = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let q_col = col_inner(d, qq, y);
        let compl_col = d.const_app(p.set_compl, &[q_col]);
        let body = count_range(d, &p, compl_col, m);
        d.lam_fv(y_fv, nat, body)
    };
    let lhs = {
        let a = d.sum_range(q_rows, m);
        let b = d.sum_range(compl_cols, n);
        d.add(a, b)
    };
    let rhs = d.mul(n, m);
    let stmt = d.eq(lhs, rhs);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(qq_fv, pred_ty, with_m)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(qq_fv, pred_ty, with_m)
    };
    d.declare_theorem(p.count_rectangle_partition_compl, ty, value)
}

// ---------------------------------------------------------------------------
// Build order.
// ---------------------------------------------------------------------------

/// Declare everything this module owns, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_lattice_count(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_sum_range_const(d, p)?;
    declare_count_range_eq_sum_range(d, p)?;
    declare_sum_range_swap(d, p)?;
    declare_count_rectangle_partition(d, p)?;
    declare_count_rectangle_partition_compl(d, p)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Kernel, build_nat_prelude};

    /// The concrete instance every test below is checked against, recomputed
    /// here in Rust rather than inherited from the ADR's Python. It is a
    /// genuine Eisenstein instance: `p = 5`, `q = 13`, so `m = (p-1)/2 = 2`
    /// and `n = (q-1)/2 = 6`, with the predicate `Q x y := p*(y+1) < q*(x+1)`.
    ///
    /// It is chosen to DISCRIMINATE, and the obvious smaller instance does
    /// not. At `(p, q) = (5, 7)` the row count and the complement column
    /// count are both `3`, so dropping the complement from the second summand
    /// still totals `6 = m*n` and the negative control below would be
    /// vacuous. Here the two are `7` and `5`, and the un-complemented column
    /// count is `7`, so the mutation gives `14` against `12`.
    fn reference() -> (u32, u32, u32, u32, u32) {
        let (p, q) = (5_u32, 13_u32);
        let (m, n) = ((p - 1) / 2, (q - 1) / 2);
        let pred = |x: u32, y: u32| p * (y + 1) < q * (x + 1);
        let count = |f: &dyn Fn(u32) -> bool, bound: u32| -> u32 {
            u32::try_from((0..bound).filter(|&v| f(v)).count()).expect("small")
        };
        let rows: u32 = (0..m).map(|x| count(&|y| pred(x, y), n)).sum();
        let compl_cols: u32 = (0..n).map(|y| count(&|x| !pred(x, y), m)).sum();
        let plain_cols: u32 = (0..n).map(|y| count(&|x| pred(x, y), m)).sum();
        assert_eq!((m, n, rows, compl_cols, plain_cols), (2, 6, 7, 5, 7));
        assert_eq!(rows + compl_cols, n * m);
        // The same two numbers as sums of floors -- this instance IS the
        // classical lattice identity for `(5, 13)`.
        let f1: u32 = (1..=m).map(|x| (q * x) / p).sum();
        let f2: u32 = (1..=n).map(|y| (p * y) / q).sum();
        assert_eq!((f1, f2), (rows, compl_cols));
        (m, n, rows, compl_cols, plain_cols)
    }

    /// `fun x y => ble (succ (mul 5 (succ y))) (mul 13 (succ x))`, i.e.
    /// `5*(y+1) < 13*(x+1)`. Every magnitude formed is at most `31`, well
    /// under the unary-numeral cost cliff.
    fn eisenstein_predicate(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
        let nat = d.nat_ty();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let five = d.num(5);
        let thirteen = d.num(13);
        let sy = d.succ(y);
        let sx = d.succ(x);
        let left = d.mul(five, sy);
        let left = d.succ(left);
        let right = d.mul(thirteen, sx);
        let body = d.const_app(p.ble, &[left, right]);
        let inner = d.lam_fv(y_fv, nat, body);
        d.lam_fv(x_fv, nat, inner)
    }

    #[test]
    fn the_reference_instance_is_what_the_adr_says_it_is() {
        let _ = reference();
    }

    /// The two aggregates the partition names REDUCE, by the kernel's own
    /// iota rules, to the numbers `reference()` computes -- and the negative
    /// control separates the complemented column count from the plain one.
    #[test]
    fn the_rectangle_aggregates_compute_at_the_eisenstein_instance() {
        let (m_ref, n_ref, rows_ref, compl_ref, plain_ref) = reference();
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = NatDev::new(&mut k, p);

        let qq = eisenstein_predicate(&mut d, &p);
        let m = d.num(m_ref);
        let n = d.num(n_ref);
        let nat = d.nat_ty();

        let q_rows = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let row = row_inner(&mut d, qq, x);
            let body = count_range(&mut d, &p, row, n);
            d.lam_fv(x_fv, nat, body)
        };
        let rows = d.sum_range(q_rows, m);
        let rows_expected = d.num(rows_ref);
        assert!(
            d.kernel().def_eq(rows, rows_expected),
            "the row count must reduce to {rows_ref}"
        );

        let compl_cols = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let col = col_inner(&mut d, qq, y);
            let compl = d.const_app(p.set_compl, &[col]);
            let body = count_range(&mut d, &p, compl, m);
            d.lam_fv(y_fv, nat, body)
        };
        let cols = d.sum_range(compl_cols, n);
        let cols_expected = d.num(compl_ref);
        assert!(
            d.kernel().def_eq(cols, cols_expected),
            "the complemented column count must reduce to {compl_ref}"
        );

        let total = d.add(rows, cols);
        let product = d.mul(n, m);
        assert!(
            d.kernel().def_eq(total, product),
            "the partition must hold by computation at this instance"
        );

        // Negative control -- and it is NOT vacuous here, unlike at `(5, 7)`.
        let plain_cols = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let col = col_inner(&mut d, qq, y);
            let body = count_range(&mut d, &p, col, m);
            d.lam_fv(y_fv, nat, body)
        };
        let plain = d.sum_range(plain_cols, n);
        let plain_expected = d.num(plain_ref);
        assert!(
            d.kernel().def_eq(plain, plain_expected),
            "the un-complemented column count must reduce to {plain_ref}"
        );
        let mutated = d.add(rows, plain);
        assert!(
            !d.kernel().def_eq(mutated, product),
            "negative control: dropping the complement must break the identity \
             ({rows_ref} + {plain_ref} against {n_ref} * {m_ref})"
        );
    }

    /// The THEOREM, not merely its statement: instantiate
    /// `Nat.countRectangle_partition_compl` at this concrete predicate and
    /// these bounds, and confirm the kernel INFERS a type whose two sides
    /// both reduce to the reference numbers.
    ///
    /// This is what separates "the declaration was admitted" from "the
    /// declaration says what we think". `Kernel::add_declaration` checked the
    /// proof against the stated type; nothing in that check knows the stated
    /// type is the identity we wanted.
    #[test]
    fn the_partition_theorem_instantiates_at_the_eisenstein_instance() {
        let (m_ref, n_ref, rows_ref, compl_ref, _) = reference();
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = NatDev::new(&mut k, p);

        let qq = eisenstein_predicate(&mut d, &p);
        let m = d.num(m_ref);
        let n = d.num(n_ref);
        let instance = d.lemma(p.count_rectangle_partition_compl, &[qq, m, n]);
        let inferred = d
            .kernel()
            .infer(instance)
            .expect("the instantiated theorem must infer");

        let sum = d.num(rows_ref + compl_ref);
        let product = d.mul(n, m);
        let expected = d.eq(sum, product);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the instantiated theorem must be the identity `{} = {} * {}`",
            rows_ref + compl_ref,
            n_ref,
            m_ref
        );

        // Negative control on the STATEMENT rather than on the aggregates:
        // the same equation with the left side off by one must NOT be what
        // the theorem says. Both sides stay concrete numerals, so this is a
        // cheap failing `def_eq`, not the unbounded kind.
        let off_by_one = d.num(rows_ref + compl_ref + 1);
        let wrong = d.eq(off_by_one, product);
        assert!(
            !d.kernel().def_eq(inferred, wrong),
            "negative control: the theorem must not also assert the shifted identity"
        );
    }

    /// `Nat.sumRange_swap` at an ASYMMETRIC family, with a control showing
    /// the bound order is load-bearing.
    #[test]
    fn sum_range_swap_holds_at_an_asymmetric_family_and_the_bounds_matter() {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = NatDev::new(&mut k, p);

        // `F i j := add (mul 3 i) (mul 5 j)` -- asymmetric in `i`, `j`.
        let ff = {
            let nat = d.nat_ty();
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let three = d.num(3);
            let five = d.num(5);
            let a = d.mul(three, i);
            let b = d.mul(five, j);
            let body = d.add(a, b);
            let inner = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, inner)
        };
        let expect: u32 = (0..2u32)
            .map(|i| (0..3u32).map(|j| 3 * i + 5 * j).sum::<u32>())
            .sum();
        assert_eq!(expect, 39);

        let m = d.num(2);
        let n = d.num(3);
        let rows = row_sum_fn(&mut d, ff, n);
        let lhs = d.sum_range(rows, m);
        let cols = col_sum_fn(&mut d, ff, m);
        let rhs = d.sum_range(cols, n);
        let value = d.num(expect);
        assert!(
            d.kernel().def_eq(lhs, value),
            "the row-major sum must be {expect}"
        );
        assert!(
            d.kernel().def_eq(rhs, value),
            "the column-major sum must be {expect}"
        );

        let thm = d.lemma(p.sum_range_swap, &[ff, m, n]);
        let inferred = d.kernel().infer(thm).expect("the swap must infer");
        let expected = d.eq(lhs, rhs);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the instantiated swap must be exactly the two iterated sums"
        );

        // Negative control: summing column-major with the OUTER bound left at
        // `n` and the inner bound also `n` -- what a proof that swapped the
        // summation order without swapping the bounds would produce.
        let bad: u32 = (0..3u32)
            .map(|j| (0..3u32).map(|i| 3 * i + 5 * j).sum::<u32>())
            .sum();
        assert_ne!(bad, expect, "the control must separate the two bounds");
        let cols_bad = col_sum_fn(&mut d, ff, n);
        let rhs_bad = d.sum_range(cols_bad, n);
        assert!(
            !d.kernel().def_eq(lhs, rhs_bad),
            "negative control: swapping the summation order without swapping \
             the bounds must NOT hold"
        );
    }
}
