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
            let h_zero = d.lemma(p.sum_range_const_zero, &[n]);

            let start = d.sum_range(cols0, n);
            let mid = d.sum_range(zero_fn, n);
            let zero_end = d.zero();
            let (_e, forward) = d.chain(start, &[(mid, h_congr), (zero_end, h_zero)]);
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
    Ok(())
}
