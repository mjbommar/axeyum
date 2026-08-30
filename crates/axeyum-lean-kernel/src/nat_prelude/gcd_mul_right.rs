//! `Nat.gcd_mul_right : ∀ a b c, gcd (a*c) (b*c) = gcd a b * c`.
//!
//! This is the distributive law that blocks three `ml430` mirrors
//! (`F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`,
//! `F:ml430-nat-dvd-gcd-mul-gcd-iff-dvd-mul-07fec722`,
//! `F:ml430-nat-dvd-mul-gcd-iff-dvd-mul-f9517e6b`), all of which reduce to it
//! plus already-proved gcd/divisibility algebra (`docs/plan/status/331-nat-gcd-dvd-mirrors.md`).
//! It genuinely does not exist anywhere in this development: neither
//! `nat_prelude/gcd.rs` nor `nat_prelude/lcm_gcd_lemmas.rs` declares a
//! `gcd_mul_*` distributive law under any spelling, and
//! `int_prelude/gcd.rs`'s own module doc (around its `Int.gcd_div`
//! construction) says so explicitly: "`Nat.gcd_mul_left`/`gcd_mul_right`...
//! neither exists in this development, and building either would need a
//! fresh strong-induction principle over `Nat.gcd`'s well-founded
//! recursion". `Int.gcd_mul_right` (the coprimality-descent pair in that
//! same file, around `declare_gcd_eq_one_of_gcd_mul_right_eq_one`) is an
//! unrelated proposition that happens to share the Mathlib name.
//!
//! # Strategy
//!
//! Well-founded induction on the first argument `a`, mirroring `gcd`'s own
//! Euclidean recursion exactly the way `declare_gcd_bezout` mirrors it for
//! Bézout witnesses (`nat_prelude/bezout.rs`) -- same relation
//! (`lt_well_founded`), same `family`/`step_motive`/`step` scaffolding, same
//! trick of using an ordinary `Nat.rec` purely to case-split on `a` while the
//! genuine induction hypothesis comes from the well-founded `recursive`
//! parameter.
//!
//! The row being proved for a fixed first argument `m` is
//! `row(m) := ∀ b c, gcd (m*c) (b*c) = gcd m b * c`.
//!
//! - **Base case `m = 0`.** Both sides reduce to `b*c` via `zero_mul` +
//!   `gcd_zero_left` (`gcd 0 x = x`).
//! - **Step case `m = succ predecessor =: M`.** Case-split on `c`:
//!   - `c = 0`: both sides are `0` via `mul_zero` + `gcd_zero_left`.
//!   - `c = succ _ =: C` (both `M` and `C` positive): `M*C` is positive, so
//!     `gcd_unfold_pos` gives `gcd(M*C, b*C) = gcd(mod(b*C, M*C), M*C)`,
//!     generalizing `gcd_succ` (which needs its first argument literally of
//!     shape `succ _`) the same way `div_mod_reconstructed` generalizes
//!     `div_mod_exec`. The scaling lemma `mul_mod_mul_right_eq` rewrites
//!     `mod(b*C, M*C)` to `(mod b M)*C`, landing on
//!     `gcd(M*C, b*C) = gcd((mod b M)*C, M*C)`. The right-hand side is
//!     exactly `row(mod b M)` instantiated at `(b, c) := (M, C)`, which the
//!     well-founded hypothesis `recursive` supplies directly (`mod b M < M`
//!     via `mod_lt`), giving
//!     `gcd(M*C, b*C) = mul(gcd(mod b M, M), C)`. Finally `gcd_succ`
//!     identifies `gcd(mod b M, M)` with `gcd(M, b)`, closing the goal.
//!
//! # The scaling lemma
//!
//! `mul_mod_mul_right_eq` proves, for POSITIVE `m` (`pos_m : Lt zero m`)
//! and arbitrary `n`, `c`: `mod(n*c, m*c) = (mod n m) * c`. Case-split on `c`:
//! `c = 0` is trivial (`mul_zero` on both sides); `c = succ _ =: C` reuses
//! `div_mod_reconstructed`'s canonical decomposition `n = m*q + r`, `r < m`,
//! scales it by `C` (`right_distrib` + `mul_assoc`/`mul_comm` to regroup
//! `(m*q)*C` into `(m*C)*q`, `mul_lt_mul_right` for `r*C < m*C`) into a
//! second valid `divMod (m*C) (n*C) q (r*C)` decomposition, and
//! `div_mod_unique` against the canonical decomposition of `n*C` at `m*C`
//! forces `r*C = mod(n*C, m*C)` -- which, since `r` IS `mod n m`, is the
//! goal.

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_reverse};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// Reconstruct `divMod dd x (div x dd) (mod x dd)` for arbitrary `x`, given
/// `pos_dd : Lt zero dd`. A local copy of the pattern established in
/// `mod_mul_lemmas.rs` (itself copied from `div_mod_lemmas.rs`/`group.rs`/
/// `base_induction.rs`) -- see `mod_mul_lemmas.rs`'s module doc for why this
/// is a per-file copy rather than a shared export.
fn div_mod_reconstructed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    pos_dd: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let succ_pred_witness = d.lemma(p.succ_pred_of_pos, &[dd]);
    let dd_eq_succ_pred = d.apply(succ_pred_witness, &[pos_dd]); // dd = succ (pred dd)
    let pred_dd = d.pred(dd);
    let succ_pred_dd = d.succ(pred_dd);
    let exec = d.lemma(p.div_mod_exec, &[pred_dd, x]); // divMod (succ pred_dd) x (div x (succ pred_dd)) (mod x (succ pred_dd))

    let motive = d.eq_motive(succ_pred_dd, &|d, y| {
        let q = d.div(x, y);
        let r = d.modulo(x, y);
        d.div_mod(y, x, q, r)
    });
    let eq_rev = d.symm(dd, succ_pred_dd, dd_eq_succ_pred); // succ_pred_dd = dd
    d.transport(succ_pred_dd, motive, exec, dd, eq_rev)
}

/// `Eq (gcd x y) (gcd (mod y x) x)` for arbitrary POSITIVE `x`
/// (`pos_x : Lt zero x`), generalizing `gcd_succ` (which needs `x` literally
/// of shape `succ _`) the same way `div_mod_reconstructed` generalizes
/// `div_mod_exec`: rewrite `x` to `succ (pred x)` via `succ_pred_of_pos`,
/// apply `gcd_succ` there, and transport back along the reverse equation.
fn gcd_unfold_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    pos_x: ExprId,
    y: ExprId,
) -> ExprId {
    let p = *p;
    let succ_pred_witness = d.lemma(p.succ_pred_of_pos, &[x]);
    let x_eq_succ_pred = d.apply(succ_pred_witness, &[pos_x]); // x = succ (pred x)
    let pred_x = d.pred(x);
    let succ_pred_x = d.succ(pred_x);
    let gcd_succ_eq = d.lemma(p.gcd_succ, &[pred_x, y]); // gcd(succ pred_x, y) = gcd(mod y (succ pred_x), succ pred_x)

    let motive = d.eq_motive(succ_pred_x, &|d, z| {
        let lhs = d.gcd(z, y);
        let remainder = d.modulo(y, z);
        let rhs = d.gcd(remainder, z);
        d.eq(lhs, rhs)
    });
    let eq_rev = d.symm(x, succ_pred_x, x_eq_succ_pred); // succ_pred_x = x
    d.transport(succ_pred_x, motive, gcd_succ_eq, x, eq_rev)
}

/// `Eq (mod (mul n c) (mul m c)) (mul (mod n m) c)`, given `pos_m : Lt zero
/// m`. See the module doc for the derivation. Case-splits only on `c`
/// (`m`'s positivity is a hypothesis, not case-split away).
fn mul_mod_mul_right_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    m: ExprId,
    pos_m: ExprId,
    c: ExprId,
) -> ExprId {
    let p = *p;

    let motive_c = |d: &mut NatDev<'_>, cc: ExprId| -> ExprId {
        let mc = d.mul(m, cc);
        let nc = d.mul(n, cc);
        let lhs = d.modulo(nc, mc);
        let rm = d.modulo(n, m);
        let rhs = d.mul(rm, cc);
        d.eq(lhs, rhs)
    };

    let at_zero_c = |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let mc0 = d.mul(m, zero);
        let nc0 = d.mul(n, zero);
        let lhs0 = d.modulo(nc0, mc0);

        let mul_m_zero = d.lemma(p.mul_zero, &[m]); // mul m zero = zero
        let lhs_step1 = d.congr(mc0, zero, mul_m_zero, &|d, v| d.modulo(nc0, v));
        let mod_nc0_zero = d.modulo(nc0, zero);
        let mod_zero_nc0 = d.lemma(p.mod_zero, &[nc0]); // mod nc0 zero = nc0
        let mul_n_zero = d.lemma(p.mul_zero, &[n]); // mul n zero = zero
        let (_, lhs_eq) = d.chain(
            lhs0,
            &[
                (mod_nc0_zero, lhs_step1),
                (nc0, mod_zero_nc0),
                (zero, mul_n_zero),
            ],
        );

        let rm0 = d.modulo(n, m);
        let rhs0 = d.mul(rm0, zero);
        let mul_rm0_zero = d.lemma(p.mul_zero, &[rm0]); // mul rm0 zero = zero
        let (_, rhs_eq) = d.chain(rhs0, &[(zero, mul_rm0_zero)]);

        let zero_eq_rhs = d.symm(rhs0, zero, rhs_eq);
        d.trans(lhs0, zero, rhs0, lhs_eq, zero_eq_rhs)
    };

    let at_succ_c = |d: &mut NatDev<'_>, c_pred: ExprId| -> ExprId {
        let big_c = d.succ(c_pred);
        let pos_c = d.zero_lt_succ(c_pred);

        // Canonical decomposition of n at m: n = m*q + r, r < m.
        let q = d.div(n, m);
        let r = d.modulo(n, m);
        let relation1 = div_mod_reconstructed(d, &p, m, pos_m, n);
        let eq1_ty = {
            let product = d.mul(m, q);
            let reconstructed = d.add(product, r);
            d.eq(n, reconstructed)
        };
        let bound1_ty = d.lt(r, m);
        let eq1 = and_left(d, eq1_ty, bound1_ty, relation1);
        let bound1 = and_right(d, eq1_ty, bound1_ty, relation1);

        // Scale: n*C = (m*q + r)*C = (m*q)*C + r*C = (m*C)*q + r*C.
        let m_q = d.mul(m, q);
        let reconstructed = d.add(m_q, r);
        let n_c = d.mul(n, big_c);
        let reconstructed_c = d.mul(reconstructed, big_c);
        let step1 = d.congr(n, reconstructed, eq1, &|d, v| d.mul(v, big_c));

        let m_q_c = d.mul(m_q, big_c);
        let r_c = d.mul(r, big_c);
        let mq_c_plus_rc = d.add(m_q_c, r_c);
        let distrib = d.lemma(p.right_distrib, &[m_q, r, big_c]); // (m*q+r)*C = (m*q)*C + r*C

        let q_c = d.mul(q, big_c);
        let c_q = d.mul(big_c, q);
        let m_c = d.mul(m, big_c);
        let mc_q = d.mul(m_c, q);

        let assoc1 = d.lemma(p.mul_assoc, &[m, q, big_c]); // (m*q)*C = m*(q*C)
        let m_qc = d.mul(m, q_c);
        let comm1 = d.lemma(p.mul_comm, &[q, big_c]); // q*C = C*q
        let step_comm = d.congr(q_c, c_q, comm1, &|d, v| d.mul(m, v));
        let m_cq = d.mul(m, c_q);
        let assoc2 = d.lemma(p.mul_assoc, &[m, big_c, q]); // (m*C)*q = m*(C*q)
        let step_assoc2_rev = d.symm(mc_q, m_cq, assoc2);

        let (_, mqc_eq_mcq) = d.chain(
            m_q_c,
            &[(m_qc, assoc1), (m_cq, step_comm), (mc_q, step_assoc2_rev)],
        );

        let sum_step = d.congr(m_q_c, mc_q, mqc_eq_mcq, &|d, v| d.add(v, r_c));
        let mc_q_plus_rc = d.add(mc_q, r_c);

        let (_, nc_eq_final) = d.chain(
            n_c,
            &[
                (reconstructed_c, step1),
                (mq_c_plus_rc, distrib),
                (mc_q_plus_rc, sum_step),
            ],
        );
        // nc_eq_final : Eq (mul n big_c) (add (mul m_c q) r_c)

        // Bound: r*C < m*C from r < m, C > 0.
        let mlmr_iff = d.lemma(p.mul_lt_mul_right, &[big_c, r, m, pos_c]); // Iff (Lt r*C m*C) (Lt r m)
        let lt_rc_mc = d.lt(r_c, m_c);
        let lt_r_m = d.lt(r, m);
        let reverse_fn = iff_reverse(d, lt_rc_mc, lt_r_m, mlmr_iff);
        let bound_final = d.apply(reverse_fn, &[bound1]);

        // Package as divMod (m*C) (n*C) q (r*C).
        let eq_ty2 = d.eq(n_c, mc_q_plus_rc);
        let relation2 = d.const_app(
            p.logic.and_intro,
            &[eq_ty2, lt_rc_mc, nc_eq_final, bound_final],
        );

        let pos_mc = d.lemma(p.one_le_mul, &[m, big_c, pos_m, pos_c]); // Le one (m*C) ~ Lt zero (m*C)
        let canonical = div_mod_reconstructed(d, &p, m_c, pos_mc, n_c);

        let div_nc_mc = d.div(n_c, m_c);
        let mod_nc_mc = d.modulo(n_c, m_c);
        let both = d.lemma(
            p.div_mod_unique,
            &[m_c, n_c, q, r_c, div_nc_mc, mod_nc_mc, relation2, canonical],
        );

        let q_eq_ty = d.eq(q, div_nc_mc);
        let r_eq_ty = d.eq(r_c, mod_nc_mc);
        let r_eq = and_right(d, q_eq_ty, r_eq_ty, both); // Eq r_c mod_nc_mc
        d.symm(r_c, mod_nc_mc, r_eq) // Eq mod_nc_mc r_c == Eq (mod (n*C)(m*C)) ((mod n m)*C)
    };

    cases_zero_succ(d, c, &motive_c, &at_zero_c, &at_succ_c)
}

/// `Nat.gcd_mul_right : ∀ a b c, Eq (gcd (mul a c) (mul b c)) (mul (gcd a b) c)`.
/// See the module doc for the well-founded induction strategy.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_gcd_mul_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();

    let row = |d: &mut NatDev<'_>, m: ExprId| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lhs = {
            let mc = d.mul(m, c);
            let bc = d.mul(b, c);
            d.gcd(mc, bc)
        };
        let rhs = {
            let g = d.gcd(m, b);
            d.mul(g, c)
        };
        let body = d.eq(lhs, rhs);
        let inner = d.pi_fv(c_fv, nat, body);
        d.pi_fv(b_fv, nat, inner)
    };

    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| -> ExprId {
        let lower_fv = d.fresh_fvar();
        let lower = d.kernel().fvar(lower_fv);
        let related_fv = d.fresh_fvar();
        let related = d.lt(lower, upper);
        let lower_row = row(d, lower);
        let body = d.pi_fv(related_fv, related, lower_row);
        d.pi_fv(lower_fv, nat, body)
    };

    let family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = row(d, m);
        d.lam_fv(m_fv, nat, body)
    };

    let step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = recursive_ty(d, m);
        let result = row(d, m);
        let body = d.arrow(recursive, result);
        d.lam_fv(m_fv, nat, body)
    };

    let zero_minor = {
        let zero = d.zero();
        let recursive_fv = d.fresh_fvar();
        let recursive = recursive_ty(d, zero);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        // gcd(0*c, b*c) = gcd(0, b*c) [zero_mul] = b*c [gcd_zero_left]
        let zero_c = d.mul(zero, c);
        let bc = d.mul(b, c);
        let lhs = d.gcd(zero_c, bc);
        let zero_mul_c = d.lemma(p.zero_mul, &[c]); // mul zero c = zero
        let lhs_step = d.congr(zero_c, zero, zero_mul_c, &|d, v| d.gcd(v, bc));
        let gcd_zero_bc = d.gcd(zero, bc);
        let gcd_zero_bc_eq = d.lemma(p.gcd_zero_left, &[bc]); // gcd 0 (b*c) = b*c
        let (_, lhs_eq) = d.chain(lhs, &[(gcd_zero_bc, lhs_step), (bc, gcd_zero_bc_eq)]);

        // mul(gcd 0 b, c) = mul(b, c)
        let gcd_zero_b = d.gcd(zero, b);
        let rhs = d.mul(gcd_zero_b, c);
        let gcd_zero_b_eq = d.lemma(p.gcd_zero_left, &[b]); // gcd 0 b = b
        let rhs_step = d.congr(gcd_zero_b, b, gcd_zero_b_eq, &|d, v| d.mul(v, c));
        let (_, rhs_eq) = d.chain(rhs, &[(bc, rhs_step)]);

        let bc_eq_rhs = d.symm(rhs, bc, rhs_eq);
        let body = d.trans(lhs, bc, rhs, lhs_eq, bc_eq_rhs);

        let with_c = d.lam_fv(c_fv, nat, body);
        let with_b = d.lam_fv(b_fv, nat, with_c);
        d.lam_fv(recursive_fv, recursive, with_b)
    };

    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let big_m = d.succ(predecessor);
        let ignored_ih_fv = d.fresh_fvar();
        let predecessor_recursive = recursive_ty(d, predecessor);
        let predecessor_row = row(d, predecessor);
        let ignored_ih_ty = d.arrow(predecessor_recursive, predecessor_row);

        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, big_m);

        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        let pos_m = d.zero_lt_succ(predecessor);

        let motive_c = |d: &mut NatDev<'_>, cc: ExprId| -> ExprId {
            let mc = d.mul(big_m, cc);
            let bc = d.mul(b, cc);
            let lhs = d.gcd(mc, bc);
            let g = d.gcd(big_m, b);
            let rhs = d.mul(g, cc);
            d.eq(lhs, rhs)
        };

        let at_zero_c = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let mc0 = d.mul(big_m, zero);
            let bc0 = d.mul(b, zero);
            let lhs0 = d.gcd(mc0, bc0);

            let mul_m_zero = d.lemma(p.mul_zero, &[big_m]); // M*0 = 0
            let step_left = d.congr(mc0, zero, mul_m_zero, &|d, v| d.gcd(v, bc0));
            let gcd_zero_bc0 = d.gcd(zero, bc0);

            let mul_b_zero = d.lemma(p.mul_zero, &[b]); // b*0 = 0
            let step_right = d.congr(bc0, zero, mul_b_zero, &|d, v| d.gcd(zero, v));
            let gcd_zero_zero = d.gcd(zero, zero);

            let gcd_zero_zero_eq = d.lemma(p.gcd_zero_left, &[zero]); // gcd 0 0 = 0

            let (_, lhs_eq) = d.chain(
                lhs0,
                &[
                    (gcd_zero_bc0, step_left),
                    (gcd_zero_zero, step_right),
                    (zero, gcd_zero_zero_eq),
                ],
            );

            let g = d.gcd(big_m, b);
            let rhs0 = d.mul(g, zero);
            let mul_g_zero = d.lemma(p.mul_zero, &[g]); // g*0 = 0
            let (_, rhs_eq) = d.chain(rhs0, &[(zero, mul_g_zero)]);

            let zero_eq_rhs = d.symm(rhs0, zero, rhs_eq);
            d.trans(lhs0, zero, rhs0, lhs_eq, zero_eq_rhs)
        };

        let at_succ_c = |d: &mut NatDev<'_>, c_pred: ExprId| -> ExprId {
            let big_c = d.succ(c_pred);
            let mc = d.mul(big_m, big_c);
            let bc = d.mul(b, big_c);
            let pos_c = d.zero_lt_succ(c_pred);
            let pos_mc = d.lemma(p.one_le_mul, &[big_m, big_c, pos_m, pos_c]);

            // Step A: gcd(M*C, b*C) = gcd(mod(b*C, M*C), M*C)
            let step_a = gcd_unfold_pos(d, &p, mc, pos_mc, bc);
            let mod_bc_mc = d.modulo(bc, mc);
            let gcd_mod_bc_mc_mc = d.gcd(mod_bc_mc, mc);

            // Step B: mod(b*C, M*C) = (mod b M)*C
            let step_b = mul_mod_mul_right_eq(d, &p, b, big_m, pos_m, big_c);
            let mod_b_m = d.modulo(b, big_m);
            let mod_b_m_c = d.mul(mod_b_m, big_c);

            let step_a_rewritten = d.congr(mod_bc_mc, mod_b_m_c, step_b, &|d, v| d.gcd(v, mc));
            let gcd_lhs = d.gcd(mc, bc);
            let gcd_mid = d.gcd(mod_b_m_c, mc);
            let combined_a = d.trans(gcd_lhs, gcd_mod_bc_mc_mc, gcd_mid, step_a, step_a_rewritten);

            // Step D: IH at lower := mod b M, applied at (b, c) := (M, C).
            let decrease = d.lemma(p.mod_lt, &[b, big_m, pos_m]); // Lt (mod b M) M
            let recursive_row = d.apply(recursive, &[mod_b_m, decrease]); // row(mod b M)
            let step_d = d.apply(recursive_row, &[big_m, big_c]);
            let gcd_mod_b_m_m = d.gcd(mod_b_m, big_m);
            let rhs_d = d.mul(gcd_mod_b_m_m, big_c);

            let combined_ad = d.trans(gcd_lhs, gcd_mid, rhs_d, combined_a, step_d);

            // Step E: gcd_succ(predecessor, b) : gcd(M,b) = gcd(mod b M, M).
            let gcd_succ_e = d.lemma(p.gcd_succ, &[predecessor, b]);
            let gcd_m_b = d.gcd(big_m, b);
            let symm_e = d.symm(gcd_m_b, gcd_mod_b_m_m, gcd_succ_e);

            let step_f = d.congr(gcd_mod_b_m_m, gcd_m_b, symm_e, &|d, v| d.mul(v, big_c));
            let final_rhs = d.mul(gcd_m_b, big_c);

            d.trans(gcd_lhs, rhs_d, final_rhs, combined_ad, step_f)
        };

        let body = cases_zero_succ(d, c, &motive_c, &at_zero_c, &at_succ_c);

        let with_c = d.lam_fv(c_fv, nat, body);
        let with_b = d.lam_fv(b_fv, nat, with_c);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, with_b);
        let with_ignored_ih = d.lam_fv(ignored_ih_fv, ignored_ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ignored_ih)
    };

    let step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, m);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let selected = d.apply(rec, &[step_motive, zero_minor, succ_minor, m]);
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, body);
        d.lam_fv(m_fv, nat, with_recursive)
    };

    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let all = d.apply(fix, &[nat, relation, family, well_founded, step]);

    d.theorem(p.gcd_mul_right, 3, &|d, values| {
        let (a, b, c) = (values[0], values[1], values[2]);
        let lhs = {
            let ac = d.mul(a, c);
            let bc = d.mul(b, c);
            d.gcd(ac, bc)
        };
        let rhs = {
            let g = d.gcd(a, b);
            d.mul(g, c)
        };
        (d.eq(lhs, rhs), d.apply(all, &[a, b, c]))
    })?;

    Ok(())
}
