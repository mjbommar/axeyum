//! `ml430` mirrors against `Nat.fermatNumber` (`fermat_number.rs`): the
//! trichotomy `fermatNumber_ne_one`/`fermatNumber_mono`, and Goldbach's
//! coprimality theorem `coprime_fermatNumber_fermatNumber`.
//!
//! `fermatNumber n := add (pow 2 (pow 2 n)) 1` (`fermat_number.rs`), so
//! `fermatNumber n` is DEFEQ `succ (pow 2 (pow 2 n))` for any `n` — `add`
//! recurses on its right argument and `1 = succ 0` is concrete regardless of
//! the left operand's shape. Every proof here works with that unfolded
//! `succ`/`add` shape and lets the kernel's own defeq check bridge back to
//! `fermatNumber n` at `add_declaration` time; nothing here ever forms a
//! concrete Fermat NUMBER (`n` stays a free variable throughout, so the
//! largest magnitude any proof term evaluates is the numeral `2` itself —
//! see CLAUDE.md's "EVERY `Nat` NUMERAL … IS UNARY" entry for why that
//! restriction is load-bearing here).
//!
//! ## `coprime_fermatNumber_fermatNumber` (Goldbach's theorem)
//!
//! For `m < n`, write `a := 2^(2^m)` (so `fermatNumber m = a + 1`) and
//! `t := n - m > 0`. Since `pow` recurses on the exponent, `t = succ (pred
//! t)` gives `2^t` defeq `mul j 2` (`j := 2^(pred t)`), and `mul_comm` turns
//! that into `2 * j`. `pow_add`/[`pow_mul_eq`] then give
//!
//! ```text
//! 2^(2^n) = 2^(2^m * (2*j)) = (2^(2^m))^(2*j) = ((2^(2^m))^2)^j = (a^2)^j
//! ```
//!
//! Separately, `a^2 ≡ 1 (mod a+1)` by a direct existential witness (`u = 1`,
//! `v = a`: `a*a + (a+1)*1 = 1 + (a+1)*a`, an `add`/`mul` reshuffle with no
//! subtraction). `Nat.mod_eq_pow` (`fermat.rs`) raises that to the `j`-th
//! power: `(a^2)^j ≡ 1^j = 1 (mod a+1)`, i.e. `2^(2^n) ≡ 1 (mod
//! fermatNumber m)`, and `mod_eq_add_right` shifts both sides by `+1`:
//! `fermatNumber n ≡ 2 (mod fermatNumber m)`.
//!
//! `Nat.ModEq.gcd_eq` then gives `gcd (fermatNumber n) (fermatNumber m) = gcd
//! 2 (fermatNumber m)`, and `fermatNumber m` is odd (`2^k` is even for any
//! `k > 0`, `pow_pos` gives `2^m > 0`), so `coprime_two_left`'s reverse
//! direction closes it at `gcd 2 (fermatNumber m) = 1`.

use super::NatPrelude;
use super::finite::{ne_of_lt, ne_symm};
use super::helpers::{iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps};
use super::parity::even_predicate;
use super::steps::absurd;
use super::steps::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// `Nat.fermatNumber_ne_one : ∀ n, Ne (fermatNumber n) 1`.
// ============================================================================

/// `fermatNumber n` is DEFEQ `succ (pow 2 (pow 2 n))`, and `pow 2 (pow 2 n) >
/// 0` (`pow_pos`), so `1 < fermatNumber n` (`succ_le_succ` on `0 < pow 2 (pow
/// 2 n)`, defeq `Le 1 (succ (pow 2 (pow 2 n)))`), hence `fermatNumber n ≠ 1`
/// (`ne_of_lt` + `ne_symm`, `finite.rs`).
pub(super) fn declare_fermatnumber_ne_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fermatnumber_ne_one, 1, &|d, v| {
        let n = v[0];
        let two = d.num(2);
        let one = d.num(1);

        let inner_pow = d.pow(two, n);
        let m = d.pow(two, inner_pow); // 2^(2^n)

        let zero_lt_two = d.zero_lt_succ(one); // Lt 0 2
        let h0 = d.lemma(p.pow_pos, &[two, inner_pow, zero_lt_two]); // Lt 0 m
        let h1 = d.lemma(p.succ_le_succ, &[one, m, h0]); // Le (succ 1) (succ m), defeq Lt 1 (succ m)

        let fermat_n = d.const_app(p.fermat_number, &[n]);
        let hne1 = ne_of_lt(d, &p, one, fermat_n, h1); // Not (Eq 1 fermat_n)
        let hne2 = ne_symm(d, one, fermat_n, hne1); // Not (Eq fermat_n 1)

        let eq_ty = d.eq(fermat_n, one);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let stmt = d.arrow(eq_ty, false_ty);
        (stmt, hne2)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.fermatNumber_mono : Monotone Nat.fermatNumber`.
// ============================================================================

/// `pow b · ` is monotone in the exponent for any base `b > 1`
/// (`pow_lt_pow_of_lt` for the strict case, `le_refl` transported along the
/// equality for the reflexive one) — the `Le`-strength companion
/// `pow_lt_pow_of_lt` itself never needed.
fn pow_le_pow_of_le_local(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    b: ExprId,
    i: ExprId,
    j: ExprId,
    hb: ExprId,
    hij: ExprId,
) -> ExprId {
    let p = *p;
    let split = d.lemma(p.lt_or_eq_of_le, &[i, j, hij]); // Or (Lt i j) (Eq i j)
    let pow_i = d.pow(b, i);
    let pow_j = d.pow(b, j);
    let goal = d.le(pow_i, pow_j);

    let lt_ty = d.lt(i, j);
    let eq_ty = d.eq(i, j);

    let on_lt = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let strict = d.lemma(p.pow_lt_pow_of_lt, &[b, i, j, hb, h]); // Lt pow_i pow_j
        let succ_pow_i = d.succ(pow_i);
        let le_succ_pi = d.lemma(p.le_succ, &[pow_i]); // Le pow_i (succ pow_i)
        let weak = d.lemma(p.le_trans, &[pow_i, succ_pow_i, pow_j, le_succ_pi, strict]);
        d.lam_fv(h_fv, lt_ty, weak)
    };
    let on_eq = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = d.eq_motive(i, &|d, x| {
            let px = d.pow(b, x);
            d.le(pow_i, px)
        });
        let refl_case = d.lemma(p.le_refl, &[pow_i]); // Le pow_i pow_i
        let transported = d.transport(i, motive, refl_case, j, h);
        d.lam_fv(h_fv, eq_ty, transported)
    };
    or_cases(d, lt_ty, eq_ty, goal, on_lt, on_eq, split)
}

/// `Nat.fermatNumber_mono : ∀ x y, Le x y → Le (fermatNumber x) (fermatNumber
/// y)` — the core-rendered `Monotone` unfolding (Mathlib's `Monotone f :=
/// ∀ x y, x ≤ y → f x ≤ f y`), the same treatment already given
/// `Nat.log_monotone`/`Nat.clog_monotone`. `fermatNumber` composes
/// `pow 2 ·` with itself twice then `add · 1`, and `pow_le_pow_of_le_local`
/// plus `add_le_add_right` climb through all three monotone layers.
pub(super) fn declare_fermatnumber_mono(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fermatnumber_mono, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let one = d.num(1);
        let two = d.num(2);

        let h_ty = d.le(x, y);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // Lt 1 2, defeq Le (succ 1) 2 = Le 2 2 = le_refl 2.
        let hb = d.lemma(p.le_refl, &[two]); // Le 2 2, defeq Lt 1 2

        // 2^x ≤ 2^y.
        let inner_le = pow_le_pow_of_le_local(d, &p, two, x, y, hb, h);
        // 2^(2^x) ≤ 2^(2^y).
        let pow_x = d.pow(two, x);
        let pow_y = d.pow(two, y);
        let outer_le = pow_le_pow_of_le_local(d, &p, two, pow_x, pow_y, hb, inner_le);

        // fermatNumber x = pow2x' + 1 ≤ pow2y' + 1 = fermatNumber y.
        let pow2x2 = d.pow(two, pow_x);
        let pow2y2 = d.pow(two, pow_y);
        let concl_raw = d.lemma(p.add_le_add_right, &[one, pow2x2, pow2y2, outer_le]);

        let fermat_x = d.const_app(p.fermat_number, &[x]);
        let fermat_y = d.const_app(p.fermat_number, &[y]);
        let concl = d.le(fermat_x, fermat_y);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, concl_raw);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.coprime_fermatNumber_fermatNumber` (Goldbach's theorem) — see the
// module doc for the proof route.
// ============================================================================

/// `Eq (pow b (mul x y)) (pow (pow b x) y)`, by induction on `y`: base is
/// `refl 1` (`mul x 0`/`pow b 0`/`pow (pow b x) 0` all defeq `0`/`1`/`1`);
/// step composes `pow_add` (`mul x (succ j)` defeq `add (mul x j) x`) with
/// the IH via `congr`, landing defeq on `pow (pow b x) (succ j)`
/// (`pow_succ` reversed).
fn pow_mul_eq(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let p = *p;
    let pow_bx = d.pow(b, x);
    let motive = move |d: &mut NatDev<'_>, yy: ExprId| -> ExprId {
        let mul_xy = d.mul(x, yy);
        let lhs = d.pow(b, mul_xy);
        let rhs = d.pow(pow_bx, yy);
        d.eq(lhs, rhs)
    };
    let base = |d: &mut NatDev<'_>| -> ExprId {
        let one = d.num(1);
        d.refl(one)
    };
    let step = move |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let mul_xj = d.mul(x, j);
        let pow_add_eq = d.lemma(p.pow_add, &[b, mul_xj, x]);
        // Eq (pow b (add mul_xj x)) (mul (pow b mul_xj) (pow b x))
        let pow_b_mulxj = d.pow(b, mul_xj);
        let pow_bx_j = d.pow(pow_bx, j);
        let congr_ih = d.congr(pow_b_mulxj, pow_bx_j, ih, &move |d, z| d.mul(z, pow_bx));
        // Eq (mul pow_b_mulxj pow_bx) (mul pow_bx_j pow_bx)
        let mul_lhs = d.mul(pow_b_mulxj, pow_bx);
        let mul_rhs = d.mul(pow_bx_j, pow_bx);
        let add_mxj_x = d.add(mul_xj, x);
        let pow_b_addmxjx = d.pow(b, add_mxj_x);
        d.trans(pow_b_addmxjx, mul_lhs, mul_rhs, pow_add_eq, congr_ih)
    };
    d.induct(&motive, &base, &step, y)
}

/// `Not (Eq m n) → Or (Lt m n) (Lt n m)`, via `le_total` then `lt_or_eq_of_le`
/// on each branch, refuting the equality case against `hne`. `pub(super)` so
/// `dist.rs`'s `dist_pos_of_ne` (draw 9, `natural-distance`) can reuse it
/// rather than re-deriving the same case split.
pub(super) fn lt_or_gt_of_ne_local(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    hne: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let lt_mn = d.lt(m, n);
    let lt_nm = d.lt(n, m);
    let goal = d.const_app(logic.or, &[lt_mn, lt_nm]);

    let total = d.lemma(p.le_total, &[m, n]); // Or (Le m n) (Le n m)
    let le_mn_ty = d.le(m, n);
    let le_nm_ty = d.le(n, m);

    let on_le_mn = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let split = d.lemma(p.lt_or_eq_of_le, &[m, n, h]); // Or (Lt m n) (Eq m n)
        let eq_ty = d.eq(m, n);
        let on_lt = {
            let hl_fv = d.fresh_fvar();
            let hl = d.kernel().fvar(hl_fv);
            let inl = d.const_app(logic.or_inl, &[lt_mn, lt_nm, hl]);
            d.lam_fv(hl_fv, lt_mn, inl)
        };
        let on_eq = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let contra = d.apply(hne, &[he]);
            let result = absurd(d, goal, contra);
            d.lam_fv(he_fv, eq_ty, result)
        };
        let case_result = or_cases(d, lt_mn, eq_ty, goal, on_lt, on_eq, split);
        d.lam_fv(h_fv, le_mn_ty, case_result)
    };
    let on_le_nm = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let split = d.lemma(p.lt_or_eq_of_le, &[n, m, h]); // Or (Lt n m) (Eq n m)
        let eq_ty = d.eq(n, m);
        let on_lt = {
            let hl_fv = d.fresh_fvar();
            let hl = d.kernel().fvar(hl_fv);
            let inr = d.const_app(logic.or_inr, &[lt_mn, lt_nm, hl]);
            d.lam_fv(hl_fv, lt_nm, inr)
        };
        let on_eq = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let he_rev = d.symm(n, m, he); // Eq m n
            let contra = d.apply(hne, &[he_rev]);
            let result = absurd(d, goal, contra);
            d.lam_fv(he_fv, eq_ty, result)
        };
        let case_result = or_cases(d, lt_nm, eq_ty, goal, on_lt, on_eq, split);
        d.lam_fv(h_fv, le_nm_ty, case_result)
    };
    or_cases(d, le_mn_ty, le_nm_ty, goal, on_le_mn, on_le_nm, total)
}

/// `Lt m (add m t) → Lt zero t`, via `zero_le t` + `lt_or_eq_of_le`: the
/// `Eq zero t` branch transports `hlt` along it to `Lt m (add m zero)`,
/// defeq `Lt m m`, refuted by `lt_irrefl`.
pub(super) fn pos_of_lt_add_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    t: ExprId,
    hlt: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let goal = d.lt(zero, t);
    let zero_le_t = d.lemma(p.zero_le, &[t]);
    let split = d.lemma(p.lt_or_eq_of_le, &[zero, t, zero_le_t]);
    let lt_ty = d.lt(zero, t);
    let eq_ty = d.eq(zero, t);
    let on_lt = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        d.lam_fv(h_fv, lt_ty, h)
    };
    let on_eq = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_rev = d.symm(zero, t, h); // Eq t zero
        let motive = d.eq_motive(t, &move |d, x| {
            let amx = d.add(m, x);
            d.lt(m, amx)
        });
        let lt_m_addm0 = d.transport(t, motive, hlt, zero, h_rev); // Lt m (add m zero), defeq Lt m m
        let contra = d.lemma(p.lt_irrefl, &[m, lt_m_addm0]);
        let result = absurd(d, goal, contra);
        d.lam_fv(h_fv, eq_ty, result)
    };
    or_cases(d, lt_ty, eq_ty, goal, on_lt, on_eq, split)
}

/// `Even (pow 2 k)` for `k > 0`: write `k = succ (pred k)`
/// (`succ_pred_of_pos`), so `pow 2 k` is defeq `mul j 2` (`j := pow 2 (pred
/// k)`), defeq `add (add 0 j) j`; `zero_add` plus `congr` relate that to
/// `add j j`, the witness form `Even` needs directly.
fn even_pow_two_of_pos(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId, hk_pos: ExprId) -> ExprId {
    let p = *p;
    let succpred_eq = d.lemma(p.succ_pred_of_pos, &[k, hk_pos]); // Eq k (succ (pred k))
    let pred_k = d.pred(k);
    let succ_pred_k = d.succ(pred_k);
    let two = d.num(2);
    let j = d.pow(two, pred_k);

    let zero = d.zero();
    let add_zero_j = d.add(zero, j);
    let za = d.lemma(p.zero_add, &[j]); // Eq (add zero j) j
    let add_j_j = d.add(j, j);
    let step_eq = d.congr(add_zero_j, j, za, &move |d, x| d.add(x, j));
    // step_eq : Eq (add (add zero j) j) (add j j)

    let add_add_zero_j_j = d.add(add_zero_j, j);
    let pred_witness = even_predicate(d, add_j_j); // fun c => Eq add_j_j (add c c)
    let refl_proof = d.refl(add_j_j);
    let level_one = d.level_one();
    let nat = d.nat_ty();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
    let even_add_j_j = d.apply(intro, &[nat, pred_witness, j, refl_proof]);

    let step_eq_rev = d.symm(add_add_zero_j_j, add_j_j, step_eq);
    let motive1 = d.eq_motive(add_j_j, &move |d, x| d.const_app(p.even, &[x]));
    let even_add_add_zero_j_j = d.transport(
        add_j_j,
        motive1,
        even_add_j_j,
        add_add_zero_j_j,
        step_eq_rev,
    );
    // even_add_add_zero_j_j : Even (add (add zero j) j), defeq Even (mul j 2), defeq Even (pow 2 (succ (pred k)))

    let h_rev = d.symm(k, succ_pred_k, succpred_eq); // Eq (succ (pred k)) k
    let motive2 = d.eq_motive(succ_pred_k, &move |d, x| {
        let px = d.pow(two, x);
        d.const_app(p.even, &[px])
    });
    d.transport(succ_pred_k, motive2, even_add_add_zero_j_j, k, h_rev)
    // : Even (pow 2 k)
}

/// `Odd (add (pow 2 (pow 2 m)) 1)` (defeq `Odd (fermatNumber m)`) — `pow 2
/// (pow 2 m)` is `Even` (`even_pow_two_of_pos`, exponent positive by
/// `pow_pos`), and `even_iff_odd_succ`'s `mp` direction turns `Even n` into
/// `Odd (succ n)`.
fn odd_fermat_number_local(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let exp_m = d.pow(two, m);
    let zero_lt_two = d.zero_lt_succ(one);
    let exp_m_pos = d.lemma(p.pow_pos, &[two, m, zero_lt_two]);
    let val = d.pow(two, exp_m); // = a
    let even_val = even_pow_two_of_pos(d, &p, exp_m, exp_m_pos);

    let iff_pf = d.lemma(p.even_iff_odd_succ, &[val]);
    let even_ty = d.lemma(p.even, &[val]);
    let succ_val = d.succ(val);
    let odd_succ_ty = d.lemma(p.odd, &[succ_val]);
    let mp_fn = iff_forward(d, even_ty, odd_succ_ty, iff_pf);
    d.apply(mp_fn, &[even_val])
    // : Odd (succ val), defeq Odd (add val one) = Odd (fermatNumber m)
}

/// A `modEq d a b` proof from explicit witnesses `u, v` and an equation
/// `Eq (a + d*u) (b + d*v)`.
#[allow(clippy::too_many_arguments)]
fn mk_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    a: ExprId,
    b: ExprId,
    u: ExprId,
    v: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let level_one = d.level_one();
    let nat = d.nat_ty();
    let inner_pred = d.mod_eq_inner_predicate(modulus, a, b, u);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
    let inner = d.apply(intro, &[nat, inner_pred, v, heq]);
    let outer_pred = d.mod_eq_outer_predicate(modulus, a, b);
    d.apply(intro, &[nat, outer_pred, u, inner])
}

/// `modEq (add a one) (pow a two) one` — witnessed by `u = 1, v = a`:
/// `pow a two + (a+1)*1 = 1 + (a+1)*a`, i.e. `a*a + (a+1) = 1 + (a*a + a)`
/// (`right_distrib`/`one_mul` expand `(a+1)*a`; `mul_one` collapses
/// `(a+1)*1`; `add_assoc`/`add_comm` reshuffle the three summands).
fn base_congr_a_plus_1(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let aa = d.mul(a, a);
    let a_plus_1 = d.add(a, one);
    let two = d.num(2);
    let pow_a2 = d.pow(a, two);

    // pow_a2_eq_aa : Eq (pow a 2) (mul a a) -- pow a 2 defeq mul (mul 1 a) a.
    let one_mul_a = d.lemma(p.one_mul, &[a]); // Eq (mul one a) a
    let mul_one_a_pre = d.mul(one, a);
    let pow_a2_eq_aa = d.congr(mul_one_a_pre, a, one_mul_a, &move |d, x| d.mul(x, a));

    // mul_one_eq : Eq (mul a_plus_1 one) a_plus_1.
    let mul_a1_1 = d.mul(a_plus_1, one);
    let mul_one_eq = d.lemma(p.mul_one, &[a_plus_1]);

    // rd_final : Eq (mul a_plus_1 a) (add aa a).
    let mul_a1_a = d.mul(a_plus_1, a);
    let rd_eq = d.lemma(p.right_distrib, &[a, one, a]); // Eq (mul (add a one) a) (add (mul a a) (mul one a))
    let mul_one_a = d.mul(one, a);
    let add_aa_mulonea = d.add(aa, mul_one_a);
    let rd_congr = d.congr(mul_one_a, a, one_mul_a, &move |d, x| d.add(aa, x));
    let add_aa_a = d.add(aa, a);
    let rd_final = d.trans(mul_a1_a, add_aa_mulonea, add_aa_a, rd_eq, rd_congr);

    let rhs_congr = d.congr(mul_a1_a, add_aa_a, rd_final, &move |d, x| d.add(one, x));
    // rhs_congr : Eq (add one (mul a_plus_1 a)) (add one (add aa a))
    let add_one_mula1a = d.add(one, mul_a1_a);
    let add_one_addaaa = d.add(one, add_aa_a);
    let symm_rhs_congr = d.symm(add_one_mula1a, add_one_addaaa, rhs_congr);

    let assoc_result = d.lemma(p.add_assoc, &[aa, a, one]); // Eq (add (add aa a) one) (add aa (add a one))
    let add_addaaa_one = d.add(add_aa_a, one);
    let add_a_one = d.add(a, one);
    let add_aa_addaone = d.add(aa, add_a_one);
    let symm_assoc = d.symm(add_addaaa_one, add_aa_addaone, assoc_result);
    let comm_result = d.lemma(p.add_comm, &[add_aa_a, one]); // Eq (add (add aa a) one) (add one (add aa a))

    let start = d.add(pow_a2, mul_a1_1);
    let step0 = d.congr(pow_a2, aa, pow_a2_eq_aa, &move |d, x| d.add(x, mul_a1_1));
    let add_aa_mula11 = d.add(aa, mul_a1_1);
    let step1 = d.congr(mul_a1_1, a_plus_1, mul_one_eq, &move |d, x| d.add(aa, x));
    let add_aa_ap1 = d.add(aa, a_plus_1);

    let (_last, heq) = d.chain(
        start,
        &[
            (add_aa_mula11, step0),
            (add_aa_ap1, step1),
            (add_addaaa_one, symm_assoc),
            (add_one_addaaa, comm_result),
            (add_one_mula1a, symm_rhs_congr),
        ],
    );
    mk_mod_eq(d, &p, a_plus_1, pow_a2, one, one, a, heq)
}

/// `Lt m n → Eq (gcd (fermatNumber m) (fermatNumber n)) one` — see the
/// module doc for the full route.
fn fermat_coprime_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    hlt: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);

    let succ_m = d.succ(m);
    let le_succ_m = d.lemma(p.le_succ, &[m]);
    let le_mn = d.lemma(p.le_trans, &[m, succ_m, n, le_succ_m, hlt]);

    let t = d.sub(n, m);
    let add_m_t = d.add(m, t);
    let eq1 = d.lemma(p.add_sub_cancel_of_le, &[m, n, le_mn]); // Eq (add m t) n
    let eq_n = d.symm(add_m_t, n, eq1); // Eq n (add m t)

    let motive_h = d.eq_motive(n, &move |d, x| d.lt(m, x));
    let hlt2 = d.transport(n, motive_h, hlt, add_m_t, eq_n); // Lt m (add m t)

    let t_pos = pos_of_lt_add_left(d, &p, m, t, hlt2);

    let exp_m = d.pow(two, m);
    let one2 = d.num(1);
    let zero_lt_two = d.zero_lt_succ(one2);
    let _exp_m_pos = d.lemma(p.pow_pos, &[two, m, zero_lt_two]);
    let a = d.pow(two, exp_m);

    let succpred_t_eq = d.lemma(p.succ_pred_of_pos, &[t, t_pos]); // Eq t (succ (pred t))
    let pred_t = d.pred(t);
    let succ_pred_t = d.succ(pred_t);
    let j = d.pow(two, pred_t);

    let t_pow = d.pow(two, t);
    let t_pow_eq_pow_succpredt = d.congr(t, succ_pred_t, succpred_t_eq, &move |d, x| d.pow(two, x));
    let mul_j2 = d.mul(j, two);
    let mul_2j = d.mul(two, j);
    let comm_j2 = d.lemma(p.mul_comm, &[j, two]); // Eq (mul j two) (mul two j)
    let (_last1, t_pow_eq_2j) = d.chain(
        t_pow,
        &[(mul_j2, t_pow_eq_pow_succpredt), (mul_2j, comm_j2)],
    );

    let exp_n = d.pow(two, n);
    let pow_two_addmt = d.pow(two, add_m_t);
    let congr_n = d.congr(n, add_m_t, eq_n, &move |d, x| d.pow(two, x));
    let pow_add_eq = d.lemma(p.pow_add, &[two, m, t]); // Eq (pow2 (add m t)) (mul (pow2 m) (pow2 t))
    let mul_em_tpow = d.mul(exp_m, t_pow);
    let (_last2, exp_n_eq) = d.chain(
        exp_n,
        &[(pow_two_addmt, congr_n), (mul_em_tpow, pow_add_eq)],
    );

    let congr_tpow = d.congr(t_pow, mul_2j, t_pow_eq_2j, &move |d, x| d.mul(exp_m, x));
    let mul_em_2j = d.mul(exp_m, mul_2j);
    let (_last3, exp_n_eq2) = d.chain(exp_n, &[(mul_em_tpow, exp_n_eq), (mul_em_2j, congr_tpow)]);

    let a2 = d.pow(a, two);
    let a2_j = d.pow(a2, j);
    let pow_exp_n = d.pow(two, exp_n);
    let pow_two_mulem2j = d.pow(two, mul_em_2j);
    let congr_expn = d.congr(exp_n, mul_em_2j, exp_n_eq2, &move |d, x| d.pow(two, x));
    let pow_mul_eq1 = pow_mul_eq(d, &p, two, exp_m, mul_2j); // Eq (pow2 (mul exp_m mul_2j)) (pow (pow2 exp_m) mul_2j)
    let pow_a_mul2j = d.pow(a, mul_2j);
    let pow_mul_eq2 = pow_mul_eq(d, &p, a, two, j); // Eq (pow a (mul two j)) (pow (pow a two) j)

    let (_last4, master_eq) = d.chain(
        pow_exp_n,
        &[
            (pow_two_mulem2j, congr_expn),
            (pow_a_mul2j, pow_mul_eq1),
            (a2_j, pow_mul_eq2),
        ],
    );
    // master_eq : Eq (pow_exp_n) (a2_j)

    let base_congr = base_congr_a_plus_1(d, &p, a); // modEq (add a one) (pow a two) one
    let a_plus_1 = d.add(a, one);
    let mod_eq_pow_j = d.lemma(p.mod_eq_pow, &[a_plus_1, a2, one, j, base_congr]);
    // modEq a_plus_1 (pow a2 j) (pow one j)

    let one_pow_eq = d.lemma(p.one_pow, &[j]); // Eq (pow one j) one
    let pow_one_j = d.pow(one, j);
    let motive_modeq = d.eq_motive(pow_one_j, &move |d, x| d.mod_eq(a_plus_1, a2_j, x));
    let mod_eq_final = d.transport(pow_one_j, motive_modeq, mod_eq_pow_j, one, one_pow_eq);
    // modEq a_plus_1 a2_j one

    let master_eq_rev = d.symm(pow_exp_n, a2_j, master_eq); // Eq a2_j pow_exp_n
    let motive_modeq2 = d.eq_motive(a2_j, &move |d, x| d.mod_eq(a_plus_1, x, one));
    let mod_eq_expn = d.transport(a2_j, motive_modeq2, mod_eq_final, pow_exp_n, master_eq_rev);
    // modEq a_plus_1 pow_exp_n one

    let mod_eq_plus1 = d.lemma(
        p.mod_eq_add_right,
        &[a_plus_1, pow_exp_n, one, one, mod_eq_expn],
    );
    // modEq a_plus_1 (add pow_exp_n one) (add one one), defeq modEq (fermatNumber m) (fermatNumber n) two

    let fermat_n_raw = d.add(pow_exp_n, one);
    let gcd_eq = d.lemma(
        p.mod_eq_gcd_eq,
        &[a_plus_1, fermat_n_raw, two, mod_eq_plus1],
    );
    // Eq (gcd fermat_n_raw a_plus_1) (gcd two a_plus_1)

    let odd_fermat_m = odd_fermat_number_local(d, &p, m); // Odd (add a one) = Odd a_plus_1
    let coprime_two_left_iff = d.lemma(p.coprime_two_left, &[a_plus_1]);
    // Iff (Eq (gcd two a_plus_1) one) (Odd a_plus_1)
    let gcd_two_ap1_ty_val = d.gcd(two, a_plus_1);
    let gcd_two_ap1_ty = d.eq(gcd_two_ap1_ty_val, one);
    let odd_ap1_ty = d.lemma(p.odd, &[a_plus_1]);
    let mpr_fn = iff_reverse(d, gcd_two_ap1_ty, odd_ap1_ty, coprime_two_left_iff);
    let gcd_two_ap1_eq_one = d.apply(mpr_fn, &[odd_fermat_m]);

    let gcd_fnraw_ap1 = d.gcd(fermat_n_raw, a_plus_1);
    let gcd_two_ap1 = d.gcd(two, a_plus_1);
    let (_last5, gcd_nm_eq_one) = d.chain(
        gcd_fnraw_ap1,
        &[(gcd_two_ap1, gcd_eq), (one, gcd_two_ap1_eq_one)],
    );
    // Eq (gcd fermat_n_raw a_plus_1) one

    d.lemma(
        p.coprime_symmetric,
        &[fermat_n_raw, a_plus_1, gcd_nm_eq_one],
    )
    // Eq (gcd a_plus_1 fermat_n_raw) one, defeq Eq (gcd (fermatNumber m) (fermatNumber n)) one
}

/// `Nat.coprime_fermatNumber_fermatNumber : ∀ m n, Not (Eq m n) →
/// Eq (gcd (fermatNumber m) (fermatNumber n)) one` (Goldbach's theorem).
pub(super) fn declare_coprime_fermatnumber_fermatnumber(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_fermatnumber_fermatnumber, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let eq_ty = d.eq(m, n);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eq_ty, false_ty);

        let fermat_m = d.const_app(p.fermat_number, &[m]);
        let fermat_n = d.const_app(p.fermat_number, &[n]);
        let one = d.num(1);
        let gcd_fm_fn = d.gcd(fermat_m, fermat_n);
        let concl = d.eq(gcd_fm_fn, one);
        let stmt = d.arrow(ne_ty, concl);

        let hne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(hne_fv);

        let split = lt_or_gt_of_ne_local(d, &p, m, n, hne);
        let lt_mn_ty = d.lt(m, n);
        let lt_nm_ty = d.lt(n, m);

        let on_lt_mn = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let proof = fermat_coprime_of_lt(d, &p, m, n, h);
            d.lam_fv(h_fv, lt_mn_ty, proof)
        };
        let on_lt_nm = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let proof_nm = fermat_coprime_of_lt(d, &p, n, m, h); // Eq (gcd Fn Fm) one
            let fermat_n2 = d.const_app(p.fermat_number, &[n]);
            let fermat_m2 = d.const_app(p.fermat_number, &[m]);
            let swapped = d.lemma(p.coprime_symmetric, &[fermat_n2, fermat_m2, proof_nm]);
            d.lam_fv(h_fv, lt_nm_ty, swapped)
        };
        let case_result = or_cases(d, lt_mn_ty, lt_nm_ty, concl, on_lt_mn, on_lt_nm, split);
        let proof = d.lam_fv(hne_fv, ne_ty, case_result);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare all three `fermatNumber` mirrors, in difficulty order.
pub(super) fn declare_fermat_number_mirrors_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_fermatnumber_ne_one(d, p)?;
    declare_fermatnumber_mono(d, p)?;
    declare_coprime_fermatnumber_fermatnumber(d, p)?;
    Ok(())
}

// ============================================================================
// `fermat-easy` lane: three closed reductions, `Nat.odd_fermatNumber`, and
// `Nat.fermatNumber_strictMono` — `docs/plan/status/377-fermat-easy.md`.
// ============================================================================

/// `Nat.fermatNumber_zero : Eq (fermatNumber 0) 3` — `fermatNumber 0 = add
/// (pow 2 (pow 2 0)) 1 = add (pow 2 1) 1 = add 2 1 = 3`, fully concrete
/// (largest formed magnitude 3), closed by `refl` alone. This equation was
/// decided the instant `Nat.fermatNumber` was declared
/// (`docs/research/09-decisions/adr-0695-…`); this declaration only states
/// it as its own checkable theorem.
pub(super) fn declare_fermatnumber_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fermatnumber_zero, 0, &|d, _v| {
        let zero = d.zero();
        let three = d.num(3);
        let lhs = d.const_app(p.fermat_number, &[zero]);
        (d.eq(lhs, three), d.refl(lhs))
    })?;
    Ok(())
}

/// `Nat.fermatNumber_one : Eq (fermatNumber 1) 5` — `fermatNumber 1 = add
/// (pow 2 (pow 2 1)) 1 = add (pow 2 2) 1 = add 4 1 = 5`, largest formed
/// magnitude 5.
pub(super) fn declare_fermatnumber_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fermatnumber_one, 0, &|d, _v| {
        let one = d.num(1);
        let five = d.num(5);
        let lhs = d.const_app(p.fermat_number, &[one]);
        (d.eq(lhs, five), d.refl(lhs))
    })?;
    Ok(())
}

/// `Nat.fermatNumber_two : Eq (fermatNumber 2) 17` — `fermatNumber 2 = add
/// (pow 2 (pow 2 2)) 1 = add (pow 2 4) 1 = add 16 1 = 17`, largest formed
/// magnitude 17 — the ceiling this lane holds to (`n = 3` would form 257,
/// `n = 4` would form 65537; CLAUDE.md's "EVERY `Nat` NUMERAL … IS UNARY"
/// entry).
pub(super) fn declare_fermatnumber_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fermatnumber_two, 0, &|d, _v| {
        let two = d.num(2);
        let seventeen = d.num(17);
        let lhs = d.const_app(p.fermat_number, &[two]);
        (d.eq(lhs, seventeen), d.refl(lhs))
    })?;
    Ok(())
}

/// `Nat.odd_fermatNumber : ∀ n, Odd (fermatNumber n)` — entirely symbolic
/// (`n` stays a free variable throughout; largest formed numeral is the
/// base `2`), reusing `odd_fermat_number_local` above verbatim: it already
/// builds a proof of `Odd (fermatNumber m)` (up to defeq) for whatever `m`
/// it is handed.
pub(super) fn declare_odd_fermatnumber(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.odd_fermatnumber, 1, &|d, v| {
        let n = v[0];
        let fermat_n = d.const_app(p.fermat_number, &[n]);
        let stmt = d.const_app(p.odd, &[fermat_n]);
        let proof = odd_fermat_number_local(d, &p, n);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Lt a b → Lt (add a c) (add b c)`, via `add_comm` + `add_lt_add_left` —
/// only the `Le`-strength `add_le_add_right` exists directly in this
/// prelude (used by `declare_fermatnumber_mono`, above).
fn add_lt_add_right_local(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
) -> ExprId {
    let p = *p;
    let lt_ca_cb = d.lemma(p.add_lt_add_left, &[c, a, b, hab]); // Lt (add c a) (add c b)
    let add_c_a = d.add(c, a);
    let add_c_b = d.add(c, b);
    let add_a_c = d.add(a, c);
    let add_b_c = d.add(b, c);
    let comm_ca = d.lemma(p.add_comm, &[c, a]); // Eq (add c a) (add a c)
    let comm_cb = d.lemma(p.add_comm, &[c, b]); // Eq (add c b) (add b c)

    let motive_lhs = d.eq_motive(add_c_a, &move |d, x| d.lt(x, add_c_b));
    let step1 = d.transport(add_c_a, motive_lhs, lt_ca_cb, add_a_c, comm_ca);
    let motive_rhs = d.eq_motive(add_c_b, &move |d, x| d.lt(add_a_c, x));
    d.transport(add_c_b, motive_rhs, step1, add_b_c, comm_cb)
}

/// `Nat.fermatNumber_strictMono : StrictMono Nat.fermatNumber`
/// (core-rendered `∀ x y, Lt x y → Lt (fermatNumber x) (fermatNumber y)`).
/// Entirely symbolic (`x`, `y` stay free; largest formed numeral is the
/// base `2`) — `pow_lt_pow_of_lt` climbs both `pow 2 ·` layers exactly as
/// `pow_le_pow_of_le_local`'s strict branch does for
/// `declare_fermatnumber_mono` above, and `add_lt_add_right_local` closes
/// the final `+1` layer.
pub(super) fn declare_fermatnumber_strictmono(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fermatnumber_strictmono, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let one = d.num(1);
        let two = d.num(2);

        let h_ty = d.lt(x, y);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // Lt 1 2, defeq Le (succ 1) 2 = Le 2 2 = le_refl 2 (the same device
        // `declare_fermatnumber_mono` uses for its `hb`).
        let hb = d.lemma(p.le_refl, &[two]);

        // 2^x < 2^y.
        let inner_lt = d.lemma(p.pow_lt_pow_of_lt, &[two, x, y, hb, h]);
        // 2^(2^x) < 2^(2^y).
        let pow_x = d.pow(two, x);
        let pow_y = d.pow(two, y);
        let outer_lt = d.lemma(p.pow_lt_pow_of_lt, &[two, pow_x, pow_y, hb, inner_lt]);

        // fermatNumber x = pow2x2 + 1 < pow2y2 + 1 = fermatNumber y.
        let pow2x2 = d.pow(two, pow_x);
        let pow2y2 = d.pow(two, pow_y);
        let concl_raw = add_lt_add_right_local(d, &p, one, pow2x2, pow2y2, outer_lt);

        let fermat_x = d.const_app(p.fermat_number, &[x]);
        let fermat_y = d.const_app(p.fermat_number, &[y]);
        let concl = d.lt(fermat_x, fermat_y);
        let stmt = d.arrow(h_ty, concl);
        let proof = d.lam_fv(h_fv, h_ty, concl_raw);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare all five `fermat-easy` mirrors: the three closed reductions,
/// oddness, and strict monotonicity.
pub(super) fn declare_fermat_number_easy_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_fermatnumber_zero(d, p)?;
    declare_fermatnumber_one(d, p)?;
    declare_fermatnumber_two(d, p)?;
    declare_odd_fermatnumber(d, p)?;
    declare_fermatnumber_strictmono(d, p)?;
    Ok(())
}
