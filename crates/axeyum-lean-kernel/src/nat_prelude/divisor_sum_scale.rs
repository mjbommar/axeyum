//! Divisor-sum monotonicity under `dvd`, and the two `ml430` mirrors it
//! unblocks: `Nat.abundant_of_dvd`, `Nat.abundant_mul_left`.
//!
//! `divisor-sum-monotonicity` lane. `abundant_deficient_lemmas.rs` closed
//! seven `ml430` mirrors and left three open for a shared reason: no
//! infrastructure related `Nat.sumDivisors m` to `Nat.sumDivisors n` when
//! `m ∣ n`. Two of the three ([`F:ml430-nat-abundant-of-dvd-686548ce`],
//! [`F:ml430-nat-abundant-mul-left-4de4fbe7`]) need exactly that. The third
//! (`F:ml430-nat-prime-deficient-pow-9c5e1fef`) needs a DIFFERENT piece
//! (a prime-power divisor characterization) and is not attempted here — see
//! this lane's report.
//!
//! # The core lemma
//!
//! [`declare_sum_divisors_scale_le`] is
//!
//! ```text
//! Nat.sum_divisors_scale_le : ∀ q m, Lt zero q →
//!   Le (mul q (sumDivisors m)) (sumDivisors (mul q m))
//! ```
//!
//! i.e. for a positive scale factor `q`, scaling every divisor of `m` by `q`
//! injects into the divisors of `q*m`, so the divisor sum can only grow (it
//! grows by more than a factor of `q` whenever `m` itself has a divisor `d`
//! with `q*d` not already counted, but `≤` is all three targets need).
//!
//! Both `Nat.dvd a n := ∃ q, n = a*q` and `Nat.sumDivisors n := sumRange (fun
//! d => if n%d=0 then d else 0) (succ n)` (`divisibility.rs`, `perfect.rs`)
//! are reused verbatim; `Nat.mul_sumRange` (`algebra.rs`) turns `mul q
//! (sumDivisors m)` into a sum over the SAME index range `[0,m]`, so the
//! whole proof is one induction relating that sum, term by term, to the sum
//! over `[0, q*m]` that defines `sumDivisors (mul q m)`:
//!
//! - **[`sum_range_mono`]** (Lemma A): `sumRange` is monotone in its bound,
//!   by induction on the `Le` derivation itself (`Nat.le.rec`, the same
//!   pattern `order.rs` uses for `add_le_add_left` etc.).
//! - **[`divisor_scale_pointwise_succ`]** (the per-term bound): at a
//!   SYNTACTICALLY successor-shaped divisor `succ j`, `q*(mth divisor term at
//!   succ j)` is `≤` the `q*m`th divisor term at `q*(succ j)` — an equality
//!   when `succ j ∣ m` (chase the witness through `mul_assoc`/`mul_comm` to
//!   get `q*(succ j) ∣ q*m`), and `0 ≤ anything` otherwise. The general
//!   (non-literal-succ) `mod = 0 ↔ dvd` bridge
//!   ([`mod_eq_zero_iff_dvd_general`], a local copy of
//!   `mod_mul_lemmas.rs`'s `div_mod_reconstructed` pattern) is what lets this
//!   run at the DERIVED divisor `mul q (succ j)`, which is not itself
//!   syntactically `succ _`.
//! - The main induction (inside [`declare_sum_divisors_scale_le`]) combines
//!   the two: peel one term off each side (`sum_range_succ`), bound the new
//!   term via the pointwise lemma, and close the gap between `succ (mul q j)`
//!   and `mul q (succ j)` via [`sum_range_mono`] plus [`scale_lt`] (the `mpr`
//!   direction of `Nat.mul_lt_mul_left`, extracted with
//!   `helpers::iff_reverse`).
//!
//! Everything strictly INSIDE this induction is a private Rust proof-term
//! builder, not a separate kernel declaration — matching how
//! `abundant_deficient_lemmas.rs`'s `two_mul_eq_add_self`/`le_of_lt` are
//! private local combinators rather than named theorems. Only
//! `sum_divisors_scale_le` and the two target mirrors are declared.
//!
//! # The two targets
//!
//! [`declare_abundant_mul_left`] (`Nat.abundant_mul_left : ∀ n m, Abundant n
//! → Not (Eq m zero) → Abundant (mul m n)`) is a direct instance: apply the
//! scale lemma at `q := m`, multiply the `Abundant n` hypothesis through by
//! `m` (again via `scale_lt`), and reassociate `mul m (mul 2 n)` to `mul 2
//! (mul m n)`.
//!
//! [`declare_abundant_of_dvd`] (`Nat.abundant_of_dvd : ∀ m n, Abundant m →
//! dvd m n → Not (Eq n zero) → Abundant n`) destructs the `dvd` witness `q`
//! (`n = mul m q`), derives `Lt zero q` from `Not (Eq n zero)` by
//! contradiction (`q = 0` would force `n = 0` via `mul_zero`), then runs the
//! same scale-and-reassociate argument with `q` as the scale factor and `m`
//! (rewritten to `mul q m` via `mul_comm`) as the base.

use super::NatPrelude;
use super::helpers::{iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local copies of private helpers from other modules (this repository's
// established convention for small proof-term combinators reused across
// files with no shared export point — see `mod_mul_lemmas.rs`'s module doc).
// ============================================================================

/// `fun d => bool_select_nat (beq (mod n d) 0) d 0` — local copy of
/// `perfect.rs`'s private `sum_divisors_term`, matched structurally so that
/// `Nat.sumDivisors n` (`fun n => sumRange (this) (succ n)`) unfolds
/// (delta+beta) to `sumRange (divisor_term n) (succ n)`.
fn divisor_term(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let divisor_fv = d.fresh_fvar();
    let divisor = d.kernel().fvar(divisor_fv);
    let remainder = d.modulo(n, divisor);
    let zero = d.zero();
    let cond = d.beq(remainder, zero);
    let body = d.bool_select_nat(cond, divisor, zero);
    d.lam_fv(divisor_fv, nat, body)
}

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)` — local copy of `perfect.rs`'s
/// private `bool_congr_nat`.
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

/// Reconstruct `divMod dd x (div x dd) (mod x dd)` for ANY `x`, given
/// `pos_dd : Lt zero dd` — local copy of `mod_mul_lemmas.rs`'s private
/// `div_mod_reconstructed` (itself a local copy; see that file's module doc
/// for why this is copied per-file rather than shared).
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
    let exec = d.lemma(p.div_mod_exec, &[pred_dd, x]);

    let motive = d.eq_motive(succ_pred_dd, &|d, y| {
        let q = d.div(x, y);
        let r = d.modulo(x, y);
        d.div_mod(y, x, q, r)
    });
    let eq_rev = d.symm(dd, succ_pred_dd, dd_eq_succ_pred);
    d.transport(succ_pred_dd, motive, exec, dd, eq_rev)
}

/// `Iff (Eq (mod x dd) zero) (dvd dd x)`, for ANY `dd` given `pos_dd : Lt
/// zero dd` (not restricted to a syntactically `succ`-shaped divisor, unlike
/// `perfect.rs`'s `mod_eq_zero_iff_dvd_succ`). Composes
/// [`div_mod_reconstructed`] with `Nat.div_mod_remainder_eq_zero_iff_dvd`.
fn mod_eq_zero_iff_dvd_general(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    pos_dd: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let witness = div_mod_reconstructed(d, &p, dd, pos_dd, x);
    let q = d.div(x, dd);
    let r = d.modulo(x, dd);
    d.lemma(p.div_mod_remainder_eq_zero_iff_dvd, &[dd, x, q, r, witness])
}

/// Build a proof of `dvd a n` from a witness `q` and `eq_proof : Eq n (mul a
/// q)` — local copy of `divisibility.rs`'s private `dvd_intro`.
fn dvd_intro(
    d: &mut NatDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// Eliminate `dvd_hyp : dvd divisor dividend`, continuing with the witness
/// `q` and `eq_proof : Eq dividend (mul divisor q)` to build a proof of
/// `goal` (which must not mention `q`) — local copy of `divisibility.rs`'s
/// private `dvd_elim`.
fn dvd_elim(
    d: &mut NatDev<'_>,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d
        .kernel()
        .lam(anon, dvd_ty, goal, crate::BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec_name = d.prelude().logic.exists_rec;
    let rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

/// `h : Le a b`, `heq : Eq b c ⊢ Le a c` — local copy of `binomial.rs`'s
/// private `rewrite_le_rhs`.
fn rewrite_le_rhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    heq: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b, &|d, x| d.le(a, x));
    d.transport(b, motive, h, c, heq)
}

/// `h : Le a b`, `heq : Eq a a2 ⊢ Le a2 b` — local copy of `binomial.rs`'s
/// private `rewrite_le_lhs`.
fn rewrite_le_lhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    a2: ExprId,
    b: ExprId,
    heq: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = d.eq_motive(a, &|d, x| d.le(x, b));
    d.transport(a, motive, h, a2, heq)
}

// ============================================================================
// Small arithmetic/order combinators.
// ============================================================================

/// `pos_q : Lt zero q`, `hab : Lt a b` ⊢ `Lt (mul q a) (mul q b)` — the
/// `mpr` direction of `Nat.mul_lt_mul_left`, extracted via
/// `helpers::iff_reverse`.
fn scale_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    a: ExprId,
    b: ExprId,
    pos_q: ExprId,
    hab: ExprId,
) -> ExprId {
    let p = *p;
    let iff_proof = d.lemma(p.mul_lt_mul_left, &[q, a, b, pos_q]);
    let mul_qa = d.mul(q, a);
    let mul_qb = d.mul(q, b);
    let lhs_ty = d.lt(mul_qa, mul_qb);
    let rhs_ty = d.lt(a, b);
    let mpr = iff_reverse(d, lhs_ty, rhs_ty, iff_proof);
    d.apply(mpr, &[hab])
}

/// `sumRange` is monotone in its bound: `h_le : Le m1 m2 ⊢ Le (sumRange g m1)
/// (sumRange g m2)`. Induction on the `Le` DERIVATION (`Nat.le.rec`), the
/// same pattern `order.rs` uses for `add_le_add_left`/`le_trans`.
fn sum_range_mono(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    m1: ExprId,
    m2: ExprId,
    h_le: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let sr_m1 = d.sum_range(g, m1);

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let sr_x = d.sum_range(g, x);
        let body = d.le(sr_m1, sr_x);
        let dom = d.le(m1, x);
        let inner = d.kernel().lam(anon, dom, body, crate::BinderInfo::Default);
        d.lam_fv(x_fv, nat, inner)
    };
    let minor_refl = d.lemma(p.le_refl, &[sr_m1]);
    let minor_step = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx_ty = d.le(m1, x);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let sr_x = d.sum_range(g, x);
        let ih_ty = d.le(sr_m1, sr_x);
        let gx = d.apply(g, &[x]);
        let sx = d.succ(x);
        let sr_sx = d.sum_range(g, sx);
        let sr_succ_eq = d.lemma(p.sum_range_succ, &[g, x]); // Eq(sumRange g (succ x))(add sr_x gx)
        let ext = d.lemma(p.le_add_right, &[sr_x, gx]); // Le sr_x (add sr_x gx)
        let add_sx_gx = d.add(sr_x, gx);
        let combined = d.lemma(p.le_trans, &[sr_m1, sr_x, add_sx_gx, ih, ext]); // Le sr_m1 (add sr_x gx)
        let symm_eq = d.symm(sr_sx, add_sx_gx, sr_succ_eq); // Eq (add sr_x gx) sr_sx
        let rewritten = rewrite_le_rhs(d, sr_m1, add_sx_gx, sr_sx, symm_eq, combined);
        let l_ih = d.lam_fv(ih_fv, ih_ty, rewritten);
        let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
        d.lam_fv(x_fv, nat, l_hx)
    };
    d.const_app(p.le_rec, &[m1, motive, minor_refl, minor_step, m2, h_le])
}

/// `ha : Le a1 a2`, `hb : Le b1 b2` ⊢ `Le (add a1 b1) (add a2 b2)`.
#[allow(clippy::too_many_arguments)]
fn add_le_add(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a1: ExprId,
    a2: ExprId,
    b1: ExprId,
    b2: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = *p;
    let step1 = d.lemma(p.add_le_add_right, &[b1, a1, a2, ha]); // Le(add a1 b1)(add a2 b1)
    let step2 = d.lemma(p.add_le_add_left, &[a2, b1, b2, hb]); // Le(add a2 b1)(add a2 b2)
    let add_a1_b1 = d.add(a1, b1);
    let add_a2_b1 = d.add(a2, b1);
    let add_a2_b2 = d.add(a2, b2);
    d.lemma(p.le_trans, &[add_a1_b1, add_a2_b1, add_a2_b2, step1, step2])
}

// ============================================================================
// The pointwise bound: at a `succ`-shaped divisor, scaling by a positive `q`
// does not decrease the divisor-sum contribution.
// ============================================================================

/// `pos_q : Lt zero q ⊢ Le (mul q (divisor_term m applied at (succ j))) (divisor_term n applied at (mul q (succ j)))`.
///
/// Case-splits on whether `succ j` divides `m`. If it does (`beq (mod m (succ
/// j)) 0 = true`), the divisor term at `m` is `succ j` itself; chasing the
/// `dvd` witness through `mul_assoc`/`mul_comm` shows `mul q (succ j)`
/// divides `n`, so the divisor term at `n` there is `mul q (succ j)` too —
/// equal, hence `Le`. If it does not, the divisor term at `m` is `0`, and
/// `Le zero _` is `Nat.zero_le`.
fn divisor_scale_pointwise_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    m: ExprId,
    n: ExprId,
    pos_q: ExprId,
    j: ExprId,
) -> ExprId {
    let p = *p;
    let sx = d.succ(j);
    let zero = d.zero();

    let mod_m_sx = d.modulo(m, sx);
    let cond_m = d.beq(mod_m_sx, zero);
    let f_val = d.bool_select_nat(cond_m, sx, zero);
    let mul_q_fval = d.mul(q, f_val);

    let mul_q_sx = d.mul(q, sx);
    let mod_n_qsx = d.modulo(n, mul_q_sx);
    let cond_n = d.beq(mod_n_qsx, zero);
    let g_val = d.bool_select_nat(cond_n, mul_q_sx, zero);

    let goal = d.le(mul_q_fval, g_val);

    let bool_true = d.bool_true();
    let bool_false = d.bool_false();
    let true_ty = d.bool_eq(cond_m, bool_true);
    let false_ty = d.bool_eq(cond_m, bool_false);
    let split = bool_true_or_false(d, &p, cond_m);

    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let sel_m = bool_congr_nat(d, cond_m, bool_true, heq, &move |d, x| {
            d.bool_select_nat(x, sx, zero)
        }); // Eq f_val sx  (RHS defeq sx via iota)

        let mod_eq_zero = d.lemma(p.eq_of_beq_eq_true, &[mod_m_sx, zero, heq]); // Eq mod_m_sx zero

        let pos_sx = d.zero_lt_succ(j);
        let bridge_m = mod_eq_zero_iff_dvd_general(d, &p, sx, pos_sx, m); // Iff(Eq mod_m_sx zero)(dvd sx m)
        let eq_mod_m_ty = d.eq(mod_m_sx, zero);
        let dvd_sx_m_ty = d.dvd(sx, m);
        let fwd = iff_forward(d, eq_mod_m_ty, dvd_sx_m_ty, bridge_m);
        let dvd_sx_m = d.apply(fwd, &[mod_eq_zero]);

        let body = dvd_elim(d, sx, m, goal, dvd_sx_m, &move |d, c, eq_m_sxc| {
            // eq_m_sxc : Eq m (mul sx c)
            let n_local = n; // fixed outer capture
            let mul_q_m = d.mul(q, m);
            let mul_sx_c = d.mul(sx, c);
            let step1 = d.congr(m, mul_sx_c, eq_m_sxc, &move |d, t| d.mul(q, t)); // Eq(mul q m)(mul q(mul sx c))
            let mul_qsx_c = d.mul(mul_q_sx, c);
            let assoc = d.lemma(p.mul_assoc, &[q, sx, c]); // Eq(mul(mul q sx)c)(mul q(mul sx c))
            let mul_q_mulsxc = d.mul(q, mul_sx_c);
            let assoc_symm = d.symm(mul_qsx_c, mul_q_mulsxc, assoc); // Eq(mul q(mul sx c))(mul(mul q sx)c)
            let (_, n_eq) = d.chain(mul_q_m, &[(mul_q_mulsxc, step1), (mul_qsx_c, assoc_symm)]);
            // n_eq : Eq (mul q m) (mul (mul q sx) c) -- but we need it about `n`, not `mul q m`.
            // n was not asserted equal to mul q m here; the caller (main proof)
            // fixes n := mul q m, so this IS the needed equation directly.
            let dvd_qsx_n = dvd_intro(d, mul_q_sx, n_local, c, n_eq); // dvd (mul q sx) n

            let pos_sx2 = d.zero_lt_succ(j);
            let pos_qsx = d.lemma(p.one_le_mul, &[q, sx, pos_q, pos_sx2]); // Le one (mul q sx) ~ Lt zero (mul q sx)
            let bridge_n = mod_eq_zero_iff_dvd_general(d, &p, mul_q_sx, pos_qsx, n_local); // Iff(Eq mod_n_qsx zero)(dvd mul_q_sx n)
            let eq_mod_n_ty = d.eq(mod_n_qsx, zero);
            let dvd_qsx_n_ty = d.dvd(mul_q_sx, n_local);
            let rev = iff_reverse(d, eq_mod_n_ty, dvd_qsx_n_ty, bridge_n);
            let mod_n_qsx_zero = d.apply(rev, &[dvd_qsx_n]); // Eq mod_n_qsx zero

            let cond_n_true = d.lemma(p.beq_eq_true_of_eq, &[mod_n_qsx, zero, mod_n_qsx_zero]); // Eq cond_n true

            let sel_n = bool_congr_nat(d, cond_n, bool_true, cond_n_true, &move |d, x| {
                d.bool_select_nat(x, mul_q_sx, zero)
            }); // Eq g_val mul_q_sx

            let congr_fval = d.congr(f_val, sx, sel_m, &move |d, t| d.mul(q, t)); // Eq mul_q_fval mul_q_sx
            let le_refl_mqsx = d.lemma(p.le_refl, &[mul_q_sx]);
            let symm_congr = d.symm(mul_q_fval, mul_q_sx, congr_fval); // Eq mul_q_sx mul_q_fval
            let step_lhs =
                rewrite_le_lhs(d, mul_q_sx, mul_q_fval, mul_q_sx, symm_congr, le_refl_mqsx); // Le mul_q_fval mul_q_sx
            let symm_seln = d.symm(g_val, mul_q_sx, sel_n); // Eq mul_q_sx g_val
            rewrite_le_rhs(d, mul_q_fval, mul_q_sx, g_val, symm_seln, step_lhs) // Le mul_q_fval g_val
        });
        d.lam_fv(heq_fv, true_ty, body)
    };

    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let sel_m_false = bool_congr_nat(d, cond_m, bool_false, heq, &move |d, x| {
            d.bool_select_nat(x, sx, zero)
        }); // Eq f_val zero  (RHS defeq zero via iota)
        let congr_fval = d.congr(f_val, zero, sel_m_false, &move |d, t| d.mul(q, t)); // Eq mul_q_fval (mul q zero)
        let mul_q_zero = d.mul(q, zero);
        let mqz_eq_zero = d.lemma(p.mul_zero, &[q]); // Eq (mul q zero) zero
        let (_, mqf_eq_zero) =
            d.chain(mul_q_fval, &[(mul_q_zero, congr_fval), (zero, mqz_eq_zero)]);
        let zero_le_gval = d.lemma(p.zero_le, &[g_val]);
        let symm_eq = d.symm(mul_q_fval, zero, mqf_eq_zero);
        let body = rewrite_le_lhs(d, zero, mul_q_fval, g_val, symm_eq, zero_le_gval);
        d.lam_fv(heq_fv, false_ty, body)
    };

    super::primes::or_cases(
        d,
        &p,
        true_ty,
        false_ty,
        goal,
        true_minor,
        false_minor,
        split,
    )
}

// ============================================================================
// `Nat.sum_divisors_scale_le`.
// ============================================================================

/// `Nat.sum_divisors_scale_le : ∀ q m, Lt zero q → Le (mul q (sumDivisors
/// m)) (sumDivisors (mul q m))`.
///
/// `mul_sumRange` turns the LHS into `sumRange F (succ m)` where `F := fun i
/// => mul q (divisor_term m applied at i)`; the goal becomes an induction on
/// `m` proving `Le (sumRange F (succ x)) (sumRange (divisor_term n) (succ
/// (mul q x)))` (`n := mul q m`, fixed), peeling one term off each side per
/// step and bounding the new term via [`divisor_scale_pointwise_succ`]
/// (always invoked at a `succ`-shaped index, by construction of the
/// induction) plus [`sum_range_mono`] to bridge `succ (mul q j)` up to `mul q
/// (succ j)`.
pub(super) fn declare_sum_divisors_scale_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.sum_divisors_scale_le, 2, &|d, v| {
        let q = v[0];
        let m = v[1];
        let zero = d.zero();
        let pos_q_ty = d.lt(zero, q);

        let sum_m = d.const_app(p.sum_divisors, &[m]);
        let mul_q_summ = d.mul(q, sum_m);
        let mul_q_m = d.mul(q, m);
        let sum_qm = d.const_app(p.sum_divisors, &[mul_q_m]);
        let concl = d.le(mul_q_summ, sum_qm);
        let stmt = d.arrow(pos_q_ty, concl);

        let pos_q_fv = d.fresh_fvar();
        let pos_q = d.kernel().fvar(pos_q_fv);

        let n = d.mul(q, m); // same expr as mul_q_m, rebuilt for clarity below
        let f_m = divisor_term(d, m);
        let g_n = divisor_term(d, n);

        // F := fun i => mul q (apply f_m i) -- matches `mul_sumRange`'s own
        // internal `scaled_fn` construction (algebra.rs) exactly.
        let f_term = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f_m, &[i]);
            let body = d.mul(q, fi);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };

        let stmt_at = move |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let sx = d.succ(x);
            let lhs = d.sum_range(f_term, sx);
            let qx = d.mul(q, x);
            let sqx = d.succ(qx);
            let rhs = d.sum_range(g_n, sqx);
            d.le(lhs, rhs)
        };

        let base = move |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let sz = d.succ(zero);

            // LHS: sumRange f_term sz = f_term(0)
            let sr_f_sz_eq = d.lemma(p.sum_range_succ, &[f_term, zero]);
            let sr_f_z_eq = d.lemma(p.sum_range_zero, &[f_term]);
            let fm0 = d.apply(f_m, &[zero]);
            let f0 = d.mul(q, fm0);
            let sr_f_zero = d.sum_range(f_term, zero);
            let add_srfz_f0 = d.add(sr_f_zero, f0);
            let add_zero_f0 = d.add(zero, f0);
            let step_a = d.congr(sr_f_zero, zero, sr_f_z_eq, &move |d, t| d.add(t, f0));
            let za1 = d.lemma(p.zero_add, &[f0]);
            let sr_f_sz = d.sum_range(f_term, sz);
            let (_, lhs_eq) = d.chain(
                sr_f_sz,
                &[(add_srfz_f0, sr_f_sz_eq), (add_zero_f0, step_a), (f0, za1)],
            );
            // lhs_eq : Eq (sumRange f_term sz) f0

            let fm0_eq_zero = divisor_term_zero_eq_zero(d, &p, m);
            let mul_q_zero = d.mul(q, zero);
            let congr_fm0 = d.congr(fm0, zero, fm0_eq_zero, &move |d, t| d.mul(q, t));
            let mqz_eq_zero = d.lemma(p.mul_zero, &[q]);
            let (_, f0_eq_zero) = d.chain(f0, &[(mul_q_zero, congr_fm0), (zero, mqz_eq_zero)]);
            let (_, lhs_eq_zero) = d.chain(sr_f_sz, &[(f0, lhs_eq), (zero, f0_eq_zero)]);
            // lhs_eq_zero : Eq (sumRange f_term sz) zero

            // RHS: sumRange g_n (succ (mul q zero)) = g_n(0)
            let mul_q_0 = d.mul(q, zero);
            let mul_q_0_eq_zero = d.lemma(p.mul_zero, &[q]);
            let s_mul_q_0 = d.succ(mul_q_0);
            let succ_rewrite = d.congr(mul_q_0, zero, mul_q_0_eq_zero, &move |d, t| d.succ(t));
            let sr_g_smq0 = d.sum_range(g_n, s_mul_q_0);
            let sr_g_sz = d.sum_range(g_n, sz);
            let sr_g_sz_rewritten = d.congr(s_mul_q_0, sz, succ_rewrite, &move |d, t| {
                d.sum_range(g_n, t)
            });

            let sr_g_sz_eq = d.lemma(p.sum_range_succ, &[g_n, zero]);
            let sr_g_z_eq = d.lemma(p.sum_range_zero, &[g_n]);
            let g0 = d.apply(g_n, &[zero]);
            let sr_g_zero = d.sum_range(g_n, zero);
            let add_srgz_g0 = d.add(sr_g_zero, g0);
            let add_zero_g0 = d.add(zero, g0);
            let step_b = d.congr(sr_g_zero, zero, sr_g_z_eq, &move |d, t| d.add(t, g0));
            let za2 = d.lemma(p.zero_add, &[g0]);
            let (_, sr_g_sz_eq_g0) = d.chain(
                sr_g_sz,
                &[(add_srgz_g0, sr_g_sz_eq), (add_zero_g0, step_b), (g0, za2)],
            );

            let g0_eq_zero = divisor_term_zero_eq_zero(d, &p, n);
            let (_, rhs_full_eq) = d.chain(
                sr_g_smq0,
                &[
                    (sr_g_sz, sr_g_sz_rewritten),
                    (g0, sr_g_sz_eq_g0),
                    (zero, g0_eq_zero),
                ],
            );
            // rhs_full_eq : Eq (sumRange g_n s_mul_q_0) zero

            let le_zero_zero = d.lemma(p.le_refl, &[zero]);
            let symm_rhs = d.symm(sr_g_smq0, zero, rhs_full_eq);
            let rhs_rewritten = rewrite_le_rhs(d, zero, zero, sr_g_smq0, symm_rhs, le_zero_zero);
            let symm_lhs = d.symm(sr_f_sz, zero, lhs_eq_zero);
            rewrite_le_lhs(d, zero, sr_f_sz, sr_g_smq0, symm_lhs, rhs_rewritten)
        };

        let step = move |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let mul_q_j = d.mul(q, j);
            let s_mul_q_j = d.succ(mul_q_j);
            let mul_q_sj = d.mul(q, sj);

            // ih : Le (sumRange f_term sj) (sumRange g_n s_mul_q_j)
            let sr_f_sj = d.sum_range(f_term, sj);
            let f_sj = d.apply(f_term, &[sj]);
            let sr_f_ssj_eq = d.lemma(p.sum_range_succ, &[f_term, sj]); // Eq(sumRange f_term(succ sj))(add sr_f_sj f_sj)
            let sr_g_smqj = d.sum_range(g_n, s_mul_q_j);
            let step1 = d.lemma(p.add_le_add_right, &[f_sj, sr_f_sj, sr_g_smqj, ih]);
            // step1 : Le (add sr_f_sj f_sj) (add sr_g_smqj f_sj)

            let pw = divisor_scale_pointwise_succ(d, &p, q, m, n, pos_q, j);
            // pw : Le (mul q (f_m (succ j))) (g_n (mul q (succ j)))  ~defeq~  Le f_sj (apply g_n mul_q_sj)
            let g_mqsj = d.apply(g_n, &[mul_q_sj]);

            let lt_succ = d.lemma(p.lt_succ_self, &[j]); // Lt j sj
            let bound_lt = scale_lt(d, &p, q, j, sj, pos_q, lt_succ); // Lt (mul q j) (mul q sj) = Le s_mul_q_j (mul q sj)
            let mono_step = sum_range_mono(d, &p, g_n, s_mul_q_j, mul_q_sj, bound_lt);
            // mono_step : Le sr_g_smqj (sumRange g_n mul_q_sj)

            let sr_g_mqsj = d.sum_range(g_n, mul_q_sj);
            let step2 = add_le_add(d, &p, sr_g_smqj, sr_g_mqsj, f_sj, g_mqsj, mono_step, pw);
            // step2 : Le (add sr_g_smqj f_sj) (add sr_g_mqsj g_mqsj)

            let add_srfsj_fsj = d.add(sr_f_sj, f_sj);
            let add_srgsmqj_fsj = d.add(sr_g_smqj, f_sj);
            let add_srgmqsj_gmqsj = d.add(sr_g_mqsj, g_mqsj);
            let combined = d.lemma(
                p.le_trans,
                &[
                    add_srfsj_fsj,
                    add_srgsmqj_fsj,
                    add_srgmqsj_gmqsj,
                    step1,
                    step2,
                ],
            );
            // combined : Le (add sr_f_sj f_sj) (add sr_g_mqsj g_mqsj)

            let sr_g_succ_mqsj_eq = d.lemma(p.sum_range_succ, &[g_n, mul_q_sj]);
            // Eq (sumRange g_n (succ mul_q_sj)) (add sr_g_mqsj g_mqsj)
            let succ_mul_q_sj = d.succ(mul_q_sj);
            let sr_g_succ_mqsj = d.sum_range(g_n, succ_mul_q_sj);
            let symm_final = d.symm(sr_g_succ_mqsj, add_srgmqsj_gmqsj, sr_g_succ_mqsj_eq);
            let final_le = rewrite_le_rhs(
                d,
                add_srfsj_fsj,
                add_srgmqsj_gmqsj,
                sr_g_succ_mqsj,
                symm_final,
                combined,
            );
            // final_le : Le (add sr_f_sj f_sj) (sumRange g_n (succ mul_q_sj))

            let succ_sj = d.succ(sj);
            let sr_f_succ_sj = d.sum_range(f_term, succ_sj);
            let symm_lhs = d.symm(sr_f_succ_sj, add_srfsj_fsj, sr_f_ssj_eq);
            rewrite_le_lhs(
                d,
                add_srfsj_fsj,
                sr_f_succ_sj,
                sr_g_succ_mqsj,
                symm_lhs,
                final_le,
            )
        };

        let induction_result = d.induct(&stmt_at, &base, &step, m);
        // induction_result : Le (sumRange f_term (succ m)) (sumRange g_n (succ (mul q m)))

        let succ_m = d.succ(m);
        let mul_sr_eq = d.lemma(p.mul_sum_range, &[q, f_m, succ_m]);
        // Eq (mul q (sumRange f_m succ_m)) (sumRange f_term succ_m)
        // `mul q (sumDivisors m)` is defeq `mul q (sumRange f_m succ_m)`.
        let sr_f_succm = d.sum_range(f_term, succ_m);
        let symm_unfold = d.symm(mul_q_summ, sr_f_succm, mul_sr_eq);
        let proof_concl = rewrite_le_lhs(
            d,
            sr_f_succm,
            mul_q_summ,
            sum_qm,
            symm_unfold,
            induction_result,
        );
        // `sumDivisors (mul q m)` is defeq `sumRange g_n (succ (mul q m))`,
        // matching `induction_result`'s RHS via defeq; no further rewrite needed.

        let proof = d.lam_fv(pos_q_fv, pos_q_ty, proof_concl);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq (divisor_term n applied at zero) zero` — `d = 0` never contributes
/// (`perfect.rs`'s module doc): both `bool_select_nat` branches are `0`
/// there, established via `bool_select_nat_same`.
fn divisor_term_zero_eq_zero(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let remainder = d.modulo(n, zero);
    let cond = d.beq(remainder, zero);
    super::ops::bool_select_nat_same(d, &p, cond, zero)
}

// ============================================================================
// `Nat.abundant_mul_left`, `Nat.abundant_of_dvd`.
// ============================================================================

/// `Nat.abundant_mul_left : ∀ n m, Abundant n → Not (Eq m zero) →
/// Abundant (mul m n)`.
pub(super) fn declare_abundant_mul_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.abundant_mul_left, 2, &|d, v| {
        let n = v[0];
        let m = v[1];
        let abundant_n = d.const_app(p.abundant, &[n]);
        let zero = d.zero();
        let m_ne_zero = {
            let eq_m0 = d.eq(m, zero);
            d.const_app(p.logic.not, &[eq_m0])
        };
        let mul_mn = d.mul(m, n);
        let abundant_mn = d.const_app(p.abundant, &[mul_mn]);
        let inner_ty = d.arrow(m_ne_zero, abundant_mn);
        let stmt = d.arrow(abundant_n, inner_ty);

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv); // Abundant n = Lt (mul 2 n) (sumDivisors n)
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv); // Not (Eq m zero)

        let pos_m = d.lemma(p.zero_lt_of_ne_zero, &[m, hm]); // Lt zero m

        let sum_n = d.const_app(p.sum_divisors, &[n]);
        let scale = d.lemma(p.sum_divisors_scale_le, &[m, n, pos_m]);
        // scale : Le (mul m (sumDivisors n)) (sumDivisors (mul m n))

        let two = d.num(2);
        let two_n = d.mul(two, n);
        let scaled_lt = scale_lt(d, &p, m, two_n, sum_n, pos_m, ha);
        // scaled_lt : Lt (mul m (mul 2 n)) (mul m (sumDivisors n))

        let mul_m_2n = d.mul(m, two_n);
        let mul_m_sumn = d.mul(m, sum_n);
        let sum_mn = d.const_app(p.sum_divisors, &[mul_mn]);
        let lt_trans = d.lemma(
            p.lt_of_lt_of_le,
            &[mul_m_2n, mul_m_sumn, sum_mn, scaled_lt, scale],
        );
        // lt_trans : Lt (mul m (mul 2 n)) (sumDivisors (mul m n))

        // mul m (mul 2 n) = mul 2 (mul m n)
        let mul_m2 = d.mul(m, two);
        let assoc1 = d.lemma(p.mul_assoc, &[m, two, n]); // Eq(mul(mul m 2)n)(mul m(mul 2 n))
        let mul_m2_n = d.mul(mul_m2, n);
        let assoc1_symm = d.symm(mul_m2_n, mul_m_2n, assoc1); // Eq(mul m(mul 2 n))(mul(mul m 2)n)
        let comm_m2 = d.lemma(p.mul_comm, &[m, two]); // Eq(mul m 2)(mul 2 m)
        let two_m = d.mul(two, m);
        let comm_congr = d.congr(mul_m2, two_m, comm_m2, &move |d, t| d.mul(t, n)); // Eq(mul(mul m 2)n)(mul(mul 2 m)n)
        let two_m_n = d.mul(two_m, n);
        let assoc2 = d.lemma(p.mul_assoc, &[two, m, n]); // Eq(mul(mul 2 m)n)(mul 2(mul m n))
        let two_mn = d.mul(two, mul_mn);
        let (_, lhs_eq) = d.chain(
            mul_m_2n,
            &[
                (mul_m2_n, assoc1_symm),
                (two_m_n, comm_congr),
                (two_mn, assoc2),
            ],
        );
        // lhs_eq : Eq (mul m (mul 2 n)) (mul 2 (mul m n))

        // `Lt a b` is literally `Le (succ a) b`, so rewriting the Lt's LHS is a
        // congr under `succ` followed by the ordinary `Le`-rewrite helper.
        let succ_mul_m_2n = d.succ(mul_m_2n);
        let succ_two_mn = d.succ(two_mn);
        let succ_lhs_eq = d.congr(mul_m_2n, two_mn, lhs_eq, &move |d, t| d.succ(t));
        let final_proof =
            rewrite_le_lhs(d, succ_mul_m_2n, succ_two_mn, sum_mn, succ_lhs_eq, lt_trans);
        // final_proof : Le (succ two_mn) sum_mn = Lt two_mn sum_mn = Abundant (mul m n)

        let inner = d.lam_fv(hm_fv, m_ne_zero, final_proof);
        let proof = d.lam_fv(ha_fv, abundant_n, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.abundant_of_dvd : ∀ m n, Abundant m → dvd m n → Not (Eq n zero) →
/// Abundant n`.
pub(super) fn declare_abundant_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.abundant_of_dvd, 2, &|d, v| {
        let m = v[0];
        let n = v[1];
        let abundant_m = d.const_app(p.abundant, &[m]);
        let dvd_mn = d.dvd(m, n);
        let zero = d.zero();
        let n_ne_zero = {
            let eq_n0 = d.eq(n, zero);
            d.const_app(p.logic.not, &[eq_n0])
        };
        let abundant_n = d.const_app(p.abundant, &[n]);
        let inner3 = d.arrow(n_ne_zero, abundant_n);
        let inner2_ty = d.arrow(dvd_mn, inner3);
        let stmt = d.arrow(abundant_m, inner2_ty);

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv); // Abundant m
        let hdvd_fv = d.fresh_fvar();
        let hdvd = d.kernel().fvar(hdvd_fv); // dvd m n
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv); // Not (Eq n zero)

        let body = dvd_elim(d, m, n, abundant_n, hdvd, &move |d, qw, eq_n_mqw| {
            // eq_n_mqw : Eq n (mul m qw)
            let mul_m_qw = d.mul(m, qw);
            // qw ≠ 0 : suppose Eq qw zero, derive Eq n zero, contradict hn.
            let qw_ne_zero = {
                let hq0_fv = d.fresh_fvar();
                let hq0 = d.kernel().fvar(hq0_fv); // Eq qw zero
                let congr_step = d.congr(qw, zero, hq0, &move |d, t| d.mul(m, t)); // Eq(mul m qw)(mul m zero)
                let mul_m_zero = d.mul(m, zero);
                let mmz_eq_zero = d.lemma(p.mul_zero, &[m]);
                let (_, n_eq_zero) = d.chain(
                    n,
                    &[
                        (mul_m_qw, eq_n_mqw),
                        (mul_m_zero, congr_step),
                        (zero, mmz_eq_zero),
                    ],
                );
                let contra = d.apply(hn, &[n_eq_zero]);
                let eq_qw0 = d.eq(qw, zero);
                d.lam_fv(hq0_fv, eq_qw0, contra)
            };
            let pos_qw = d.lemma(p.zero_lt_of_ne_zero, &[qw, qw_ne_zero]); // Lt zero qw

            let sum_m = d.const_app(p.sum_divisors, &[m]);
            let scale = d.lemma(p.sum_divisors_scale_le, &[qw, m, pos_qw]);
            // scale : Le (mul qw (sumDivisors m)) (sumDivisors (mul qw m))

            let two = d.num(2);
            let two_m = d.mul(two, m);
            let scaled_lt = scale_lt(d, &p, qw, two_m, sum_m, pos_qw, ha);
            // scaled_lt : Lt (mul qw (mul 2 m)) (mul qw (sumDivisors m))

            let mul_qw_2m = d.mul(qw, two_m);
            let mul_qw_summ = d.mul(qw, sum_m);
            let mul_qw_m = d.mul(qw, m);
            let sum_qwm = d.const_app(p.sum_divisors, &[mul_qw_m]);
            let lt_trans = d.lemma(
                p.lt_of_lt_of_le,
                &[mul_qw_2m, mul_qw_summ, sum_qwm, scaled_lt, scale],
            );
            // lt_trans : Lt (mul qw (mul 2 m)) (sumDivisors (mul qw m))

            // n = mul m qw = mul qw m
            let comm_mqw = d.lemma(p.mul_comm, &[m, qw]); // Eq(mul m qw)(mul qw m)
            let (_, n_eq_mul_qw_m) = d.chain(n, &[(mul_m_qw, eq_n_mqw), (mul_qw_m, comm_mqw)]);
            // n_eq_mul_qw_m : Eq n (mul qw m)
            let symm_n = d.symm(n, mul_qw_m, n_eq_mul_qw_m); // Eq (mul qw m) n

            // sumDivisors(mul qw m) -> sumDivisors n
            let sum_n = d.const_app(p.sum_divisors, &[n]);
            let congr_sum = d.congr(mul_qw_m, n, symm_n, &move |d, t| {
                d.const_app(p.sum_divisors, &[t])
            });
            // congr_sum : Eq (sumDivisors (mul qw m)) (sumDivisors n)

            // mul qw (mul 2 m) = mul 2 n
            let mul_qw2 = d.mul(qw, two);
            let assoc1 = d.lemma(p.mul_assoc, &[qw, two, m]); // Eq(mul(mul qw 2)m)(mul qw(mul 2 m))
            let mul_qw2_m = d.mul(mul_qw2, m);
            let assoc1_symm = d.symm(mul_qw2_m, mul_qw_2m, assoc1); // Eq(mul qw(mul 2 m))(mul(mul qw 2)m)
            let comm_qw2 = d.lemma(p.mul_comm, &[qw, two]); // Eq(mul qw 2)(mul 2 qw)
            let two_qw = d.mul(two, qw);
            let comm_congr = d.congr(mul_qw2, two_qw, comm_qw2, &move |d, t| d.mul(t, m));
            let two_qw_m = d.mul(two_qw, m);
            let assoc2 = d.lemma(p.mul_assoc, &[two, qw, m]); // Eq(mul(mul 2 qw)m)(mul 2(mul qw m))
            let two_mul_qw_m = d.mul(two, mul_qw_m);
            let (_, lhs_pre) = d.chain(
                mul_qw_2m,
                &[
                    (mul_qw2_m, assoc1_symm),
                    (two_qw_m, comm_congr),
                    (two_mul_qw_m, assoc2),
                ],
            );
            // lhs_pre : Eq (mul qw (mul 2 m)) (mul 2 (mul qw m))
            let two_n = d.mul(two, n);
            let congr_two = d.congr(mul_qw_m, n, symm_n, &move |d, t| d.mul(two, t));
            // congr_two : Eq (mul 2 (mul qw m)) (mul 2 n)
            let (_, lhs_eq) = d.chain(mul_qw_2m, &[(two_mul_qw_m, lhs_pre), (two_n, congr_two)]);
            // lhs_eq : Eq (mul qw (mul 2 m)) (mul 2 n)

            let succ_mul_qw_2m = d.succ(mul_qw_2m);
            let succ_two_n = d.succ(two_n);
            let succ_lhs_eq = d.congr(mul_qw_2m, two_n, lhs_eq, &move |d, t| d.succ(t));
            let step1 = rewrite_le_lhs(
                d,
                succ_mul_qw_2m,
                succ_two_n,
                sum_qwm,
                succ_lhs_eq,
                lt_trans,
            );
            // step1 : Le (succ two_n) sum_qwm = Lt two_n sum_qwm

            rewrite_le_rhs(d, succ_two_n, sum_qwm, sum_n, congr_sum, step1)
            // : Le (succ two_n) sum_n = Lt two_n sum_n = Abundant n
        });

        let inner2 = d.lam_fv(hn_fv, n_ne_zero, body);
        let inner1 = d.lam_fv(hdvd_fv, dvd_mn, inner2);
        let proof = d.lam_fv(ha_fv, abundant_m, inner1);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.sum_divisors_scale_le`, `Nat.abundant_mul_left`,
/// `Nat.abundant_of_dvd`. Must run after
/// [`super::abundant_deficient::declare_abundant_deficient_all`] (needs
/// `Nat.Abundant`) and [`super::perfect::declare_perfect_all`] (needs
/// `Nat.sumDivisors`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_divisor_sum_scale_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_sum_divisors_scale_le(d, p)?;
    declare_abundant_mul_left(d, p)?;
    declare_abundant_of_dvd(d, p)?;
    Ok(())
}
