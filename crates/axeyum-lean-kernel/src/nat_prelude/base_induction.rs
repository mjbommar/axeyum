//! `Nat.base_induction`: an induction principle mirroring a number's base-`b`
//! representation (Lean core `Init.Data.Nat.Div.Lemmas`, not Mathlib itself --
//! `Nat.base_induction`'s `source_group`/`module` in
//! `artifacts/autogenesis/nursery-v2-extension.json` names
//! `Init.Data.Nat.Div.Lemmas`).
//!
//! ```text
//! theorem base_induction {P : Nat -> Prop} {n : Nat} (b : Nat) (hb : 1 < b)
//!     (single : ∀ m, m < b -> P m)
//!     (digit : ∀ m k, k < b -> 0 < m -> P m -> P (b * m + k)) : P n
//! ```
//!
//! `P : Nat -> Prop` is a genuine motive parameter, so [`d.theorem`]'s
//! `Nat`-only arity mechanism cannot build this statement -- the declaration
//! is assembled by hand (`pi_fv`/`lam_fv` chains), the same way `dvd`/`mod_eq`
//! are in `divisibility.rs`/`modular.rs`.
//!
//! Unlike a fuel-recursive `ml430` mirror (`Nat.binaryRec` et al., which can
//! never match Mathlib's `WellFounded.fix`-based construction because a fuel
//! row must return a value for arbitrary `n` from only `motive 0`), this one
//! genuinely CAN be built the same way Mathlib builds it: `P` is fixed at
//! `Prop`, not an arbitrary `Sort*` motive, so proving `∀ n, P n` needs no
//! dependent computational recursor at all -- ordinary strong induction over
//! `Nat.lt`'s well-foundedness suffices, and this prelude already has that
//! primitive (`NatPrelude::lt_well_founded` + `WellFounded.fix`, used the same
//! way by `declare_gcd_semantics`/`declare_gcd_bezout`/
//! `declare_exists_prime_factorization`/`declare_irrational` already).
//!
//! Route: `WellFounded.fix Nat Nat.lt P lt_well_founded step n`, where `step`
//! (given `v` and `ih : ∀ y, y<v -> P y`) case-splits `lt_or_ge v b`:
//!
//!   - `Lt v b`: `single v` directly.
//!   - `Le b v`: decompose `v = b*qv+rv` (`div_mod_reconstructed`, a local
//!     copy of `group.rs`'s helper -- this file's own per-file convention for
//!     it), case-split `qv` (`qv=0` contradicts `Le b v` since it would force
//!     `v=rv<b`; `qv=succ qvpred` is the live case). Bound `qv<v` via
//!     `mul_le_mul_left(qv,2,b,hb)` (giving `mul qv 2 <= mul qv b`),
//!     `qv < mul qv 2` (from `le_add_right(qv,qvpred)` lifted by
//!     `le_succ_succ`, since `mul qv 2` is defeq `add qv qv`), `mul_comm`, and
//!     `v >= mul b qv` (`le_add_right` again) -- three `lt_of_lt_of_le`-style
//!     chains. Then `digit qv rv (rv<b) (0<qv) (ih qv (qv<v)) : P(b*qv+rv)`,
//!     transported along `v = b*qv+rv` to `P v`.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use super::steps::absurd;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Reconstruct `divMod dd x (div x dd) (mod x dd)` for any `x`, given
/// `pos_dd : Lt zero dd`. A local copy of `group.rs`'s private
/// `div_mod_reconstructed` (per this prelude's established convention --
/// `div_mod_lemmas.rs`, `fermat.rs`, `perfect.rs`, `totient.rs` each carry
/// their own copy of the same shape).
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

/// `Nat.base_induction`. See the module doc for the route.
///
/// Must run after `declare_gcd_semantics` (or any earlier user of
/// `lt_well_founded`/`WellFounded.fix`), `declare_order`/`declare_order_more`
/// (`lt_or_ge`, `le_add_right`, `le_succ_succ`, `le_trans`, `lt_of_lt_of_le`,
/// `lt_of_le_of_lt`, `lt_irrefl`, `lt_succ_self`), `declare_divisibility`
/// (`div_mod_exec`), `declare_succ_pred_of_pos`, and
/// `declare_multiplicative_theorems`/`declare_additive_theorems` (`mul_comm`,
/// `mul_le_mul_left`, `zero_add`, `zero_lt_succ`).
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_base_induction(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let anon = d.anon_name();
    let p_domain = d.kernel().pi(anon, nat, prop, BinderInfo::Default);

    let p_fv = d.fresh_fvar();
    let p_var = d.kernel().fvar(p_fv);
    let n_fv = d.fresh_fvar();
    let n_var = d.kernel().fvar(n_fv);
    let b_fv = d.fresh_fvar();
    let b_var = d.kernel().fvar(b_fv);

    let one = d.num(1);
    let two = d.num(2);
    let zero = d.zero();

    let hb_ty = d.lt(one, b_var);

    // single : ∀ m, Lt m b -> P m
    let single_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let lt_m_b = d.lt(m, b_var);
        let p_m = d.apply(p_var, &[m]);
        let body = d.arrow(lt_m_b, p_m);
        d.pi_fv(m_fv, nat, body)
    };

    // digit : ∀ m k, Lt k b -> Lt zero m -> P m -> P (add (mul b m) k)
    let digit_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lt_k_b = d.lt(k, b_var);
        let pos_m = d.lt(zero, m);
        let p_m = d.apply(p_var, &[m]);
        let bm = d.mul(b_var, m);
        let bmk = d.add(bm, k);
        let p_bmk = d.apply(p_var, &[bmk]);
        let inner = d.arrow(p_m, p_bmk);
        let inner = d.arrow(pos_m, inner);
        let inner = d.arrow(lt_k_b, inner);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(m_fv, nat, with_k)
    };

    let concl_n = d.apply(p_var, &[n_var]);
    let stmt_inner = {
        let with_digit = d.arrow(digit_ty, concl_n);
        let with_single = d.arrow(single_ty, with_digit);
        d.arrow(hb_ty, with_single)
    };
    let ty = {
        let with_b = d.pi_fv(b_fv, nat, stmt_inner);
        let with_n = d.pi_fv(n_fv, nat, with_b);
        d.pi_fv(p_fv, p_domain, with_n)
    };

    let hb_fv = d.fresh_fvar();
    let hb_var = d.kernel().fvar(hb_fv);
    let single_fv = d.fresh_fvar();
    let single_var = d.kernel().fvar(single_fv);
    let digit_fv = d.fresh_fvar();
    let digit_var = d.kernel().fvar(digit_fv);

    // step_recursive_ty(upper) : ∀ y, Lt y upper -> P y
    let step_recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| -> ExprId {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let lt_y_upper = d.lt(y, upper);
        let p_y = d.apply(p_var, &[y]);
        let body = d.arrow(lt_y_upper, p_y);
        d.pi_fv(y_fv, nat, body)
    };

    // pos_b : Lt zero b, from hb : Lt one b = Le two b via Le one two.
    let pos_b = {
        let le_one_two = d.lemma(p.le_succ, &[one]); // Le one (succ one) = Le one two
        d.lemma(p.le_trans, &[one, two, b_var, le_one_two, hb_var]) // Le one b = Lt zero b
    };

    // step : ∀ v, (∀ y, Lt y v -> P y) -> P v
    let step = {
        let v_fv = d.fresh_fvar();
        let v_var = d.kernel().fvar(v_fv);
        let ih_fv = d.fresh_fvar();
        let ih_var = d.kernel().fvar(ih_fv);
        let recursive_v = step_recursive_ty(d, v_var);
        let concl_v = d.apply(p_var, &[v_var]);

        let lt_ty = d.lt(v_var, b_var);
        let ge_ty = d.le(b_var, v_var);
        let dichotomy = d.lemma(p.lt_or_ge, &[v_var, b_var]); // Or (Lt v b) (Le b v)

        // Case Lt v b: single v directly.
        let minor_lt = {
            let lt_fv = d.fresh_fvar();
            let lt_var = d.kernel().fvar(lt_fv);
            let body = d.apply(single_var, &[v_var, lt_var]);
            d.lam_fv(lt_fv, lt_ty, body)
        };

        // Case Le b v: decompose v = b*qv+rv, case-split qv.
        let minor_ge = {
            let ge_fv = d.fresh_fvar();
            let ge_var = d.kernel().fvar(ge_fv);

            let decomposed = div_mod_reconstructed(d, &p, b_var, pos_b, v_var);
            let qv = d.div(v_var, b_var);
            let rv = d.modulo(v_var, b_var);
            let mul_b_qv = d.mul(b_var, qv);
            let mul_b_qv_rv = d.add(mul_b_qv, rv);
            let eq_ty = d.eq(v_var, mul_b_qv_rv);
            let bound_ty = d.lt(rv, b_var);
            let eq = and_left(d, eq_ty, bound_ty, decomposed);
            let bound = and_right(d, eq_ty, bound_ty, decomposed);

            // Case-split qv via an arrow-shaped motive (the goal, `concl_v`,
            // does not mention `qv`, so `eq` is applied to the result AFTER
            // the split, exactly as `div_mod_lemmas.rs`'s `q`-case-split
            // does for the ninth add/div/mod mirror).
            let qv_motive = |d: &mut NatDev<'_>, qq: ExprId| -> ExprId {
                let mul_bqq = d.mul(b_var, qq);
                let mul_bqq_rv = d.add(mul_bqq, rv);
                let hyp_ty = d.eq(v_var, mul_bqq_rv);
                d.arrow(hyp_ty, concl_v)
            };
            let at_zero_qv = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let e_fv = d.fresh_fvar();
                let e = d.kernel().fvar(e_fv);
                // e : Eq v (add (mul b zero) rv), defeq Eq v (add zero rv).
                let zero_rv = d.add(zero, rv);
                let zero_add_rv = d.lemma(p.zero_add, &[rv]); // Eq (add zero rv) rv
                let (_, v_eq_rv) = d.chain(v_var, &[(zero_rv, e), (rv, zero_add_rv)]);
                // bound : Lt rv b. Transport from `rv` to `v` (NOT the other
                // way -- `bound`'s actual type is `motive(rv)`, so `rv` is
                // the transport SOURCE and `v` the target, via `Eq rv v`).
                let v_lt_b_motive = d.eq_motive(rv, &|d, x| d.lt(x, b_var));
                let symm_v_eq_rv = d.symm(v_var, rv, v_eq_rv); // Eq rv v
                let v_lt_b = d.transport(rv, v_lt_b_motive, bound, v_var, symm_v_eq_rv);
                // Contradiction: Le b v (ge_var) and Lt v b (v_lt_b).
                let b_lt_b = d.lemma(p.lt_of_le_of_lt, &[b_var, v_var, b_var, ge_var, v_lt_b]);
                let irrefl = d.lemma(p.lt_irrefl, &[b_var]);
                let false_val = d.apply(irrefl, &[b_lt_b]);
                let body = absurd(d, concl_v, false_val);
                let hyp_ty = d.eq(v_var, zero_rv);
                d.lam_fv(e_fv, hyp_ty, body)
            };
            let at_succ_qv = |d: &mut NatDev<'_>, qvpred: ExprId| -> ExprId {
                let qv = d.succ(qvpred);
                let e_fv = d.fresh_fvar();
                let e = d.kernel().fvar(e_fv);
                // e : Eq v (add (mul b qv) rv)

                let pos_qv = d.lemma(p.zero_lt_succ, &[qvpred]); // Lt zero qv

                // qv < mul qv 2 (mul qv 2 is defeq add (add zero qv) qv).
                let zero_add_qv = d.lemma(p.zero_add, &[qv]); // Eq (add zero qv) qv
                let qv_qv = d.add(qv, qv);
                let zero_qv = d.add(zero, qv);
                let bridge = d.congr(zero_qv, qv, zero_add_qv, &|d, v| d.add(v, qv));
                // bridge : Eq (mul qv 2) qv_qv (via the defeq LHS above)
                let le_qv_qvqvpred = d.lemma(p.le_add_right, &[qv, qvpred]); // Le qv (add qv qvpred)
                let succ_qvqvpred = d.add(qv, qvpred);
                let le_succ_step = d.lemma(p.le_succ_succ, &[qv, succ_qvqvpred, le_qv_qvqvpred]);
                // le_succ_step : Le (succ qv) (succ (add qv qvpred)),
                // defeq Lt qv qv_qv (succ (add qv qvpred) ≡ add qv (succ qvpred) = add qv qv).
                let mul_qv_2 = d.mul(qv, two);
                let symm_bridge = d.symm(mul_qv_2, qv_qv, bridge);
                let lt_qv_mulqv2_motive = d.eq_motive(qv_qv, &|d, x| d.lt(qv, x));
                let lt_qv_mulqv2 = d.transport(
                    qv_qv,
                    lt_qv_mulqv2_motive,
                    le_succ_step,
                    mul_qv_2,
                    symm_bridge,
                );

                // mul qv 2 <= mul qv b (hb : Lt one b, defeq Le two b).
                let a_bound = d.lemma(p.mul_le_mul_left, &[qv, two, b_var, hb_var]);
                let mul_qv_b = d.mul(qv, b_var);
                let lt_qv_mulqvb = d.lemma(
                    p.lt_of_lt_of_le,
                    &[qv, mul_qv_2, mul_qv_b, lt_qv_mulqv2, a_bound],
                );

                // mul qv b = mul b qv (mul_comm), so qv < mul b qv.
                let comm_qvb = d.lemma(p.mul_comm, &[qv, b_var]);
                let mul_bq = d.mul(b_var, qv);
                let lt_qv_mulbq_motive = d.eq_motive(mul_qv_b, &|d, x| d.lt(qv, x));
                let lt_qv_mulbq =
                    d.transport(mul_qv_b, lt_qv_mulbq_motive, lt_qv_mulqvb, mul_bq, comm_qvb);

                // mul b qv <= v (from e : v = mul b qv + rv).
                let le_mulbq_sum = d.lemma(p.le_add_right, &[mul_bq, rv]); // Le (mul b qv) (add (mul b qv) rv)
                let sum_bq_rv = d.add(mul_bq, rv);
                let symm_e = d.symm(v_var, sum_bq_rv, e);
                let le_mulbq_v_motive = d.eq_motive(sum_bq_rv, &|d, x| d.le(mul_bq, x));
                let le_mulbq_v =
                    d.transport(sum_bq_rv, le_mulbq_v_motive, le_mulbq_sum, v_var, symm_e);

                let qv_lt_v = d.lemma(
                    p.lt_of_lt_of_le,
                    &[qv, mul_bq, v_var, lt_qv_mulbq, le_mulbq_v],
                );

                let ih_at_qv = d.apply(ih_var, &[qv, qv_lt_v]); // P qv
                let digit_applied = d.apply(digit_var, &[qv, rv, bound, pos_qv, ih_at_qv]);
                // digit_applied : P (add (mul b qv) rv)
                let result_motive = d.eq_motive(sum_bq_rv, &|d, x| d.apply(p_var, &[x]));
                let result = d.transport(sum_bq_rv, result_motive, digit_applied, v_var, symm_e);

                let hyp_ty = d.eq(v_var, sum_bq_rv);
                d.lam_fv(e_fv, hyp_ty, result)
            };
            let qv_case_proof = cases_zero_succ(d, qv, &qv_motive, &at_zero_qv, &at_succ_qv);
            let body = d.apply(qv_case_proof, &[eq]);
            d.lam_fv(ge_fv, ge_ty, body)
        };

        let or_ty = d.const_app(p.logic.or, &[lt_ty, ge_ty]);
        let goal_motive = d.kernel().lam(anon, or_ty, concl_v, BinderInfo::Default);
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let body = d.apply(
            or_rec,
            &[lt_ty, ge_ty, goal_motive, minor_lt, minor_ge, dichotomy],
        );
        let with_ih = d.lam_fv(ih_fv, recursive_v, body);
        d.lam_fv(v_fv, nat, with_ih)
    };

    let one_level = d.level_one();
    let zero_level = d.kernel().level_zero();
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one_level, zero_level]);
    let proof_of_p_n = d.apply(fix, &[nat, relation, p_var, well_founded, step, n_var]);

    let value = {
        let with_digit = d.lam_fv(digit_fv, digit_ty, proof_of_p_n);
        let with_single = d.lam_fv(single_fv, single_ty, with_digit);
        let with_hb = d.lam_fv(hb_fv, hb_ty, with_single);
        let with_b = d.lam_fv(b_fv, nat, with_hb);
        let with_n = d.lam_fv(n_fv, nat, with_b);
        d.lam_fv(p_fv, p_domain, with_n)
    };

    d.declare_theorem(p.base_induction, ty, value)
}
