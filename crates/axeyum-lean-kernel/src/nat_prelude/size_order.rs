//! Order theory for `Nat.size` closing two `ml430` mirrors:
//! `size_bit` (`F:ml430-nat-size-bit-c601dbf0`) and `size_le_size`
//! (`F:ml430-nat-size-le-size-c4b98f53`). A NEW module rather than an
//! addition to `binary.rs` (owns `sizeAux`/`size`'s own definition) or
//! `size_extra.rs` (already a dense, self-contained pair).
//!
//! `binary.rs`'s own `declare_size_aux_lt_pow` doc comment says explicitly:
//! "`size`'s own development ... has no existing lemma relating `size n` to
//! `size (n/2)`". So both mirrors here need genuinely new fuel machinery,
//! not a lookup.
//!
//! # `sizeAux` is single-value fuel recursion, not two-value
//!
//! `landAux`/`lorAux`/`ldiffAux`/`bitwiseAux` (`rec_agreement.rs`) each carry
//! TWO value slots (`m`, `n`) riding through the fuel recursion, and their
//! shared machinery (`agree_by_double_fuel_induction`, `guarded`) is sized
//! for that. `sizeAux fuel n` has only ONE value slot — the guard is `beq n
//! 0`, not a pair of guards — so this file reuses `ops.rs`'s
//! `agree_by_fuel_induction` directly, at `a := n` (the value) and
//! `b := fuel2` (a second, independently-chosen fuel) for
//! [`declare_size_aux_agree_of_fuel`], and at `a`, `b` as two VALUES sharing
//! one fuel for [`declare_size_aux_mono_value`]. No new combinator needed —
//! `agree_by_fuel_induction`'s two generalized slots cover both shapes.
//!
//! # `size_bit`
//!
//! Given `hne : Ne (bit b n) 0`, write `m := bit b n`. `zero_lt_of_ne_zero`
//! plus `succ_pred_of_pos` give `m = succ pf` (`pf := pred m`). Rewriting the
//! FUEL slot of `size m := sizeAux m m` along that equation (`d.congr`, since
//! `m` is only PROPOSITIONALLY `succ pf` — `bit b n` does not reduce to a
//! `succ`-headed normal form for symbolic `b`/`n`) exposes `sizeAux (succ pf)
//! m`, which unfolds by pure `ι`/`β` (the fuel slot alone needs to be
//! literal-`succ`-shaped; the value slot `m` rides through unevaluated) to
//! `bool_select_nat (beq m 0) 0 (succ (sizeAux pf (m/2)))`. `beq_eq_false_of_ne`
//! rewrites the stuck guard to `false`, collapsing the selector to
//! `succ (sizeAux pf (m/2))`.
//!
//! What remains is `sizeAux pf (m/2) = size n`. `bit_div_two` gives
//! `m/2 = n` directly (`m` IS `bit b n`, not merely equal to it), so this
//! reduces to `sizeAux pf n = size n`, i.e. fuel-irrelevance
//! ([`NatPrelude::size_aux_eq_size_of_le`]) — which needs `Le n pf`.
//!
//! **The key simplification that avoids any case split on `b` or `n`**:
//! `half_le_predecessor_of_succ` (`rec_agreement.rs`) at its OWN
//! `predecessor := pf`, `k := pf`, fed the trivial `le_refl (succ pf)`,
//! gives `Le (div (succ pf) 2) pf` — a fact about `pf` ALONE, with no
//! `bit`/`n`/`b` involved. Transporting along `bit_div_two` (`div m 2 = n`)
//! and `m = succ pf` turns this directly into `Le n pf`. No case split, no
//! positivity argument about `n` or `b` needed at all.
//!
//! # `size_le_size`
//!
//! `size m := sizeAux m m`, `size n := sizeAux n n`. Given `h : Le m n`,
//! [`declare_size_aux_mono_value`] at shared fuel `n` (via `h` and
//! `le_refl n`) gives `Le (sizeAux n m) (sizeAux n n)`, i.e.
//! `Le (sizeAux n m) (size n)`. `size_aux_eq_size_of_le` at `(fuel := n,
//! value := m)` (sufficient since `m ≤ n`) gives `Eq (sizeAux n m) (size
//! m)`, and transporting the mono bound along it closes `Le (size m) (size
//! n)`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, agree_by_fuel_induction, cases_zero_succ};
use super::rec_agreement::half_le_predecessor_of_succ;
use crate::KernelError;
use crate::expr::ExprId;

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)` — the `Bool`-scrutinee, `Nat`-
/// conclusion twin of [`NatOps::congr`] (whose `eq_motive`/`transport` are
/// hardcoded to `Nat` throughout, so `congr` itself cannot express a
/// hypothesis about a `Bool` equality — needed here because
/// `beq_eq_false_of_ne`'s conclusion is `Eq Bool (beq m 0) false`, not an
/// `Eq Nat`). A private copy of `bitwise.rs`/`xor_algebra.rs`/
/// `gauss_lemma.rs`'s own `congr_bool_to_nat` (each file keeps its own,
/// per those modules' own doc comments — it is a small, self-contained
/// leaf over already-generic `ops.rs` primitives, not worth a shared
/// export).
fn congr_bool_to_nat(
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

/// `Nat.size_aux_zero_any_fuel : ∀ fuel, Eq (sizeAux fuel 0) 0` — holds at
/// ANY fuel, sufficient or not (mirrors `Nat.land_aux_zero_left_any_fuel`).
/// `cases_zero_succ` on `fuel` alone, no induction hypothesis: at `fuel = 0`
/// the base row is the constant `0` (`refl`); at `fuel = succ f` the guard
/// `beq 0 0` is fully closed (both literal `zero`, no free vars), so it
/// reduces to `true` and the selector collapses to `0` by pure `ι`, for any
/// (possibly symbolic) `f` — `refl` again.
fn declare_size_aux_zero_any_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.size_aux_zero_any_fuel, 1, &|d, v| {
        let fuel = v[0];
        let zero = d.zero();
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let lhs = d.const_app(p.size_aux, &[candidate, zero]);
            d.eq(lhs, zero)
        };
        let proof = cases_zero_succ(
            d,
            fuel,
            &statement_at,
            &|d| {
                let zero = d.zero();
                let lhs = d.const_app(p.size_aux, &[zero, zero]);
                d.refl(lhs)
            },
            &|d, predecessor| {
                let sp = d.succ(predecessor);
                let lhs = d.const_app(p.size_aux, &[sp, zero]);
                d.refl(lhs)
            },
        );
        let stmt = statement_at(d, fuel);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.size_aux_agree_of_fuel : ∀ fuel1 n fuel2, Le n fuel1 → Le n fuel2 →
/// Eq (sizeAux fuel1 n) (sizeAux fuel2 n)`. [`agree_by_fuel_induction`]
/// directly, at `a := n`, `b := fuel2` — see the module doc for why no new
/// combinator is needed. Modeled on `rec_agreement.rs`'s
/// `declare_land_aux_agree_of_fuel`, simplified: `sizeAux` has one guard
/// (on the value `n`), not two (on `m` then `n`), so the step case-splits
/// only once.
fn declare_size_aux_agree_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel1: ExprId, n: ExprId, fuel2: ExprId| {
        let bound1 = d.le(n, fuel1);
        let bound2 = d.le(n, fuel2);
        let lhs = d.const_app(p.size_aux, &[fuel1, n]);
        let rhs = d.const_app(p.size_aux, &[fuel2, n]);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound2, concl);
        d.arrow(bound1, inner)
    };

    let base = |d: &mut NatDev<'_>, n: ExprId, fuel2: ExprId| -> ExprId {
        let zero = d.zero();
        let bound1_ty = d.le(n, zero);
        let bound2_ty = d.le(n, fuel2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();

        let zero_le_n = d.lemma(p.zero_le, &[n]);
        let n_eq_zero = d.lemma(p.le_antisymm, &[n, zero, h1, zero_le_n]);

        let left_term = d.const_app(p.size_aux, &[zero, n]);
        let right_term = d.const_app(p.size_aux, &[fuel2, n]);
        let left_is_zero = d.refl(zero);

        let right_at_zero = d.const_app(p.size_aux, &[fuel2, zero]);
        let right_congr = d.congr(n, zero, n_eq_zero, &|d, x| {
            d.const_app(p.size_aux, &[fuel2, x])
        });
        let any_fuel = d.lemma(p.size_aux_zero_any_fuel, &[fuel2]);
        let (_, right_is_zero) =
            d.chain(right_term, &[(right_at_zero, right_congr), (zero, any_fuel)]);
        let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);

        let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);
        let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
        d.lam_fv(h1_fv, bound1_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, n: ExprId, fuel2: ExprId| -> ExprId {
        let sk = d.succ(k);
        let goal_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound1 = d.le(candidate, sk);
            let bound2 = d.le(candidate, fuel2);
            let lhs = d.const_app(p.size_aux, &[sk, candidate]);
            let rhs = d.const_app(p.size_aux, &[fuel2, candidate]);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

        cases_zero_succ(
            d,
            n,
            &goal_at,
            &|d| {
                let zero = d.zero();
                let bound1_ty = d.le(zero, sk);
                let bound2_ty = d.le(zero, fuel2);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let left_term = d.const_app(p.size_aux, &[sk, zero]);
                let right_term = d.const_app(p.size_aux, &[fuel2, zero]);
                let left_is_zero = d.lemma(p.size_aux_zero_any_fuel, &[sk]);
                let right_is_zero = d.lemma(p.size_aux_zero_any_fuel, &[fuel2]);
                let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);
                let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
            &|d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let bound1_ty = d.le(succ_pred, sk);
                let bound2_ty = d.le(succ_pred, fuel2);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let two = d.num(2);
                let half = d.div(succ_pred, two);

                let half_le_k = half_le_predecessor_of_succ(d, &p, predecessor, k, h1);

                let one = d.num(1);
                let one_le_succ_pred = d.zero_lt_succ(predecessor);
                let one_le_fuel2 =
                    d.lemma(p.le_trans, &[one, succ_pred, fuel2, one_le_succ_pred, h2]);
                let succ_pred_fuel2 = d.lemma(p.succ_pred_of_pos, &[fuel2, one_le_fuel2]);
                let f2p = d.pred(fuel2);
                let succ_f2p = d.succ(f2p);
                let h2_motive = d.eq_motive(fuel2, &|d, x| d.le(succ_pred, x));
                let h2_at_succ_f2p = d.transport(fuel2, h2_motive, h2, succ_f2p, succ_pred_fuel2);
                let half_le_f2p = half_le_predecessor_of_succ(d, &p, predecessor, f2p, h2_at_succ_f2p);

                let ih_at_half = d.apply(ih, &[half, f2p]);
                let ih_at_half = d.apply(ih_at_half, &[half_le_k, half_le_f2p]);
                // ih_at_half : Eq (sizeAux k half) (sizeAux f2p half)

                let recursive_general = d.const_app(p.size_aux, &[k, half]);
                let recursive_at_f2p = d.const_app(p.size_aux, &[f2p, half]);
                let succ_general = d.succ(recursive_general);
                let succ_at_f2p = d.succ(recursive_at_f2p);
                let succ_congr = d.congr(recursive_general, recursive_at_f2p, ih_at_half, &|d, x| {
                    d.succ(x)
                });
                // succ_congr : Eq (succ recursive_general) (succ recursive_at_f2p)
                // -- defeq Eq (sizeAux sk succ_pred) (succ recursive_at_f2p),
                // since `sk`/`succ_pred` are both literal-succ-shaped.
                let _ = succ_general;

                let outer_step = d.congr(fuel2, succ_f2p, succ_pred_fuel2, &|d, x| {
                    d.const_app(p.size_aux, &[x, succ_pred])
                });
                let final_target = d.const_app(p.size_aux, &[fuel2, succ_pred]);
                let mid2 = d.const_app(p.size_aux, &[succ_f2p, succ_pred]);
                let outer_step_rev = d.symm(final_target, mid2, outer_step);
                // outer_step_rev : Eq mid2 final_target -- defeq
                // Eq (succ recursive_at_f2p) final_target.

                let start = d.const_app(p.size_aux, &[sk, succ_pred]);
                let body = d.trans(start, succ_at_f2p, final_target, succ_congr, outer_step_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
        )
    };

    let fuel1_fv = d.fresh_fvar();
    let fuel1 = d.kernel().fvar(fuel1_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel1);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fuel2_fv = d.fresh_fvar();
    let fuel2 = d.kernel().fvar(fuel2_fv);
    let applied = d.apply(proof_fn, &[n, fuel2]);
    let ty = {
        let body = statement(d, fuel1, n, fuel2);
        let with_fuel2 = d.pi_fv(fuel2_fv, nat, body);
        let with_n = d.pi_fv(n_fv, nat, with_fuel2);
        d.pi_fv(fuel1_fv, nat, with_n)
    };
    let value = {
        let with_fuel2 = d.lam_fv(fuel2_fv, nat, applied);
        let with_n = d.lam_fv(n_fv, nat, with_fuel2);
        d.lam_fv(fuel1_fv, nat, with_n)
    };
    d.declare_theorem(p.size_aux_agree_of_fuel, ty, value)
}

/// `Nat.size_aux_eq_size_of_le : ∀ fuel n, Le n fuel → Eq (sizeAux fuel n)
/// (size n)` — the `fuel2 := n` instance of
/// [`declare_size_aux_agree_of_fuel`] via `le_refl`, mirroring
/// `Nat.land_aux_eq_land_of_le`: `size n` and `sizeAux n n` are the SAME
/// term by definition, so the kernel accepts the double-fuel proof directly
/// against this `size`-headed statement via defeq.
fn declare_size_aux_eq_size_of_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.size_aux_eq_size_of_le, 2, &|d, values| {
        let fuel = values[0];
        let n = values[1];
        let bound_ty = d.le(n, fuel);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let agree = d.lemma(p.size_aux_agree_of_fuel, &[fuel, n, n]);
        let agree = d.apply(agree, &[bound, le_refl_n]);
        let lhs = d.const_app(p.size_aux, &[fuel, n]);
        let rhs = d.const_app(p.size, &[n]);
        let stmt = d.eq(lhs, rhs);
        let inner_ty = d.arrow(bound_ty, stmt);
        let value = d.lam_fv(bound_fv, bound_ty, agree);
        (inner_ty, value)
    })?;
    Ok(())
}

/// `Nat.size_aux_mono_value : ∀ fuel a b, Le a b → Le b fuel → Le (sizeAux
/// fuel a) (sizeAux fuel b)` — `sizeAux` is monotone in its VALUE argument
/// at any shared, sufficient fuel. [`agree_by_fuel_induction`] at `a`, `b`
/// as the two generalized VALUES (both sharing the single fuel `fuel`), a
/// different instantiation of the same combinator
/// [`declare_size_aux_agree_of_fuel`] uses for a different pair of roles.
/// The step splits on `b` first, then (only when `b = succ pb`) on `a` —
/// mirroring `bool_select_nat`'s guard, which fires on the VALUE, not the
/// fuel.
fn declare_size_aux_mono_value(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId| {
        let hyp1 = d.le(a, b);
        let hyp2 = d.le(b, fuel);
        let lhs = d.const_app(p.size_aux, &[fuel, a]);
        let rhs = d.const_app(p.size_aux, &[fuel, b]);
        let concl = d.le(lhs, rhs);
        let inner = d.arrow(hyp2, concl);
        d.arrow(hyp1, inner)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId| -> ExprId {
        let zero = d.zero();
        let hyp1_ty = d.le(a, b);
        let hyp2_ty = d.le(b, zero);
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let le_refl0 = d.lemma(p.le_refl, &[zero]);
        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, le_refl0);
        d.lam_fv(h1_fv, hyp1_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId| -> ExprId {
        let sk = d.succ(k);
        let goal_at = |d: &mut NatDev<'_>, av: ExprId, bv: ExprId| -> ExprId {
            let hyp1 = d.le(av, bv);
            let hyp2 = d.le(bv, sk);
            let lhs = d.const_app(p.size_aux, &[sk, av]);
            let rhs = d.const_app(p.size_aux, &[sk, bv]);
            let concl = d.le(lhs, rhs);
            let inner = d.arrow(hyp2, concl);
            d.arrow(hyp1, inner)
        };

        cases_zero_succ(
            d,
            b,
            &|d, bv| goal_at(d, a, bv),
            &|d| {
                // b = 0: Le a 0 forces a = 0 (le_antisymm), so both sides
                // are the SAME term after rewriting -- le_refl suffices.
                let zero = d.zero();
                let hyp1_ty = d.le(a, zero);
                let hyp2_ty = d.le(zero, sk);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();

                let zero_le_a = d.lemma(p.zero_le, &[a]);
                let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, h1, zero_le_a]);

                let lhs_at_zero = d.const_app(p.size_aux, &[sk, zero]);
                let motive = d.eq_motive(zero, &|d, x| {
                    let lhs_x = d.const_app(p.size_aux, &[sk, x]);
                    d.le(lhs_x, lhs_at_zero)
                });
                let refl_case = d.lemma(p.le_refl, &[lhs_at_zero]);
                let rev_eq = d.symm(a, zero, a_eq_zero);
                let result = d.transport(zero, motive, refl_case, a, rev_eq);

                let with_h2 = d.lam_fv(h2_fv, hyp2_ty, result);
                d.lam_fv(h1_fv, hyp1_ty, with_h2)
            },
            &|d, pb| {
                let succ_pb = d.succ(pb);
                cases_zero_succ(
                    d,
                    a,
                    &|d, av| goal_at(d, av, succ_pb),
                    &|d| {
                        // a = 0: LHS is defeq 0, so `zero_le` at the RHS
                        // (unexpanded) closes it -- no reduction of the
                        // RHS is even needed.
                        let zero = d.zero();
                        let hyp1_ty = d.le(zero, succ_pb);
                        let hyp2_ty = d.le(succ_pb, sk);
                        let h1_fv = d.fresh_fvar();
                        let h2_fv = d.fresh_fvar();
                        let rhs = d.const_app(p.size_aux, &[sk, succ_pb]);
                        let zero_le_rhs = d.lemma(p.zero_le, &[rhs]);
                        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, zero_le_rhs);
                        d.lam_fv(h1_fv, hyp1_ty, with_h2)
                    },
                    &|d, pa| {
                        let succ_pa = d.succ(pa);
                        let hyp1_ty = d.le(succ_pa, succ_pb);
                        let hyp2_ty = d.le(succ_pb, sk);
                        let h1_fv = d.fresh_fvar();
                        let h1 = d.kernel().fvar(h1_fv);
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);

                        let two = d.num(2);
                        let half_a = d.div(succ_pa, two);
                        let half_b = d.div(succ_pb, two);

                        let half_b_le_k = half_le_predecessor_of_succ(d, &p, pb, k, h2);
                        let half_a_le_half_b =
                            d.lemma(p.div_le_div_right, &[succ_pa, succ_pb, two, h1]);

                        let ih_at = d.apply(ih, &[half_a, half_b]);
                        let ih_at = d.apply(ih_at, &[half_a_le_half_b, half_b_le_k]);
                        // ih_at : Le (sizeAux k half_a) (sizeAux k half_b)

                        let lhs_k = d.const_app(p.size_aux, &[k, half_a]);
                        let rhs_k = d.const_app(p.size_aux, &[k, half_b]);
                        let succ_le = d.lemma(p.succ_le_succ, &[lhs_k, rhs_k, ih_at]);
                        // succ_le : Le (succ lhs_k) (succ rhs_k) -- defeq
                        // Le (sizeAux sk succ_pa) (sizeAux sk succ_pb).

                        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, succ_le);
                        d.lam_fv(h1_fv, hyp1_ty, with_h2)
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let applied = d.apply(proof_fn, &[a, b]);
    let ty = {
        let body = statement(d, fuel, a, b);
        let with_b = d.pi_fv(b_fv, nat, body);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_b = d.lam_fv(b_fv, nat, applied);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.size_aux_mono_value, ty, value)
}

/// `Nat.size_le_size : ∀ m n, Le m n → Le (size m) (size n)` —
/// `F:ml430-nat-size-le-size-c4b98f53`. See the module doc for the
/// derivation.
fn declare_size_le_size(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.size_le_size, 2, &|d, values| {
        let m = values[0];
        let n = values[1];
        let hyp_ty = d.le(m, n);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let mono = d.lemma(p.size_aux_mono_value, &[n, m, n]);
        let mono = d.apply(mono, &[hyp, le_refl_n]);
        // mono : Le (sizeAux n m) (sizeAux n n), defeq Le (sizeAux n m) (size n)

        let eq_size_m = d.lemma(p.size_aux_eq_size_of_le, &[n, m, hyp]);
        // eq_size_m : Eq (sizeAux n m) (size m)

        let sizeaux_n_m = d.const_app(p.size_aux, &[n, m]);
        let size_n = d.const_app(p.size, &[n]);
        let motive = d.eq_motive(sizeaux_n_m, &|d, x| d.le(x, size_n));
        let size_m = d.const_app(p.size, &[m]);
        let result = d.transport(sizeaux_n_m, motive, mono, size_m, eq_size_m);

        let concl = d.le(size_m, size_n);
        let stmt = d.arrow(hyp_ty, concl);
        let value = d.lam_fv(hyp_fv, hyp_ty, result);
        (stmt, value)
    })?;
    Ok(())
}

/// `Nat.size_bit : ∀ {b n}, Ne (bit b n) 0 → Eq (size (bit b n)) (succ (size
/// n))` — `F:ml430-nat-size-bit-c601dbf0`. See the module doc for the
/// derivation.
fn declare_size_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero = d.zero();
    let m = d.const_app(p.bit, &[b, n]);
    let ne_ty = {
        let e = d.eq(m, zero);
        d.arrow(e, false_ty)
    };
    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);

    // m = succ pf.
    let pos = d.lemma(p.zero_lt_of_ne_zero, &[m, hne]);
    let eq_succ_pred = d.lemma(p.succ_pred_of_pos, &[m, pos]);
    let pf = d.pred(m);
    let succ_pf = d.succ(pf);

    // div m 2 = n -- `m` IS `bit b n`, not merely equal to it.
    let div_eq_n = d.lemma(p.bit_div_two, &[b, n]);

    // Le n pf: half_le_predecessor_of_succ at its own predecessor/k := pf,
    // fed le_refl (succ pf), gives Le (div (succ pf) 2) pf -- a fact about
    // `pf` alone. Transport along `bit_div_two` and `m = succ pf`.
    let le_refl_succ_pf = d.lemma(p.le_refl, &[succ_pf]);
    let le_half_succ_pf_pf = half_le_predecessor_of_succ(d, &p, pf, pf, le_refl_succ_pf);
    // le_half_succ_pf_pf : Le (div succ_pf 2) pf
    let motive_m = d.eq_motive(succ_pf, &|d, x| {
        let dx = d.div(x, d.num(2));
        d.le(dx, pf)
    });
    let rev_m_eq = d.symm(m, succ_pf, eq_succ_pred); // Eq succ_pf m
    let le_div_m_2_pf = d.transport(succ_pf, motive_m, le_half_succ_pf_pf, m, rev_m_eq);
    // le_div_m_2_pf : Le (div m 2) pf
    let div_m_2 = d.div(m, d.num(2));
    let motive_n = d.eq_motive(div_m_2, &|d, x| d.le(x, pf));
    let le_n_pf = d.transport(div_m_2, motive_n, le_div_m_2_pf, n, div_eq_n);
    // le_n_pf : Le n pf

    // sizeAux(m,m) = sizeAux(succ pf, m) (congr on the fuel slot only).
    let sizeaux_m_m = d.const_app(p.size_aux, &[m, m]);
    let congr1 = d.congr(m, succ_pf, eq_succ_pred, &|d, x| {
        d.const_app(p.size_aux, &[x, m])
    });
    let sizeaux_succ_pf_m = d.const_app(p.size_aux, &[succ_pf, m]);

    // Unfold sizeAux(succ pf, m) by iota/beta to the un-simplified selector.
    let half_m = d.div(m, d.num(2));
    let recursed = d.const_app(p.size_aux, &[pf, half_m]);
    let succ_recursed = d.succ(recursed);
    let beq_m0 = d.beq(m, zero);
    let unfold_mid = d.bool_select_nat(beq_m0, zero, succ_recursed);
    let refl_unfold = d.refl(unfold_mid);

    // Rewrite the stuck guard `beq m 0` to `false`.
    let beq_false = d.lemma(p.beq_eq_false_of_ne, &[m, zero, hne]);
    let false_lit = d.bool_false();
    let congr_beq = congr_bool_to_nat(d, beq_m0, false_lit, beq_false, &|d, x| {
        d.bool_select_nat(x, zero, succ_recursed)
    });
    let reduced = d.bool_select_nat(false_lit, zero, succ_recursed);
    let refl_final = d.refl(succ_recursed);

    // sizeAux(pf, half_m) = sizeAux(pf, n) = size n.
    let congr_half = d.congr(half_m, n, div_eq_n, &|d, x| {
        let sa = d.const_app(p.size_aux, &[pf, x]);
        d.succ(sa)
    });
    let sizeaux_pf_n = d.const_app(p.size_aux, &[pf, n]);
    let succ_sizeaux_pf_n = d.succ(sizeaux_pf_n);
    let fuel_irrelevance = d.lemma(p.size_aux_eq_size_of_le, &[pf, n, le_n_pf]);
    let size_n = d.const_app(p.size, &[n]);
    let succ_size_n = d.succ(size_n);
    let succ_fuel_irrelevance = d.congr(sizeaux_pf_n, size_n, fuel_irrelevance, &|d, x| d.succ(x));
    let _ = succ_sizeaux_pf_n;

    let (_, combined) = d.chain(
        sizeaux_m_m,
        &[
            (sizeaux_succ_pf_m, congr1),
            (unfold_mid, refl_unfold),
            (reduced, congr_beq),
            (succ_recursed, refl_final),
            (d.succ(d.const_app(p.size_aux, &[pf, n])), congr_half),
            (succ_size_n, succ_fuel_irrelevance),
        ],
    );

    let size_m = d.const_app(p.size, &[m]);
    let stmt = d.eq(size_m, succ_size_n);

    let ty = {
        let over_hyp = d.arrow(ne_ty, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_hyp);
        d.pi_fv(b_fv, bool_ty, over_n)
    };
    let value = {
        let over_hyp = d.lam_fv(hne_fv, ne_ty, combined);
        let over_n = d.lam_fv(n_fv, nat, over_hyp);
        d.lam_fv(b_fv, bool_ty, over_n)
    };
    d.declare_theorem(p.size_bit, ty, value)
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_size_order_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_size_aux_zero_any_fuel(d, p)?;
    declare_size_aux_agree_of_fuel(d, p)?;
    declare_size_aux_eq_size_of_le(d, p)?;
    declare_size_aux_mono_value(d, p)?;
    declare_size_le_size(d, p)?;
    declare_size_bit(d, p)?;
    Ok(())
}
