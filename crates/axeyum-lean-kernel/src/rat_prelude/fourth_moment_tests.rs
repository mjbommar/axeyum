//! ADR-1653, measured.
//!
//! Two things are worth saying about the shape of these tests.
//!
//! First, `Rat.FourwiseUncorrelated` is a `Definition`, and the trusted gate
//! **cannot** tell you a definition is wrong — it type-checks either way. So
//! the positive control here is not "it was admitted": it is that an
//! `h : FourwiseUncorrelated Y m p n` can be APPLIED, through `And.left`, to
//! four indices and six side conditions, and that the type the kernel then
//! infers is the mixed-moment equation and not something else. That is the
//! only evidence the unfolding is the one the module docs claim.
//!
//! Second, every statement test carries an **off-by-one control at the
//! statement level**: the same instance must NOT prove the `succ m` form. A
//! wrong index range in `Rat.sumVars`' peeling lemma would land exactly
//! there, and nothing else in this file would notice.

use super::*;
use crate::Kernel;
use crate::build_rat_prelude;

fn prelude() -> (Kernel, RatPrelude) {
    let mut k = Kernel::new();
    let p = build_rat_prelude(&mut k).expect("rat prelude must build");
    (k, p)
}

/// Every ADR-1653 declaration is axiom-free — asserted only AFTER
/// `Environment::contains`, since a name that is simply missing has an empty
/// footprint too.
#[test]
fn fourth_moment_declarations_are_axiom_free() {
    let (k, p) = prelude();
    let g = p.fourth_moment;
    let names = [
        g.expectation_sum_vars_mul,
        g.expectation_sum_vars_mul_eq_zero,
        g.fourwise_uncorrelated,
        g.expectation_sq_sum_vars_mul_sq,
        g.fourth_moment_sum_vars_le,
        g.fourth_moment_tail_sum_vars,
    ];
    for name in names {
        assert!(
            k.environment().contains(name),
            "the name must be DECLARED before its footprint means anything: {}",
            k.display_name(name)
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "every ADR-1653 declaration must be axiom-free: {}",
            k.display_name(name)
        );
    }
}

/// **The positive control on the `Definition`.** A hypothesis
/// `h : Rat.FourwiseUncorrelated Y m p n` is applied — through `And.left`, at
/// four indices and the six side conditions — and the type the kernel infers
/// must be `E[((Y a · Y b) · Y c) · Y l] = 0`.
///
/// The negative control is the same statement with the LONE index moved out
/// of the last slot. The definition's first condition is not symmetric in its
/// four slots as written (it is `l` that must differ from the other three),
/// and a test blind to that difference would not be testing the definition.
#[test]
fn fourwise_uncorrelated_applies_to_four_indices_and_yields_the_lone_index_moment() {
    let (mut k, p) = prelude();
    let names = p.fourth_moment;
    let mut d = IntDev::new(&mut k, p.int);

    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let (lone, squares) = fourwise_body(&mut d, p, y, m, pf, n);
    let whole = d.const_app(names.fourwise_uncorrelated, &[y, m, pf, n]);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let left = d.and_left(lone, squares, h);

    // Four indices, their four bounds, and the three disequalities against
    // the LAST index — each as its own free variable, so the whole
    // application can be closed and its type read off.
    let mut idx_fv = Vec::new();
    let mut idx = Vec::new();
    for _ in 0..4 {
        let fv = d.fresh_fvar();
        idx_fv.push(fv);
        idx.push(d.kernel().fvar(fv));
    }
    let mut lt_ty = Vec::new();
    let mut lt_fv = Vec::new();
    let mut lt_arg = Vec::new();
    for &index in &idx {
        lt_ty.push(d.lt(index, m));
        let fv = d.fresh_fvar();
        lt_fv.push(fv);
        lt_arg.push(d.kernel().fvar(fv));
    }
    let mut ne_ty = Vec::new();
    let mut ne_fv = Vec::new();
    let mut ne_arg = Vec::new();
    for slot in 0..3 {
        let eq = d.eq(idx[slot], idx[3]);
        ne_ty.push(d.not(eq));
        let fv = d.fresh_fvar();
        ne_fv.push(fv);
        ne_arg.push(d.kernel().fvar(fv));
    }

    let mut args = idx.clone();
    args.extend(lt_arg.iter().copied());
    args.extend(ne_arg.iter().copied());
    let applied = d.apply(left, &args);

    // Close it: the kernel cannot infer a type for a term with dangling free
    // variables, so every binder introduced above is discharged in order.
    let close = |d: &mut IntDev<'_>, body: ExprId, pi: bool| -> ExprId {
        let mut t = body;
        for slot in (0..3).rev() {
            t = if pi {
                d.pi_fv(ne_fv[slot], ne_ty[slot], t)
            } else {
                d.lam_fv(ne_fv[slot], ne_ty[slot], t)
            };
        }
        for slot in (0..4).rev() {
            t = if pi {
                d.pi_fv(lt_fv[slot], lt_ty[slot], t)
            } else {
                d.lam_fv(lt_fv[slot], lt_ty[slot], t)
            };
        }
        for slot in (0..4).rev() {
            t = if pi {
                d.pi_fv(idx_fv[slot], nat, t)
            } else {
                d.lam_fv(idx_fv[slot], nat, t)
            };
        }
        t = if pi {
            d.pi_fv(h_fv, whole, t)
        } else {
            d.lam_fv(h_fv, whole, t)
        };
        // `Y`, `p`, `n` and `m` are free in every term above; a kernel cannot
        // infer a type for a term with a dangling free variable, so they are
        // discharged too.
        for (fv, ty) in [(m_fv, nat), (n_fv, nat), (pf_fv, fn_ty), (y_fv, x_ty)] {
            t = if pi {
                d.pi_fv(fv, ty, t)
            } else {
                d.lam_fv(fv, ty, t)
            };
        }
        t
    };

    let term = close(&mut d, applied, false);
    let got = d
        .kernel()
        .infer(term)
        .expect("applying a FourwiseUncorrelated hypothesis must type-check");

    let zero_r = rzero(&mut d, p);
    let want = {
        let moment = mixed_moment(&mut d, p, y, [idx[0], idx[1], idx[2], idx[3]], pf, n);
        let concl = req(&mut d, moment, zero_r);
        close(&mut d, concl, true)
    };
    assert!(
        d.kernel().def_eq(got, want),
        "the applied hypothesis must prove the lone-index mixed moment vanishes"
    );

    let wrong = {
        let moved = [idx[3], idx[0], idx[1], idx[2]];
        let moment = mixed_moment(&mut d, p, y, moved, pf, n);
        let concl = req(&mut d, moment, zero_r);
        close(&mut d, concl, true)
    };
    assert!(
        !d.kernel().def_eq(got, wrong),
        "the lone index sits in the LAST slot; a control blind to that would \
         not be testing the definition"
    );
}

/// `Rat.expectation_sumVars_mul` proves the peeling identity at the bound it
/// is instantiated at — and NOT at `succ m`.
#[test]
fn expectation_sum_vars_mul_peels_at_the_bound_it_is_given() {
    let (mut k, p) = prelude();
    let names = p.fourth_moment;
    let mut d = IntDev::new(&mut k, p.int);

    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let inst = d.lemma(names.expectation_sum_vars_mul, &[y, w, pf, n, m]);
    let closed = {
        let t = d.lam_fv(m_fv, nat, inst);
        let t = d.lam_fv(n_fv, nat, t);
        let t = d.lam_fv(pf_fv, fn_ty, t);
        let t = d.lam_fv(w_fv, fn_ty, t);
        d.lam_fv(y_fv, x_ty, t)
    };
    let got = d
        .kernel()
        .infer(closed)
        .expect("the peeling lemma must instantiate");

    let build = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let per_index = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = expect_of(
                d,
                p,
                &|d, k| {
                    let yi = var_at(d, y, i, k);
                    let wk = d.apply(w, &[k]);
                    rmul(d, yi, wk)
                },
                pf,
                n,
            );
            d.lam_fv(i_fv, nat, body)
        };
        let lhs = expect_of(
            d,
            p,
            &|d, k| {
                let s = sv_at(d, p, y, m, k);
                let wk = d.apply(w, &[k]);
                rmul(d, s, wk)
            },
            pf,
            n,
        );
        let rhs = rsum_range(d, p, per_index, bound);
        let concl = req(d, lhs, rhs);
        let t = d.pi_fv(m_fv, nat, concl);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(pf_fv, fn_ty, t);
        let t = d.pi_fv(w_fv, fn_ty, t);
        d.pi_fv(y_fv, x_ty, t)
    };

    let want = build(&mut d, m);
    assert!(
        d.kernel().def_eq(got, want),
        "the peeling lemma must state `E[(Σ_{{i<m}} Y_i)·W] = Σ_{{i<m}} E[Y_i·W]`"
    );

    let sm = d.succ(m);
    let wrong = build(&mut d, sm);
    assert!(
        !d.kernel().def_eq(got, wrong),
        "an off-by-one in the peeled index range would land exactly here"
    );
}

/// `Rat.expectation_sumVars_mul_eq_zero` turns bounded pointwise vanishing
/// into a vanishing expectation — and does not prove the same expectation is
/// `one`, which is the control that keeps the previous assertion honest about
/// WHICH constant it reached.
#[test]
fn expectation_sum_vars_mul_eq_zero_concludes_zero_and_not_one() {
    let (mut k, p) = prelude();
    let names = p.fourth_moment;
    let mut d = IntDev::new(&mut k, p.int);

    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero_r = rzero(&mut d, p);
    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ilt = d.lt(i, m);
        let ei = expect_of(
            &mut d,
            p,
            &|d, k| {
                let yi = var_at(d, y, i, k);
                let wk = d.apply(w, &[k]);
                rmul(d, yi, wk)
            },
            pf,
            n,
        );
        let concl = req(&mut d, ei, zero_r);
        let inner = d.arrow(ilt, concl);
        d.pi_fv(i_fv, nat, inner)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inst = d.lemma(names.expectation_sum_vars_mul_eq_zero, &[y, w, pf, n, m, h]);
    let closed = {
        let t = d.lam_fv(h_fv, hyp_ty, inst);
        let t = d.lam_fv(m_fv, nat, t);
        let t = d.lam_fv(n_fv, nat, t);
        let t = d.lam_fv(pf_fv, fn_ty, t);
        let t = d.lam_fv(w_fv, fn_ty, t);
        d.lam_fv(y_fv, x_ty, t)
    };
    let got = d
        .kernel()
        .infer(closed)
        .expect("the vanishing lemma must instantiate");

    let build = |d: &mut IntDev<'_>, target: ExprId| -> ExprId {
        let lhs = expect_of(
            d,
            p,
            &|d, k| {
                let s = sv_at(d, p, y, m, k);
                let wk = d.apply(w, &[k]);
                rmul(d, s, wk)
            },
            pf,
            n,
        );
        let concl = req(d, lhs, target);
        let t = d.pi_fv(h_fv, hyp_ty, concl);
        let t = d.pi_fv(m_fv, nat, t);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(pf_fv, fn_ty, t);
        let t = d.pi_fv(w_fv, fn_ty, t);
        d.pi_fv(y_fv, x_ty, t)
    };

    let want = build(&mut d, zero_r);
    assert!(
        d.kernel().def_eq(got, want),
        "bounded pointwise vanishing must give a vanishing expectation"
    );

    let one_r = super::super::ops::rone(&mut d, p);
    let wrong = build(&mut d, one_r);
    assert!(
        !d.kernel().def_eq(got, wrong),
        "the conclusion is `= zero`; a control that cannot see `= one` is vacuous"
    );
}

/// **The multinomial coefficient is 3, and this test can see that it is not 6.**
///
/// `Rat.fourth_moment_sumVars_le`'s declared type is compared against the
/// statement rebuilt with THREE copies of `T·T` and against the same statement
/// with SIX. The first must match and the second must not. Without the second
/// half, "the bound is `Σ M₄ + 3(Σ σ²)²`" would be a claim about the source
/// rather than about the admitted declaration — and 3 is exactly the constant
/// the multinomial expansion of a fourth power puts there.
#[test]
fn fourth_moment_bound_carries_three_square_terms_and_not_six() {
    let (mut k, p) = prelude();
    let names = p.fourth_moment;
    let mut d = IntDev::new(&mut k, p.int);

    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let c = d.kernel().const_(names.fourth_moment_sum_vars_le, vec![]);
    let got = d
        .kernel()
        .infer(c)
        .expect("Rat.fourth_moment_sumVars_le must be declared");

    let build = |d: &mut IntDev<'_>, copies: usize| -> ExprId {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let pf_fv = d.fresh_fvar();
        let pf = d.kernel().fvar(pf_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m4_fv = d.fresh_fvar();
        let m4 = d.kernel().fvar(m4_fv);
        let s2_fv = d.fresh_fvar();
        let s2 = d.kernel().fvar(s2_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let zero_r = rzero(d, p);
        let hd_ty = is_distribution(d, p, pf, n);
        let hs2_ty = rle(d, p, zero_r, s2);
        let hfw_ty = d.const_app(names.fourwise_uncorrelated, &[y, m, pf, n]);
        let h4_ty = fourth_moment_bounded(d, p, y, m4, pf, n, m);
        let h2_ty = second_moment_bounded(d, p, y, s2, pf, n, m);

        let lhs = expect_of(
            d,
            p,
            &|d, kk| {
                let s = sv_at(d, p, y, m, kk);
                let ss = rmul(d, s, s);
                rmul(d, ss, ss)
            },
            pf,
            n,
        );
        let const_m4 = const_fn(d, m4);
        let const_s2 = const_fn(d, s2);
        let sm = rsum_range(d, p, const_m4, m);
        let tsum = rsum_range(d, p, const_s2, m);
        let sq = rmul(d, tsum, tsum);
        let mut acc = sq;
        for _ in 1..copies {
            acc = radd(d, acc, sq);
        }
        let rhs = radd(d, sm, acc);
        let concl = rle(d, p, lhs, rhs);

        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h4_ty, t);
        let t = d.arrow(hfw_ty, t);
        let t = d.pi_fv(m_fv, nat, t);
        let t = d.arrow(hs2_ty, t);
        let t = d.arrow(hd_ty, t);
        let t = d.pi_fv(s2_fv, carrier, t);
        let t = d.pi_fv(m4_fv, carrier, t);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(pf_fv, fn_ty, t);
        d.pi_fv(y_fv, x_ty, t)
    };

    let want = build(&mut d, 3);
    assert!(
        d.kernel().def_eq(got, want),
        "the fourth-moment bound must be `Σ M₄ + 3(Σ σ²)²`"
    );
    let wrong = build(&mut d, 6);
    assert!(
        !d.kernel().def_eq(got, wrong),
        "6 is the OTHER multinomial coefficient in a fourth power; a control \
         blind to the difference is not a control on the coefficient"
    );
}

/// **The tail's threshold is `a⁴`, not `a²`.**
///
/// The whole point of paying for a fourth moment is that the threshold enters
/// at the fourth power, which is where the `1/m²` comes from; at `a²` this
/// would be Chebyshev's shape carrying a fourth-moment right-hand side, a
/// different and unproved claim. The declared type must be the `a⁴` one and
/// must NOT be the `a²` one.
#[test]
fn fourth_moment_tail_threshold_is_a_to_the_fourth_and_not_a_squared() {
    let (mut k, p) = prelude();
    let names = p.fourth_moment;
    let mut d = IntDev::new(&mut k, p.int);

    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, fn_ty);

    let c = d.kernel().const_(names.fourth_moment_tail_sum_vars, vec![]);
    let got = d
        .kernel()
        .infer(c)
        .expect("Rat.fourth_moment_tailSumVars must be declared");

    let build = |d: &mut IntDev<'_>, fourth_power: bool| -> ExprId {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let pf_fv = d.fresh_fvar();
        let pf = d.kernel().fvar(pf_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m4_fv = d.fresh_fvar();
        let m4 = d.kernel().fvar(m4_fv);
        let s2_fv = d.fresh_fvar();
        let s2 = d.kernel().fvar(s2_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let zero_r = rzero(d, p);
        let hd_ty = is_distribution(d, p, pf, n);
        let hs2_ty = rle(d, p, zero_r, s2);
        let ha_ty = rlt(d, p, zero_r, a);
        let hc_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi = d.lt(i, m);
            let yi = d.apply(y, &[i]);
            let e = expectation(d, p, yi, pf, n);
            let concl = req(d, e, zero_r);
            let inner = d.arrow(hi, concl);
            d.pi_fv(i_fv, nat, inner)
        };
        let hfw_ty = d.const_app(names.fourwise_uncorrelated, &[y, m, pf, n]);
        let h4_ty = fourth_moment_bounded(d, p, y, m4, pf, n, m);
        let h2_ty = second_moment_bounded(d, p, y, s2, pf, n, m);

        let sv = d.const_app(p.sum_vars, &[y, m]);
        let mu = expectation(d, p, sv, pf, n);
        let a_sq = rmul(d, a, a);
        let a_4 = rmul(d, a_sq, a_sq);
        let threshold = if fourth_power { a_4 } else { a_sq };
        let dev_fn = rat_fn(d, &|d, kk| {
            let sk = sv_at(d, p, y, m, kk);
            let gap = rsub(d, p, sk, mu);
            let sq = rmul(d, gap, gap);
            rmul(d, sq, sq)
        });
        let ind = d.const_app(p.indicator, &[threshold, dev_fn]);
        let e_ind = expectation(d, p, ind, pf, n);
        let lhs = rmul(d, threshold, e_ind);

        let const_m4 = const_fn(d, m4);
        let const_s2 = const_fn(d, s2);
        let sm = rsum_range(d, p, const_m4, m);
        let tsum = rsum_range(d, p, const_s2, m);
        let sq = rmul(d, tsum, tsum);
        let two = radd(d, sq, sq);
        let three = radd(d, two, sq);
        let rhs = radd(d, sm, three);
        let concl = rle(d, p, lhs, rhs);

        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h4_ty, t);
        let t = d.arrow(hfw_ty, t);
        let t = d.arrow(hc_ty, t);
        let t = d.arrow(ha_ty, t);
        let t = d.arrow(hs2_ty, t);
        let t = d.arrow(hd_ty, t);
        let t = d.pi_fv(m_fv, nat, t);
        let t = d.pi_fv(a_fv, carrier, t);
        let t = d.pi_fv(s2_fv, carrier, t);
        let t = d.pi_fv(m4_fv, carrier, t);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(pf_fv, fn_ty, t);
        d.pi_fv(y_fv, x_ty, t)
    };

    let want = build(&mut d, true);
    assert!(
        d.kernel().def_eq(got, want),
        "the tail must be stated at the threshold `a⁴`"
    );
    let wrong = build(&mut d, false);
    assert!(
        !d.kernel().def_eq(got, wrong),
        "at `a²` this would be Chebyshev's shape carrying a fourth-moment \
         right-hand side, which is a different and unproved claim"
    );
}
