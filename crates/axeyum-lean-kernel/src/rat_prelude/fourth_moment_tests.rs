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
    for slot in 0..4 {
        lt_ty.push(d.lt(idx[slot], m));
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
        if pi {
            d.pi_fv(h_fv, whole, t)
        } else {
            d.lam_fv(h_fv, whole, t)
        }
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
