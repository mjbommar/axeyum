//! Tests for [`nat_prelude::count_range_bij`](super::count_range_bij).
//!
//! A separate file rather than an addition to the dense `nat_prelude_tests.rs`,
//! per this repository's standing merge-hazard note.
//!
//! Four kinds of check, on disjoint defect classes:
//!
//! 1. **The arithmetic, before any proof term.** The two ranges the
//!    instantiation uses are counted by evaluation, and the count at the WRONG
//!    bound is shown to differ — otherwise "cross-bound" would be decoration
//!    over an instance where the bound never mattered.
//! 2. **A concrete instantiation with all five hypotheses DISCHARGED**, not
//!    assumed: `p := (1 ≤ ·)` on `[0,3)` selects `{1,2}`, `q := (2 ≤ ·)` on
//!    `[0,4)` selects `{2,3}`, and the bijection is `σ := succ` with inverse
//!    `τ := pred`. Different bounds, different selected sets, same count.
//! 3. **The declared type at genuinely FREE variables.** Numerals reduce, and
//!    reduction hides definitional-equality gaps a symbolic instantiation
//!    exposes; the inferred type is compared against the statement written out
//!    independently here, so a drifted binder order or hypothesis shape fails.
//! 4. **A negative control that fails to DISCHARGE, not merely one where the
//!    conclusion is false.** At `σ := fun _ => 3` the conclusion is false by
//!    evaluation (`2` against `1`), and — the sharper half — the injectivity
//!    hypothesis at that `σ` is shown to be UNINHABITED: a closed term of type
//!    `H1(σ) → False` type-checks, built by applying the hypothesis at the two
//!    distinct selected indices `1` and `2`, where `σ` agrees.

use crate::expr::ExprId;
use crate::tc::{LocalContext, LocalDecl};
use crate::{BinderInfo, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// Open a local context holding one free variable per supplied type, in
    /// order.
    fn open(&mut self, tys: &[ExprId]) -> (Vec<ExprId>, LocalContext) {
        let anon = self.anon_name();
        let mut ctx = LocalContext::new();
        let mut vars = Vec::with_capacity(tys.len());
        for ty in tys {
            let fv = self.fresh_fvar();
            vars.push(self.k.fvar(fv));
            ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty: *ty,
                info: BinderInfo::Default,
            });
        }
        (vars, ctx)
    }

    /// `fun i : Nat => Nat.ble c i`, i.e. the predicate `c ≤ ·`.
    fn at_least(&mut self, c: ExprId) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let body = self.ble(c, i);
        self.lam_fv(i_fv, nat, body)
    }

    /// `fun i : Nat => Nat.succ i`.
    fn succ_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let body = self.succ(i);
        self.lam_fv(i_fv, nat, body)
    }

    /// `fun j : Nat => Nat.pred j`.
    fn pred_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);
        let body = self.pred(j);
        self.lam_fv(j_fv, nat, body)
    }

    fn count(&mut self, pred: ExprId, n: ExprId) -> ExprId {
        let name = self.p.count_range;
        self.const_app(name, &[pred, n])
    }

    /// `h : Eq Nat a b`, `at_a : body a` ⊢ `body b`.
    fn transport_eq(
        &mut self,
        a: ExprId,
        b: ExprId,
        at_a: ExprId,
        h: ExprId,
        body: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let motive = self.eq_motive(a, body);
        self.transport(a, motive, at_a, b, h)
    }
}

/// The arithmetic the cross-bound law asserts, checked by evaluation before
/// any proof term is built — the numbers, not the theorem.
///
/// `(1 ≤ ·)` selects `{1,2}` below `3` and `(2 ≤ ·)` selects `{2,3}` below
/// `4`: two counts of `2` over DIFFERENT index sets at DIFFERENT bounds. The
/// third assertion is what makes "cross-bound" mean something: moving the left
/// bound from `3` to `4` changes its count to `3`, so the equality is not an
/// accident of a bound that never mattered.
#[test]
fn the_arithmetic_the_cross_bound_law_asserts_holds_at_the_instance() {
    let mut f = Fixture::new();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);

    let p_pred = f.at_least(one);
    let q_pred = f.at_least(two);

    let left = f.count(p_pred, three);
    assert!(
        f.k.def_eq(left, two),
        "countRange (1 <= .) 3 counts {{1,2}} and must be 2"
    );
    let right = f.count(q_pred, four);
    assert!(
        f.k.def_eq(right, two),
        "countRange (2 <= .) 4 counts {{2,3}} and must be 2"
    );

    // The bound is load-bearing: at `4` the left predicate selects `{1,2,3}`.
    let left_at_four = f.count(p_pred, four);
    assert!(
        f.k.def_eq(left_at_four, three),
        "countRange (1 <= .) 4 counts {{1,2,3}} and must be 3"
    );
    assert!(
        !f.k.def_eq(left_at_four, right),
        "the two bounds are genuinely different -- this is not one bound in disguise"
    );

    // The two selected sets are different, not merely equinumerous.
    let true_ = f.bool_true();
    let false_ = f.bool_false();
    let p_at_1 = f.apply(p_pred, &[one]);
    let q_at_1 = f.apply(q_pred, &[one]);
    assert!(f.k.def_eq(p_at_1, true_), "1 is selected on the left");
    assert!(f.k.def_eq(q_at_1, false_), "1 is NOT selected on the right");
    let q_at_3 = f.apply(q_pred, &[three]);
    assert!(
        f.k.def_eq(q_at_3, true_),
        "3 is selected on the right and is not even in the left range"
    );
}

/// `Nat.countRange_bij` at a fully CERTIFIED concrete instance: every one of
/// the five hypotheses is discharged from the prelude's own order lemmas
/// rather than assumed, so this is a real theorem instance and not merely a
/// type-check of an application.
///
/// `p := (1 ≤ ·)` on `[0,3)`, `q := (2 ≤ ·)` on `[0,4)`, `σ := succ`,
/// `τ := pred`. On the selected sets `σ` sends `1 ↦ 2` and `2 ↦ 3` and `τ`
/// sends them back; off the selected sets neither map is constrained, and
/// `σ 0 = 1` is deliberately NOT in the right-hand selected set, so the
/// hypotheses' restriction to the selected sets is exercised rather than
/// incidental.
#[test]
#[allow(clippy::too_many_lines)]
fn count_range_bij_certifies_a_cross_bound_bijection() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let true_ = f.bool_true();

    let p_pred = f.at_least(one);
    let q_pred = f.at_least(two);
    let sigma = f.succ_fn();
    let tau = f.pred_fn();

    // H1: `σ` is injective wherever it is applied — `pred (succ i) = i`.
    let h1 = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let hi_fv = f.fresh_fvar();
        let hpi_fv = f.fresh_fvar();
        let hj_fv = f.fresh_fvar();
        let hpj_fv = f.fresh_fvar();
        let he_fv = f.fresh_fvar();
        let he = f.k.fvar(he_fv);

        let si = f.apply(sigma, &[i]);
        let sj = f.apply(sigma, &[j]);
        let body = f.congr(si, sj, he, &|d: &mut Fixture, x| d.pred(x));

        let he_ty = f.eq(si, sj);
        let with_he = f.lam_fv(he_fv, he_ty, body);
        let pj = f.apply(p_pred, &[j]);
        let hpj_ty = f.bool_eq(pj, true_);
        let with_hpj = f.lam_fv(hpj_fv, hpj_ty, with_he);
        let hj_ty = f.lt(j, three);
        let with_hj = f.lam_fv(hj_fv, hj_ty, with_hpj);
        let pi = f.apply(p_pred, &[i]);
        let hpi_ty = f.bool_eq(pi, true_);
        let with_hpi = f.lam_fv(hpi_fv, hpi_ty, with_hj);
        let hi_ty = f.lt(i, three);
        let with_hi = f.lam_fv(hi_fv, hi_ty, with_hpi);
        let with_j = f.lam_fv(j_fv, nat, with_hi);
        f.lam_fv(i_fv, nat, with_j)
    };

    // H2: `succ` sends `{i < 3 | 1 ≤ i}` into `{j < 4 | 2 ≤ j}`.
    let h2 = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let hi_fv = f.fresh_fvar();
        let hi = f.k.fvar(hi_fv);
        let hp_fv = f.fresh_fvar();
        let hp = f.k.fvar(hp_fv);

        // `Lt i 3` is `Le (succ i) 3`, so `Le (succ (succ i)) 4` is one
        // `le_succ_succ` away and IS `Lt (succ i) 4`.
        let si = f.apply(sigma, &[i]);
        let succ_i = f.succ(i);
        let bound = f.const_app(p.le_succ_succ, &[succ_i, three, hi]);
        // `ble 1 i = true` gives `Le 1 i`, hence `Le 2 (succ i)`.
        let pi = f.apply(p_pred, &[i]);
        let le_1_i = f.const_app(p.le_of_ble_eq_true, &[one, i, hp]);
        let le_2_si = f.const_app(p.le_succ_succ, &[one, i, le_1_i]);
        let selected = f.const_app(p.ble_eq_true_of_le, &[two, si, le_2_si]);

        let bound_ty = f.lt(si, four);
        let q_si = f.apply(q_pred, &[si]);
        let sel_ty = f.bool_eq(q_si, true_);
        let pair = f.const_app(p.logic.and_intro, &[bound_ty, sel_ty, bound, selected]);

        let hp_ty = f.bool_eq(pi, true_);
        let with_hp = f.lam_fv(hp_fv, hp_ty, pair);
        let hi_ty = f.lt(i, three);
        let with_hi = f.lam_fv(hi_fv, hi_ty, with_hp);
        f.lam_fv(i_fv, nat, with_hi)
    };

    // H3: `pred` sends `{j < 4 | 2 ≤ j}` back into `{i < 3 | 1 ≤ i}`.
    let h3 = {
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let hj_fv = f.fresh_fvar();
        let hj = f.k.fvar(hj_fv);
        let hq_fv = f.fresh_fvar();
        let hq = f.k.fvar(hq_fv);

        let le_2_j = f.const_app(p.le_of_ble_eq_true, &[two, j, hq]);
        // `Lt 0 j` is `Le 1 j`, from `Le 1 2` and `Le 2 j`.
        let le_1_2 = f.const_app(p.le_succ, &[one]);
        let pos = f.const_app(p.le_trans, &[one, two, j, le_1_2, le_2_j]);
        // `j = succ (pred j)`.
        let unfold = f.const_app(p.succ_pred_of_pos, &[j, pos]);
        let pred_j = f.pred(j);
        let succ_pred_j = f.succ(pred_j);

        // `Lt j 4` is `Le (succ j) (succ 3)`, so `Le j 3`.
        let le_j_3 = f.const_app(p.le_of_succ_le_succ, &[j, three, hj]);
        let tj = f.apply(tau, &[j]);
        let bound = f.transport_eq(j, succ_pred_j, le_j_3, unfold, &|d: &mut Fixture, x| {
            let three = d.num(3);
            d.le(x, three)
        });
        // `Le 2 (succ (pred j))` strips to `Le 1 (pred j)`.
        let le_2_unfolded =
            f.transport_eq(j, succ_pred_j, le_2_j, unfold, &|d: &mut Fixture, x| {
                let two = d.num(2);
                d.le(two, x)
            });
        let le_1_pred = f.const_app(p.le_of_succ_le_succ, &[one, pred_j, le_2_unfolded]);
        let selected = f.const_app(p.ble_eq_true_of_le, &[one, tj, le_1_pred]);

        let bound_ty = f.lt(tj, three);
        let p_tj = f.apply(p_pred, &[tj]);
        let sel_ty = f.bool_eq(p_tj, true_);
        let pair = f.const_app(p.logic.and_intro, &[bound_ty, sel_ty, bound, selected]);

        let qj = f.apply(q_pred, &[j]);
        let hq_ty = f.bool_eq(qj, true_);
        let with_hq = f.lam_fv(hq_fv, hq_ty, pair);
        let hj_ty = f.lt(j, four);
        let with_hj = f.lam_fv(hj_fv, hj_ty, with_hq);
        f.lam_fv(j_fv, nat, with_hj)
    };

    // H4: `pred (succ i) = i` — `Eq.refl`, by ι-reduction.
    let h4 = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let hi_fv = f.fresh_fvar();
        let hp_fv = f.fresh_fvar();
        let body = f.refl(i);
        let pi = f.apply(p_pred, &[i]);
        let hp_ty = f.bool_eq(pi, true_);
        let with_hp = f.lam_fv(hp_fv, hp_ty, body);
        let hi_ty = f.lt(i, three);
        let with_hi = f.lam_fv(hi_fv, hi_ty, with_hp);
        f.lam_fv(i_fv, nat, with_hi)
    };

    // H5: `succ (pred j) = j` on the selected set, where `j` is positive.
    let h5 = {
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let hj_fv = f.fresh_fvar();
        let hq_fv = f.fresh_fvar();
        let hq = f.k.fvar(hq_fv);

        let le_2_j = f.const_app(p.le_of_ble_eq_true, &[two, j, hq]);
        let le_1_2 = f.const_app(p.le_succ, &[one]);
        let pos = f.const_app(p.le_trans, &[one, two, j, le_1_2, le_2_j]);
        let unfold = f.const_app(p.succ_pred_of_pos, &[j, pos]);
        let pred_j = f.pred(j);
        let succ_pred_j = f.succ(pred_j);
        let body = f.symm(j, succ_pred_j, unfold);

        let qj = f.apply(q_pred, &[j]);
        let hq_ty = f.bool_eq(qj, true_);
        let with_hq = f.lam_fv(hq_fv, hq_ty, body);
        let hj_ty = f.lt(j, four);
        let with_hj = f.lam_fv(hj_fv, hj_ty, with_hq);
        f.lam_fv(j_fv, nat, with_hj)
    };

    let proof = f.const_app(
        p.count_range_bij,
        &[p_pred, q_pred, sigma, tau, three, four, h1, h2, h3, h4, h5],
    );
    let inferred = match f.k.infer(proof) {
        Ok(t) => t,
        Err(e) => panic!(
            "countRange_bij must apply at (1<=.) on [0,3) <-> (2<=.) on [0,4): {}",
            f.explain(&e)
        ),
    };

    let lhs = f.count(p_pred, three);
    let rhs = f.count(q_pred, four);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the instance must state countRange (1<=.) 3 = countRange (2<=.) 4"
    );

    // Both sides compute to 2 — the kernel accepting the application says
    // nothing about what either side counts.
    let two_again = f.num(2);
    assert!(f.k.def_eq(lhs, two_again), "the left count must be 2");
    assert!(f.k.def_eq(rhs, two_again), "the right count must be 2");

    for name in [p.count_range_bij, p.count_range_eq_zero_of_all_false] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "the cross-bound counting family must rest on zero axioms"
        );
    }
}

/// The two new laws applied at genuinely FREE variables, not numerals.
///
/// Numerals reduce, and reduction hides definitional-equality gaps that a
/// symbolic instantiation exposes. Each inferred type is checked against the
/// statement written out independently here, so a declaration whose binder
/// order or hypothesis shape drifted would fail rather than pass.
#[test]
#[allow(clippy::too_many_lines)]
fn the_cross_bound_family_applies_at_free_variables() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let bool_ty = f.bool_ty();
    let pred_ty = f.arrow(nat, bool_ty);
    let fn_ty = f.arrow(nat, nat);
    let true_ = f.bool_true();
    let false_ = f.bool_false();

    // --- `countRange_eq_zero_of_all_false` ---------------------------------
    {
        let (vars, mut ctx) = f.open(&[pred_ty, nat]);
        let (g, n) = (vars[0], vars[1]);
        let hyp_ty = {
            let k_fv = f.fresh_fvar();
            let k = f.k.fvar(k_fv);
            let gk = f.apply(g, &[k]);
            let eq = f.bool_eq(gk, false_);
            let bound = f.lt(k, n);
            let inner = f.arrow(bound, eq);
            f.pi_fv(k_fv, nat, inner)
        };
        let anon = f.anon_name();
        let hfv = f.fresh_fvar();
        let hvar = f.k.fvar(hfv);
        ctx.push(LocalDecl {
            fvar: hfv,
            name: anon,
            ty: hyp_ty,
            info: BinderInfo::Default,
        });
        let applied = f.const_app(p.count_range_eq_zero_of_all_false, &[g, n, hvar]);
        let inferred = match f.k.infer_in(applied, &mut ctx) {
            Ok(t) => t,
            Err(e) => panic!(
                "countRange_eq_zero_of_all_false must apply at free f, n: {}",
                f.explain(&e)
            ),
        };
        let count = f.count(g, n);
        let zero = f.zero();
        let expected = f.eq(count, zero);
        assert!(
            f.k.def_eq(inferred, expected),
            "the symbolic statement must be countRange f n = 0"
        );
    }

    // --- `countRange_bij` ---------------------------------------------------
    let (vars, mut ctx) = f.open(&[pred_ty, pred_ty, fn_ty, fn_ty, nat, nat]);
    let (pp, q, sigma, tau, n, m) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);

    // Write the five hypothesis types out independently of the declaration.
    let h1_ty = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let si = f.apply(sigma, &[i]);
        let sj = f.apply(sigma, &[j]);
        let concl = f.eq(i, j);
        let heq = f.eq(si, sj);
        let s5 = f.arrow(heq, concl);
        let pj = f.apply(pp, &[j]);
        let selj = f.bool_eq(pj, true_);
        let s4 = f.arrow(selj, s5);
        let bj = f.lt(j, n);
        let s3 = f.arrow(bj, s4);
        let pi = f.apply(pp, &[i]);
        let seli = f.bool_eq(pi, true_);
        let s2 = f.arrow(seli, s3);
        let bi = f.lt(i, n);
        let s1 = f.arrow(bi, s2);
        let with_j = f.pi_fv(j_fv, nat, s1);
        f.pi_fv(i_fv, nat, with_j)
    };
    let maps_ty = |f: &mut Fixture, from: ExprId, to: ExprId, g: ExprId, src, dst| {
        let nat = f.nat_ty();
        let true_ = f.bool_true();
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let gi = f.apply(g, &[i]);
        let bound = f.lt(gi, dst);
        let to_gi = f.apply(to, &[gi]);
        let selected = f.bool_eq(to_gi, true_);
        let and_name = f.p.logic.and;
        let concl = f.const_app(and_name, &[bound, selected]);
        let from_i = f.apply(from, &[i]);
        let sel_i = f.bool_eq(from_i, true_);
        let s2 = f.arrow(sel_i, concl);
        let bi = f.lt(i, src);
        let s1 = f.arrow(bi, s2);
        f.pi_fv(i_fv, nat, s1)
    };
    let round_ty = |f: &mut Fixture, pred: ExprId, g: ExprId, h: ExprId, src| {
        let nat = f.nat_ty();
        let true_ = f.bool_true();
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let gi = f.apply(g, &[i]);
        let hgi = f.apply(h, &[gi]);
        let concl = f.eq(hgi, i);
        let pred_i = f.apply(pred, &[i]);
        let sel_i = f.bool_eq(pred_i, true_);
        let s2 = f.arrow(sel_i, concl);
        let bi = f.lt(i, src);
        let s1 = f.arrow(bi, s2);
        f.pi_fv(i_fv, nat, s1)
    };
    let h2_ty = maps_ty(&mut f, pp, q, sigma, n, m);
    let h3_ty = maps_ty(&mut f, q, pp, tau, m, n);
    let h4_ty = round_ty(&mut f, pp, sigma, tau, n);
    let h5_ty = round_ty(&mut f, q, tau, sigma, m);

    let anon = f.anon_name();
    let mut hyp_vars = Vec::new();
    for ty in [h1_ty, h2_ty, h3_ty, h4_ty, h5_ty] {
        let fv = f.fresh_fvar();
        hyp_vars.push(f.k.fvar(fv));
        ctx.push(LocalDecl {
            fvar: fv,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let mut args = vec![pp, q, sigma, tau, n, m];
    args.extend_from_slice(&hyp_vars);
    let applied = f.const_app(p.count_range_bij, &args);
    let inferred = match f.k.infer_in(applied, &mut ctx) {
        Ok(t) => t,
        Err(e) => panic!(
            "countRange_bij must apply at free p, q, sigma, tau, n, m: {}",
            f.explain(&e)
        ),
    };
    let lhs = f.count(pp, n);
    let rhs = f.count(q, m);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the symbolic statement must be countRange p n = countRange q m"
    );
}

/// NEGATIVE CONTROL: a `σ` that is not injective on the selected set cannot
/// DISCHARGE the injectivity hypothesis — the stronger statement than "the
/// conclusion happens to be false there".
///
/// `σ := fun _ => 3` maps both selected indices `1` and `2` of `p := (1 ≤ ·)`
/// to the single selected index `3` of `q := (3 ≤ ·)`, and satisfies the
/// `MapsInto` half. The conclusion is then FALSE by evaluation (`2` against
/// `1`), and the hypothesis is not merely unproved but UNINHABITED: the closed
/// term built here has type `H1(σ) → False`, so no proof of `H1(σ)` can exist.
#[test]
fn a_non_injective_sigma_cannot_discharge_the_hypothesis() {
    let mut f = Fixture::new();
    let p = f.p;
    let nat = f.nat_ty();
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let four = f.num(4);
    let true_ = f.bool_true();

    let p_pred = f.at_least(one);
    let q_bad = f.at_least(three);
    let sigma_bad = {
        let i_fv = f.fresh_fvar();
        f.lam_fv(i_fv, nat, three)
    };

    // The conclusion is false at this instance: 2 against 1.
    let lhs = f.count(p_pred, three);
    let rhs = f.count(q_bad, four);
    assert!(f.k.def_eq(lhs, two), "the left count is 2");
    assert!(f.k.def_eq(rhs, one), "the right count is 1");
    assert!(
        !f.k.def_eq(lhs, rhs),
        "the conclusion is FALSE at the non-injective sigma"
    );

    // `H1(σ_bad)` written out, exactly as `countRange_bij` states it.
    let h1_ty = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let si = f.apply(sigma_bad, &[i]);
        let sj = f.apply(sigma_bad, &[j]);
        let concl = f.eq(i, j);
        let heq = f.eq(si, sj);
        let s5 = f.arrow(heq, concl);
        let pj = f.apply(p_pred, &[j]);
        let selj = f.bool_eq(pj, true_);
        let s4 = f.arrow(selj, s5);
        let bj = f.lt(j, three);
        let s3 = f.arrow(bj, s4);
        let pi = f.apply(p_pred, &[i]);
        let seli = f.bool_eq(pi, true_);
        let s2 = f.arrow(seli, s3);
        let bi = f.lt(i, three);
        let s1 = f.arrow(bi, s2);
        let with_j = f.pi_fv(j_fv, nat, s1);
        f.pi_fv(i_fv, nat, with_j)
    };

    // `fun h => absurd (h 1 2 … refl)` : `H1(σ_bad) → False`.
    let refuter = {
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);
        // `Lt 1 3` is `Le 2 3`; `Lt 2 3` is `Le 3 3`; `Lt 1 2` is `Le 2 2`.
        let lt_1_3 = f.const_app(p.le_succ, &[two]);
        let lt_2_3 = f.const_app(p.le_refl, &[three]);
        let lt_1_2 = f.const_app(p.le_refl, &[two]);
        let sel_1 = f.bool_refl(true_);
        let sel_2 = f.bool_refl(true_);
        let agree = f.refl(three);
        let one_eq_two = f.apply(h, &[one, two, lt_1_3, sel_1, lt_2_3, sel_2, agree]);
        let two_lt_two = f.transport_eq(one, two, lt_1_2, one_eq_two, &|d: &mut Fixture, x| {
            let two = d.num(2);
            d.lt(x, two)
        });
        let contra = f.const_app(p.lt_irrefl, &[two, two_lt_two]);
        f.lam_fv(h_fv, h1_ty, contra)
    };

    let inferred = match f.k.infer(refuter) {
        Ok(t) => t,
        Err(e) => panic!(
            "the refutation of the non-injective hypothesis must type-check: {}",
            f.explain(&e)
        ),
    };
    let false_ty = f.k.const_(p.logic.false_, vec![]);
    let expected = f.arrow(h1_ty, false_ty);
    assert!(
        f.k.def_eq(inferred, expected),
        "the refuter must have type H1(sigma_bad) -> False, i.e. the hypothesis \
         is uninhabited and cannot be discharged"
    );

    // The control is not INVERTED: the same refutation shape must FAIL at the
    // injective `σ := succ`, where `Eq.refl 3` no longer has the type the
    // hypothesis's last argument demands (`Eq (succ 1) (succ 2)`, i.e. `2 = 3`).
    // Without this the test above would pass for a `σ` that is perfectly
    // injective, and would be measuring nothing.
    let sigma_good = f.succ_fn();
    let good_h1_ty = {
        let i_fv = f.fresh_fvar();
        let i = f.k.fvar(i_fv);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let si = f.apply(sigma_good, &[i]);
        let sj = f.apply(sigma_good, &[j]);
        let concl = f.eq(i, j);
        let heq = f.eq(si, sj);
        let s5 = f.arrow(heq, concl);
        let pj = f.apply(p_pred, &[j]);
        let selj = f.bool_eq(pj, true_);
        let s4 = f.arrow(selj, s5);
        let bj = f.lt(j, three);
        let s3 = f.arrow(bj, s4);
        let pi = f.apply(p_pred, &[i]);
        let seli = f.bool_eq(pi, true_);
        let s2 = f.arrow(seli, s3);
        let bi = f.lt(i, three);
        let s1 = f.arrow(bi, s2);
        let with_j = f.pi_fv(j_fv, nat, s1);
        f.pi_fv(i_fv, nat, with_j)
    };
    let good_attempt = {
        let h_fv = f.fresh_fvar();
        let h = f.k.fvar(h_fv);
        let lt_1_3 = f.const_app(p.le_succ, &[two]);
        let lt_2_3 = f.const_app(p.le_refl, &[three]);
        let lt_1_2 = f.const_app(p.le_refl, &[two]);
        let sel_1 = f.bool_refl(true_);
        let sel_2 = f.bool_refl(true_);
        let agree = f.refl(three);
        let one_eq_two = f.apply(h, &[one, two, lt_1_3, sel_1, lt_2_3, sel_2, agree]);
        let two_lt_two = f.transport_eq(one, two, lt_1_2, one_eq_two, &|d: &mut Fixture, x| {
            let two = d.num(2);
            d.lt(x, two)
        });
        let contra = f.const_app(p.lt_irrefl, &[two, two_lt_two]);
        f.lam_fv(h_fv, good_h1_ty, contra)
    };
    assert!(
        f.k.infer(good_attempt).is_err(),
        "the same refutation must NOT type-check at the injective sigma := succ \
         -- otherwise the negative control is inverted and measures nothing"
    );
}
