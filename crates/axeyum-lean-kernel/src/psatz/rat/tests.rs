//! Tests for the ℚ `psatz` producer.
//!
//! Four batteries, in the shape `ring`/`linarith` already use:
//!
//! 1. **Positive cases** — the three inequalities ADR-1649 names, each
//!    DECLARED through `Kernel::add_declaration` and each asserted to have an
//!    EMPTY axiom footprint after `Environment::contains` confirms the name is
//!    really there (an empty footprint is also what a missing name returns).
//! 2. **The Positivstellensatz product shape** — `0 ≤ x → 0 ≤ y → 0 ≤ x·y`,
//!    the one shape beyond pure SOS this producer covers.
//! 3. **Refusals** — the Motzkin form must refuse with `PsdNotSos` and nothing
//!    else, an indefinite form must refuse with `NotPsd`, and a non-`le` goal
//!    with `GoalNotLe`.
//! 4. **A corrupted certificate is refused by the KERNEL** — the producer's
//!    own identity check is deliberately switched off (`ring::rat`'s
//!    `prove_eq_unverified`, the same device that module's corruption tests
//!    use) so the trust story is not circular: what refuses the wrong term is
//!    the trusted gate, not the search that produced it.

#![allow(clippy::many_single_char_names)]

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::psatz::rat::{Ctx, prove};
use crate::psatz::{Decline, DualWitness, Q};
use crate::rat_prelude::ops::{radd, rle, rmul, rneg, rzero};
use crate::{Kernel, NameId, RatPrelude, build_rat_prelude, on_a_deep_stack};

use std::collections::BTreeMap;

struct Fixture {
    k: Kernel,
    p: RatPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("Rat prelude must build");
        Self { k, p }
    }

    fn dev(&mut self) -> IntDev<'_> {
        IntDev::new(&mut self.k, self.p.int)
    }
}

fn name(d: &mut IntDev<'_>, s: &str) -> NameId {
    let anon = d.kernel().anon();
    d.kernel().name_str(anon, s)
}

/// Declare `theorem tag : ∀ vars, concl := proof`, then require the kernel to
/// have it AND to measure its footprint empty.
///
/// The `Environment::contains` half is load-bearing: `axiom_footprint` of a name
/// that was never declared is also empty, so without it this asserts nothing.
fn declare_axiom_free(
    d: &mut IntDev<'_>,
    tag: &str,
    vars: &[(u64, ExprId)],
    concl: ExprId,
    proof: ExprId,
) -> NameId {
    let mut ty = concl;
    let mut value = proof;
    for &(fv, vty) in vars.iter().rev() {
        ty = d.pi_fv(fv, vty, ty);
        value = d.lam_fv(fv, vty, value);
    }
    let n = name(d, tag);
    d.declare_theorem(n, ty, value)
        .unwrap_or_else(|e| panic!("{tag}: kernel rejected the emitted term: {e:?}"));
    assert!(
        d.kernel().environment().contains(n),
        "{tag}: the kernel accepted the declaration but the environment does \
         not hold the name — every footprint assertion below would be vacuous"
    );
    let footprint = d.kernel().axiom_footprint(n);
    assert!(footprint.is_empty(), "{tag} rests on axioms: {footprint:?}");
    n
}

/// `n` fresh `Rat`-typed free variables, with the type for the binders.
fn rat_vars(d: &mut IntDev<'_>, n: usize) -> (Vec<u64>, Vec<ExprId>, ExprId) {
    let ty = crate::rat_prelude::ops::rat_ty(d);
    let fvs: Vec<u64> = (0..n).map(|_| d.fresh_fvar()).collect();
    let terms: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    (fvs, terms, ty)
}

fn sq(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    rmul(d, a, a)
}

// ---------------------------------------------------------------------------
// 1. positive cases
// ---------------------------------------------------------------------------

/// `2xy ≤ x² + y²`, the two-variable AM–GM in its polynomial form. The
/// certificate is `(x − y)²` and needs no scale.
#[test]
fn two_variable_am_gm_is_discharged() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (fvs, v, ty) = rat_vars(&mut d, 2);
        let (x, y) = (v[0], v[1]);

        let xy = rmul(&mut d, x, y);
        let lhs = radd(&mut d, xy, xy);
        let xx = sq(&mut d, x);
        let yy = sq(&mut d, y);
        let rhs = radd(&mut d, xx, yy);
        let goal = rle(&mut d, p, lhs, rhs);

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        let proof = prove(&mut d, &ctx, goal)
            .unwrap_or_else(|e| panic!("psatz declined 2xy ≤ x²+y²: {e:?}"));
        declare_axiom_free(
            &mut d,
            "psatz_two_var_am_gm",
            &[(fvs[0], ty), (fvs[1], ty)],
            goal,
            proof,
        );
    });
}

/// `ab + bc + ca ≤ a² + b² + c²`. The certificate is
/// `4p = (2a−b−c)² + 3(b−c)²`: the scale is **forced**, not chosen — the Gram
/// matrix has half-integer off-diagonals, so no unit-weight integer-form
/// decomposition of `p` exists at all. This is the test that exercises
/// `divide_by_scale`.
#[test]
fn three_variable_am_gm_is_discharged_through_the_scale_four_division() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (fvs, v, ty) = rat_vars(&mut d, 3);
        let (a, b, c) = (v[0], v[1], v[2]);

        let ab = rmul(&mut d, a, b);
        let bc = rmul(&mut d, b, c);
        let ca = rmul(&mut d, c, a);
        let sum_products = radd(&mut d, ab, bc);
        let lhs = radd(&mut d, sum_products, ca);

        let aa = sq(&mut d, a);
        let bb = sq(&mut d, b);
        let cc = sq(&mut d, c);
        let sum_squares = radd(&mut d, aa, bb);
        let rhs = radd(&mut d, sum_squares, cc);

        let goal = rle(&mut d, p, lhs, rhs);
        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        let proof = prove(&mut d, &ctx, goal)
            .unwrap_or_else(|e| panic!("psatz declined ab+bc+ca ≤ a²+b²+c²: {e:?}"));
        declare_axiom_free(
            &mut d,
            "psatz_three_var_am_gm",
            &[(fvs[0], ty), (fvs[1], ty), (fvs[2], ty)],
            goal,
            proof,
        );
    });
}

/// The AM–GM two-variable form in its "squared means" spelling:
/// `4ab ≤ (a + b)²`, whose difference is `(a − b)²`. Same mathematics as the
/// first case, a DIFFERENT goal shape — the right side is a product of sums,
/// so the parse has to distribute before the Gram matrix exists.
#[test]
fn am_gm_squared_means_form_is_discharged() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (fvs, v, ty) = rat_vars(&mut d, 2);
        let (a, b) = (v[0], v[1]);

        let ab = rmul(&mut d, a, b);
        let two_ab = radd(&mut d, ab, ab);
        let lhs = radd(&mut d, two_ab, two_ab);

        let a_plus_b = radd(&mut d, a, b);
        let rhs = rmul(&mut d, a_plus_b, a_plus_b);

        let goal = rle(&mut d, p, lhs, rhs);
        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        let proof = prove(&mut d, &ctx, goal)
            .unwrap_or_else(|e| panic!("psatz declined 4ab ≤ (a+b)²: {e:?}"));
        declare_axiom_free(
            &mut d,
            "psatz_am_gm_squared_means",
            &[(fvs[0], ty), (fvs[1], ty)],
            goal,
            proof,
        );
    });
}

// ---------------------------------------------------------------------------
// 2. the Positivstellensatz product shape
// ---------------------------------------------------------------------------

/// `0 ≤ x → 0 ≤ y → 0 ≤ x·y` — the ONE Positivstellensatz shape beyond pure
/// SOS this producer lands. `x·y` is provably NOT a sum of squares (its Gram
/// matrix is `[[0, ½], [½, 0]]`, indefinite), so the pure-SOS route reports
/// `NotPsd` and only the hypothesis product closes it.
#[test]
fn the_hypothesis_product_shape_is_discharged() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (fvs, v, ty) = rat_vars(&mut d, 2);
        let (x, y) = (v[0], v[1]);

        let zero = rzero(&mut d, p);
        let product = rmul(&mut d, x, y);
        let goal = rle(&mut d, p, zero, product);

        // Without the hypotheses the producer must report the FINDING that the
        // difference is not PSD — the control that the product is doing the work.
        let bare = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        assert!(
            matches!(prove(&mut d, &bare, goal), Err(Decline::NotPsd { .. })),
            "x·y is not a sum of squares; without hypotheses the producer must \
             say so rather than find a certificate"
        );

        let hx_fv = d.fresh_fvar();
        let hy_fv = d.fresh_fvar();
        let hx_ty = rle(&mut d, p, zero, x);
        let hy_ty = rle(&mut d, p, zero, y);
        let hx = d.kernel().fvar(hx_fv);
        let hy = d.kernel().fvar(hy_fv);
        let assumptions = [(hx_ty, hx), (hy_ty, hy)];
        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            dual: None,
        };
        let proof = prove(&mut d, &ctx, goal)
            .unwrap_or_else(|e| panic!("psatz declined 0 ≤ x·y under 0≤x, 0≤y: {e:?}"));
        declare_axiom_free(
            &mut d,
            "psatz_hypothesis_product",
            &[(fvs[0], ty), (fvs[1], ty), (hx_fv, hx_ty), (hy_fv, hy_ty)],
            goal,
            proof,
        );
    });
}

// ---------------------------------------------------------------------------
// 3. refusals
// ---------------------------------------------------------------------------

/// The Motzkin form `x⁴y² + x²y⁴ + z⁶ − 3x²y²z²` is nonnegative on the reals
/// and **not** a sum of squares. With the CAS's dual moment functional supplied
/// as a witness — and CHECKED here, not believed — the producer must refuse
/// with exactly `PsdNotSos`.
///
/// The reason matters: `DegreeUnsupported` would say "we did not look", and
/// `NotPsd` would say "the goal is false", and the Motzkin form is neither.
#[test]
fn the_motzkin_form_refuses_with_psd_not_sos() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (_, v, _) = rat_vars(&mut d, 3);
        let (x, y, z) = (v[0], v[1], v[2]);

        let goal = motzkin_goal(&mut d, p, x, y, z);
        let witness = motzkin_dual_witness(&mut d, p, x, y, z);

        // Without a witness the honest answer is "the search does not run at
        // this degree" — never `PsdNotSos`, which is a claim about the form.
        let bare = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        assert_eq!(
            prove(&mut d, &bare, goal),
            Err(Decline::DegreeUnsupported { degree: 6 }),
            "with no witness the producer must say it did not look, not that \
             the form is not a sum of squares"
        );

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: Some(&witness),
        };
        assert_eq!(
            prove(&mut d, &ctx, goal),
            Err(Decline::PsdNotSos),
            "the Motzkin form is PSD-not-SOS and the refusal must say exactly that"
        );
    });
}

/// A witness that does not check must NOT be reported as `PsdNotSos`. Without
/// this, `PsdNotSos` would be "a witness was offered", not "a witness was
/// verified" — the checker-that-cannot-fail defect.
#[test]
fn an_unverified_witness_is_reported_as_invalid_not_as_psd_not_sos() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (_, v, _) = rat_vars(&mut d, 3);
        let (x, y, z) = (v[0], v[1], v[2]);

        let goal = motzkin_goal(&mut d, p, x, y, z);
        let mut witness = motzkin_dual_witness(&mut d, p, x, y, z);
        // Break the x-block's exact singularity: 450 is what makes its 3x3
        // determinant zero, so 1 makes the moment matrix indefinite.
        let broken = witness
            .moments
            .keys()
            .find(|m| m.len() == 6 && m.iter().all(|&v| v == m[0]) && m[0] == 0)
            .cloned()
            .expect("the x⁶ moment is present");
        witness.moments.insert(broken, Q::integer(1));

        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: Some(&witness),
        };
        assert_eq!(prove(&mut d, &ctx, goal), Err(Decline::DualWitnessInvalid));
    });
}

/// An indefinite quadratic form is a FINDING: the goal is false.
#[test]
fn an_indefinite_form_refuses_with_not_psd() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (_, v, _) = rat_vars(&mut d, 2);
        let (x, y) = (v[0], v[1]);
        let zero = rzero(&mut d, p);
        let xx = sq(&mut d, x);
        let yy = sq(&mut d, y);
        let neg_yy = rneg(&mut d, yy);
        let difference = radd(&mut d, xx, neg_yy);
        let goal = rle(&mut d, p, zero, difference);
        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        assert!(matches!(
            prove(&mut d, &ctx, goal),
            Err(Decline::NotPsd { .. })
        ));
    });
}

/// A goal that is not `Rat.le _ _` at all.
#[test]
fn a_non_le_goal_refuses_with_goal_not_le() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (_, v, _) = rat_vars(&mut d, 1);
        let x = v[0];
        let goal = crate::rat_prelude::ops::req(&mut d, x, x);
        let ctx = Ctx {
            prelude: p,
            assumptions: &[],
            dual: None,
        };
        assert_eq!(prove(&mut d, &ctx, goal), Err(Decline::GoalNotLe));
    });
}

/// A hypothesis whose statement is not `0 ≤ h`.
#[test]
fn a_malformed_hypothesis_refuses() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (_, v, _) = rat_vars(&mut d, 2);
        let (x, y) = (v[0], v[1]);
        let zero = rzero(&mut d, p);
        let product = rmul(&mut d, x, y);
        let goal = rle(&mut d, p, zero, product);
        // `x ≤ y` is a perfectly good proposition and not of the form `0 ≤ h`.
        let bad_ty = rle(&mut d, p, x, y);
        let fv = d.fresh_fvar();
        let bad = d.kernel().fvar(fv);
        let assumptions = [(bad_ty, bad)];
        let ctx = Ctx {
            prelude: p,
            assumptions: &assumptions,
            dual: None,
        };
        assert_eq!(prove(&mut d, &ctx, goal), Err(Decline::HypothesisNotNonneg));
    });
}

// ---------------------------------------------------------------------------
// 4. a corrupted certificate is refused by the KERNEL
// ---------------------------------------------------------------------------

/// Flip the sign of a certificate weight and emit the term with the producer's
/// OWN identity check switched off, so the only thing standing between the
/// wrong certificate and an admitted theorem is `Kernel::add_declaration`.
///
/// `2xy ≤ x² + y²` has the certificate `1 × (x − y)²`. Flipping the linear
/// form's `y` coefficient gives `(x + y)²`, which expands to
/// `x² + 2xy + y² ≠ x² + y² − 2xy` — a certificate for the *wrong* difference,
/// and one whose emitted term therefore does not typecheck.
#[test]
fn a_sign_flipped_weight_is_refused_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let mut d = f.dev();
        let (fvs, v, ty) = rat_vars(&mut d, 2);
        let (x, y) = (v[0], v[1]);
        let binders = [(fvs[0], ty), (fvs[1], ty)];

        let xy = rmul(&mut d, x, y);
        let lhs = radd(&mut d, xy, xy);
        let xx = sq(&mut d, x);
        let yy = sq(&mut d, y);
        let rhs = radd(&mut d, xx, yy);
        let goal = rle(&mut d, p, lhs, rhs);

        let honest = crate::psatz::Certificate {
            scale: 1,
            atoms: vec![(
                1,
                crate::psatz::Atom::Square {
                    constant: 0,
                    linear: vec![(0, 1), (1, -1)],
                },
            )],
        };
        let corrupt = crate::psatz::Certificate {
            scale: 1,
            atoms: vec![(
                1,
                crate::psatz::Atom::Square {
                    constant: 0,
                    linear: vec![(0, 1), (1, 1)],
                },
            )],
        };

        // The control: the HONEST certificate, emitted the same way, IS accepted.
        // Without it this test would pass even if `emit_unverified` never built
        // anything a kernel could accept.
        let atoms = [x, y];
        let good = super::emit_unverified(&mut d, p, &atoms, &[], &honest, lhs, rhs)
            .expect("the honest certificate emits");
        declare_axiom_free(&mut d, "psatz_corruption_control", &binders, goal, good);

        let bad = super::emit_unverified(&mut d, p, &atoms, &[], &corrupt, lhs, rhs);
        match bad {
            Err(e) => {
                // The ring producer built no term at all; the corruption never
                // reached the kernel. Still a refusal, and reported as one.
                panic!(
                    "the corrupted certificate was refused before the kernel saw \
                     it ({e:?}); this test is meant to make the KERNEL the \
                     refuser, so `emit_unverified` must reach it"
                );
            }
            Ok(term) => {
                let mut ty_all = goal;
                let mut value = term;
                for &(fv, vty) in binders.iter().rev() {
                    ty_all = d.pi_fv(fv, vty, ty_all);
                    value = d.lam_fv(fv, vty, value);
                }
                let n = name(&mut d, "psatz_corrupted_weight");
                let outcome = d.declare_theorem(n, ty_all, value);
                assert!(
                    outcome.is_err(),
                    "the KERNEL accepted a proof built from a certificate whose \
                     weight sign was flipped — the trusted gate did not hold"
                );
            }
        }
    });
}

// ---------------------------------------------------------------------------
// helpers for the Motzkin fixtures
// ---------------------------------------------------------------------------

/// The goal `0 ≤ x⁴y² + x²y⁴ + z⁶ − 3x²y²z²`, built with `Rat.add`/`Rat.mul`/
/// `Rat.neg` only (the producer's fragment).
fn motzkin_goal(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let power = |d: &mut IntDev<'_>, base: ExprId, n: usize| {
        let mut acc = base;
        for _ in 1..n {
            acc = rmul(d, acc, base);
        }
        acc
    };
    let x4 = power(d, x, 4);
    let y2 = power(d, y, 2);
    let x2 = power(d, x, 2);
    let y4 = power(d, y, 4);
    let z6 = power(d, z, 6);
    let z2 = power(d, z, 2);

    let t1 = rmul(d, x4, y2);
    let t2 = rmul(d, x2, y4);
    let x2y2 = rmul(d, x2, y2);
    let x2y2z2 = rmul(d, x2y2, z2);
    let neg = rneg(d, x2y2z2);

    let sum = radd(d, t1, t2);
    let sum = radd(d, sum, z6);
    let sum = radd(d, sum, neg);
    let sum = radd(d, sum, neg);
    let sum = radd(d, sum, neg);

    let zero = rzero(d, p);
    rle(d, p, zero, sum)
}

/// The CAS's Motzkin dual moment functional, expressed over the atom indices
/// the producer's parser assigns to `x`, `y`, `z`.
///
/// The parser indexes atoms in first-encounter order over the goal built by
/// [`motzkin_goal`], which walks `x` before `y` before `z`, so the indices are
/// `x ↦ 0`, `y ↦ 1`, `z ↦ 2`. That is asserted, not assumed: the producer's
/// `DegreeUnsupported { degree: 6 }` answer in the same test confirms the parse
/// reached the whole form, and a wrong index assignment would make the witness
/// fail to verify rather than silently pass.
fn motzkin_dual_witness(
    _d: &mut IntDev<'_>,
    _p: RatPrelude,
    _x: ExprId,
    _y: ExprId,
    _z: ExprId,
) -> DualWitness {
    let entries: &[(&[usize], i128)] = &[
        (&[0, 0, 0, 0, 0, 0], 450),
        (&[1, 1, 1, 1, 1, 1], 450),
        (&[0, 0, 0, 0, 1, 1], 9),
        (&[0, 0, 1, 1, 1, 1], 9),
        (&[2, 2, 2, 2, 2, 2], 8),
        (&[0, 0, 1, 1, 2, 2], 9),
        (&[0, 0, 0, 0, 2, 2], 72),
        (&[1, 1, 1, 1, 2, 2], 72),
        (&[0, 0, 2, 2, 2, 2], 18),
        (&[1, 1, 2, 2, 2, 2], 18),
    ];
    let mut moments = BTreeMap::new();
    for (m, value) in entries {
        moments.insert((*m).to_vec(), Q::integer(*value));
    }
    DualWitness {
        half_degree: 3,
        moments,
    }
}
