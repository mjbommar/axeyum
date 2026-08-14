//! Does a geometry *polynomial* mean the geometric predicate it is named after?
//!
//! The cofactor certificate proves an algebraic implication between polynomials.
//! Nothing inside that proof can tell you that `det(B−A, C−A)` is collinearity
//! rather than something else — that link is the **coordinatisation**, and it is
//! the one assumption in this route that no amount of exact arithmetic verifies.
//! It is therefore the thing worth attacking from outside.
//!
//! [`axeyum_cas::geometry`] is a separate, older module that decides the same
//! predicates at concrete rational coordinates, written against lines in
//! `ax + by + c = 0` form and a cross-product helper rather than against
//! [`MvPoly`]. This suite makes the two decide the same questions over a
//! deterministic sweep of integer configurations — including the degenerate ones,
//! where the encodings are most likely to part company — and asserts they always
//! agree.
//!
//! It is a control on the *statement*, not on the proof: a passing run says the
//! polynomials in `artifacts/geometry-certificates/*.json` say what their names
//! claim.

use axeyum_cas::geometry::{Line, Point};
use axeyum_cas::geometry_certify::{
    Pt, collinear, dist_sq, equidistant, midpoint, parallel, perpendicular,
};
use axeyum_cas::mvpoly::MvPoly;
use axeyum_ir::Rational;
use std::collections::BTreeMap;

/// A deterministic sweep of small integer configurations, deliberately including
/// coincident and collinear ones.
fn configurations() -> Vec<[(i128, i128); 4]> {
    let mut out = Vec::new();
    let mut state: u64 = 0xDEAD_BEEF_1234_5678;
    let mut next = |bound: i128| -> i128 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        i128::from((state >> 33) as u32) % (2 * bound + 1) - bound
    };
    // Hand-picked degenerate shapes first.
    out.push([(0, 0), (0, 0), (1, 0), (2, 0)]); // two coincident points
    out.push([(0, 0), (1, 0), (2, 0), (5, 0)]); // four collinear points
    out.push([(0, 0), (0, 1), (0, 2), (0, 3)]); // four collinear, vertical
    out.push([(3, 3), (3, 3), (3, 3), (3, 3)]); // all four coincident
    for _ in 0..240 {
        out.push([
            (next(4), next(4)),
            (next(4), next(4)),
            (next(4), next(4)),
            (next(4), next(4)),
        ]);
    }
    out
}

fn symbolic(points: &[&str]) -> Vec<Pt> {
    points.iter().map(|name| Pt::free(name)).collect()
}

fn bind(config: &[(i128, i128); 4], names: &[&str]) -> BTreeMap<String, Rational> {
    let mut assignment = BTreeMap::new();
    for (index, name) in names.iter().enumerate() {
        assignment.insert(format!("{name}x"), Rational::integer(config[index].0));
        assignment.insert(format!("{name}y"), Rational::integer(config[index].1));
    }
    assignment
}

fn vanishes(poly: &MvPoly, assignment: &BTreeMap<String, Rational>) -> bool {
    poly.evaluate(assignment)
        .expect("small integer configurations never overflow")
        .is_zero()
}

fn concrete(pair: (i128, i128)) -> Point {
    Point::new(Rational::integer(pair.0), Rational::integer(pair.1))
}

const NAMES: [&str; 4] = ["a", "b", "c", "d"];

/// `collinear` is exactly `Point::collinear`.
#[test]
fn the_collinearity_polynomial_agrees_with_the_concrete_predicate() {
    let points = symbolic(&NAMES);
    let poly = collinear(&points[0], &points[1], &points[2]).expect("polynomial");
    let mut checked = 0usize;
    let mut degenerate = 0usize;
    for config in configurations() {
        let assignment = bind(&config, &NAMES);
        let symbolic_says = vanishes(&poly, &assignment);
        let concrete_says = Point::collinear(
            &concrete(config[0]),
            &concrete(config[1]),
            &concrete(config[2]),
        );
        assert_eq!(
            symbolic_says, concrete_says,
            "collinearity disagrees at {config:?}"
        );
        checked += 1;
        if symbolic_says {
            degenerate += 1;
        }
    }
    assert!(checked > 200, "the sweep must actually sweep");
    assert!(
        degenerate > 3,
        "the sweep must include collinear configurations, or only the easy side is tested"
    );
}

/// `parallel` is exactly `Line::is_parallel`, wherever the concrete module can
/// build both lines (it declines on a degenerate two-equal-points "line", which
/// the polynomial encoding handles by vanishing).
#[test]
fn the_parallelism_polynomial_agrees_with_the_concrete_predicate() {
    let points = symbolic(&NAMES);
    let poly = parallel(&points[0], &points[1], &points[2], &points[3]).expect("polynomial");
    let mut compared = 0usize;
    let mut vacuous = 0usize;
    for config in configurations() {
        let assignment = bind(&config, &NAMES);
        let symbolic_says = vanishes(&poly, &assignment);
        let first = Line::through(&concrete(config[0]), &concrete(config[1]));
        let second = Line::through(&concrete(config[2]), &concrete(config[3]));
        if let (Some(first), Some(second)) = (first, second) {
            assert_eq!(
                symbolic_says,
                first.is_parallel(&second),
                "parallelism disagrees at {config:?}"
            );
            compared += 1;
        } else {
            // A degenerate segment: the concrete module refuses to call it a
            // line, and the determinant vanishes because a zero vector is
            // parallel to everything. Record that this is the ONLY way the two
            // can differ, rather than skipping quietly.
            assert!(
                symbolic_says,
                "a degenerate segment must make the determinant vanish at {config:?}"
            );
            vacuous += 1;
        }
    }
    assert!(compared > 200, "the sweep must actually sweep");
    assert!(
        vacuous > 0,
        "the degenerate-segment branch must be exercised"
    );
}

/// `perpendicular` is exactly `Line::is_perpendicular`.
#[test]
fn the_perpendicularity_polynomial_agrees_with_the_concrete_predicate() {
    let points = symbolic(&NAMES);
    let poly = perpendicular(&points[0], &points[1], &points[2], &points[3]).expect("polynomial");
    let mut compared = 0usize;
    let mut orthogonal = 0usize;
    for config in configurations() {
        let assignment = bind(&config, &NAMES);
        let symbolic_says = vanishes(&poly, &assignment);
        let first = Line::through(&concrete(config[0]), &concrete(config[1]));
        let second = Line::through(&concrete(config[2]), &concrete(config[3]));
        if let (Some(first), Some(second)) = (first, second) {
            assert_eq!(
                symbolic_says,
                first.is_perpendicular(&second),
                "perpendicularity disagrees at {config:?}"
            );
            compared += 1;
            if symbolic_says {
                orthogonal += 1;
            }
        } else {
            assert!(
                symbolic_says,
                "a degenerate segment must make the inner product vanish at {config:?}"
            );
        }
    }
    assert!(compared > 200, "the sweep must actually sweep");
    assert!(
        orthogonal > 0,
        "the sweep must include perpendicular configurations"
    );
}

/// The constructed midpoint is exactly `Point::midpoint`.
#[test]
fn the_constructed_midpoint_agrees_with_the_concrete_one() {
    let points = symbolic(&NAMES);
    let m = midpoint(&points[0], &points[1]).expect("midpoint");
    for config in configurations() {
        let assignment = bind(&config, &NAMES);
        let expected = concrete(config[0]).midpoint(&concrete(config[1]));
        assert_eq!(
            m.x.evaluate(&assignment).expect("value"),
            expected.x(),
            "midpoint abscissa disagrees at {config:?}"
        );
        assert_eq!(
            m.y.evaluate(&assignment).expect("value"),
            expected.y(),
            "midpoint ordinate disagrees at {config:?}"
        );
    }
}

/// `equidistant` is exactly equality of the concrete exact distances — which are
/// surds, computed by a completely different route (`simplify_radicals` over
/// `CasExpr`) than the squared-distance polynomial.
#[test]
fn the_equidistance_polynomial_agrees_with_exact_surd_distances() {
    let points = symbolic(&NAMES);
    let poly = equidistant(&points[0], &points[1], &points[2], &points[3]).expect("polynomial");
    let mut equal = 0usize;
    for config in configurations() {
        let assignment = bind(&config, &NAMES);
        let symbolic_says = vanishes(&poly, &assignment);
        let left = concrete(config[0])
            .distance(&concrete(config[1]))
            .expect("distance");
        let right = concrete(config[2])
            .distance(&concrete(config[3]))
            .expect("distance");
        assert_eq!(
            symbolic_says,
            left == right,
            "equidistance disagrees at {config:?}: {left:?} vs {right:?}"
        );
        if symbolic_says {
            equal += 1;
        }
    }
    assert!(
        equal > 0,
        "the sweep must include equidistant configurations"
    );
}

/// `dist_sq` vanishes exactly when the two points coincide. This is the only
/// place the corpus could encode "A ≠ B" as a polynomial condition, and over ℝ
/// (though NOT over ℂ) it is faithful — recorded here as a measurement rather
/// than a remark.
#[test]
fn squared_distance_vanishes_exactly_at_coincident_points() {
    let points = symbolic(&NAMES);
    let poly = dist_sq(&points[0], &points[1]).expect("polynomial");
    let mut coincident = 0usize;
    for config in configurations() {
        let assignment = bind(&config, &NAMES);
        let same = config[0] == config[1];
        assert_eq!(
            vanishes(&poly, &assignment),
            same,
            "squared distance disagrees at {config:?}"
        );
        if same {
            coincident += 1;
        }
    }
    assert!(coincident > 0, "the sweep must include coincident points");
}
