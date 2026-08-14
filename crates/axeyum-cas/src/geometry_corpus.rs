//! The committed corpus of coordinatised Euclidean theorems.
//!
//! Each entry is a [`GeometryProblem`] stated once, here, and consumed by three
//! things that must agree: the emitter that writes
//! `artifacts/geometry-certificates/*.json`, the integration suite that re-checks
//! those files, and the fact ledger rows that cite them.
//!
//! # Reading the corpus
//!
//! The interesting column is **how many non-degeneracy conditions each theorem
//! needs**, and the answer is not what the folklore about mechanised geometry
//! suggests. Stated in the *universal* form — "any point lying on these two
//! objects lies on the third", "any configuration satisfying these equations
//! satisfies that one" — several classical concurrency theorems are outright
//! polynomial identities: the conclusion is in the plain hypothesis ideal, with
//! constant cofactors, and no side condition of any kind. Concurrency of the
//! altitudes is the sharpest example, where the certificate is
//!
//! ```text
//! (P−C)·(B−A) = −(P−A)·(C−B) − (P−B)·(A−C)
//! ```
//!
//! an identity holding for every `P`, `A`, `B`, `C` whatsoever.
//!
//! Non-degeneracy becomes load-bearing exactly when a theorem asserts something
//! about a point the hypotheses are supposed to *pin down*. "The medians meet"
//! needs nothing; "the point where the medians meet is `(A+B+C)/3`" needs the
//! triangle to be non-degenerate, because on a collapsed triangle the hypotheses
//! stop determining the point and the conclusion is false. Both are in this
//! corpus, adjacent, sharing their hypotheses character for character, for
//! exactly that reason.
//!
//! # The counterexamples are part of the corpus
//!
//! Every condition a certificate actually uses carries a [`DegenerateWitness`]:
//! exact rational coordinates satisfying every hypothesis, annihilating the
//! condition, and **falsifying** a conclusion. The checker re-runs them from the
//! artifact, and refuses a certificate whose counterexample fails to break the
//! theorem. A theorem whose side condition cannot be broken did not need it, and
//! the certifier would have proved it without one.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::geometry_certify::{
    Condition, Constraint, DegenerateWitness, GenericWitness, GeometryProblem, Pt, centroid,
    collinear, equidistant, midpoint, parallel, perpendicular,
};
use crate::mvpoly::MvPoly;

/// Gloss rows for the coordinates of the named points.
fn gloss(points: &[(&str, &str)]) -> Vec<(String, String)> {
    let mut rows = Vec::with_capacity(points.len() * 2);
    for (var, label) in points {
        rows.push((format!("{var}x"), format!("{label}.x")));
        rows.push((format!("{var}y"), format!("{label}.y")));
    }
    rows
}

/// A rational assignment from `(variable, numerator, denominator)` triples.
fn at(entries: &[(&str, i128, i128)]) -> BTreeMap<String, Rational> {
    entries
        .iter()
        .map(|(name, numerator, denominator)| {
            ((*name).to_string(), Rational::new(*numerator, *denominator))
        })
        .collect()
}

/// Every theorem this route **reaches**, in a stable order. Each has a committed
/// certificate in `artifacts/geometry-certificates/`.
#[must_use]
pub fn corpus() -> Vec<GeometryProblem> {
    vec![
        varignon(),
        thales(),
        altitudes_concurrent(),
        medians_concurrent(),
        centroid_divides_medians(),
        parallelogram_diagonals_bisect(),
    ]
}

/// Theorems stated here, correctly as far as the encoding goes, that the cofactor
/// route does **not** currently certify.
///
/// They stay in the tree rather than being deleted because the value of a
/// measured limit is that it is reproducible:
/// `cargo run -p axeyum-cas --release --example geometry_probe 1 <id>`
/// re-derives the decline. Measured 2026-08-14 on a loaded 24-core box, release
/// build, budget `geometry_limits`:
///
/// | theorem | conditions | outcome |
/// |---|---|---|
/// | `rhombus-diagonals-perpendicular` | none | 4.6-8.9 s, correctly reports a nonzero remainder |
/// | `rhombus-diagonals-perpendicular` | `abd-not-collinear` | **declined after 247-365 s** |
/// | `euler-line` | none | no verdict within 600 s |
///
/// The shared cause is the cost of `Buchberger`'s algorithm under the pure
/// lexicographic order this crate uses everywhere, compounded by carrying a
/// representation in the generators alongside every intermediate polynomial. The
/// timings vary by a factor of two between an idle and a loaded machine, so treat
/// them as an order of magnitude, not a baseline.
#[must_use]
pub fn frontier() -> Vec<GeometryProblem> {
    vec![rhombus_diagonals_perpendicular(), euler_line()]
}

/// Varignon: the midpoints of the sides of an arbitrary quadrilateral form a
/// parallelogram — in the strong sense that the two midlines are **equal
/// vectors**, not merely parallel.
fn varignon() -> GeometryProblem {
    let corners = [Pt::free("a"), Pt::free("b"), Pt::free("c"), Pt::free("d")];
    let mid_ab = midpoint(&corners[0], &corners[1]).expect("midpoint");
    let mid_bc = midpoint(&corners[1], &corners[2]).expect("midpoint");
    let mid_cd = midpoint(&corners[2], &corners[3]).expect("midpoint");
    let mid_da = midpoint(&corners[3], &corners[0]).expect("midpoint");
    let first_midline = mid_bc.sub(&mid_ab).expect("difference");
    let second_midline = mid_cd.sub(&mid_da).expect("difference");
    GeometryProblem {
        id: "varignon-midpoint-parallelogram".into(),
        title: "Varignon's theorem: the midpoint quadrilateral is a parallelogram".into(),
        statement: "For any four points A, B, C, D of the plane, let P, Q, R, S be the midpoints \
                    of AB, BC, CD, DA. Then the vector from P to Q equals the vector from S to R, \
                    so PQRS is a parallelogram. NO non-degeneracy condition is required: the \
                    conclusion holds for every configuration, including collinear and coincident \
                    ones."
            .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C"), ("d", "D")]),
        hypotheses: Vec::new(),
        nondegeneracy: Vec::new(),
        conclusions: vec![
            Constraint::new(
                "midlines-equal-x",
                "the abscissa of Q-P equals that of R-S",
                first_midline.x.sub(&second_midline.x).expect("difference"),
            ),
            Constraint::new(
                "midlines-equal-y",
                "the ordinate of Q-P equals that of R-S",
                first_midline.y.sub(&second_midline.y).expect("difference"),
            ),
        ],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "a convex quadrilateral (0,0), (4,0), (5,3), (1,2)".into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 4, 1),
                ("by", 0, 1),
                ("cx", 5, 1),
                ("cy", 3, 1),
                ("dx", 1, 1),
                ("dy", 2, 1),
            ]),
        }],
    }
}

/// Thales: an angle inscribed in a semicircle is right.
fn thales() -> GeometryProblem {
    let vertex_a = Pt::free("a");
    let vertex_b = Pt::free("b");
    let vertex_c = Pt::free("c");
    let centre = midpoint(&vertex_a, &vertex_b).expect("midpoint");
    GeometryProblem {
        id: "thales-right-angle-in-semicircle".into(),
        title: "Thales' theorem: an angle in a semicircle is right".into(),
        statement: "Let O be the midpoint of AB and let C satisfy |OC| = |OA|, i.e. C lies on the \
                    circle with diameter AB. Then CA is perpendicular to CB. NO non-degeneracy \
                    condition is required: when A = B the circle degenerates to a point, C \
                    coincides with it, and the conclusion holds because the zero vector is \
                    orthogonal to everything -- the theorem is true ON the degeneracy locus, not \
                    merely off it."
            .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C")]),
        hypotheses: vec![Constraint::new(
            "c-on-circle",
            "|OC| = |OA| with O the midpoint of AB",
            equidistant(&centre, &vertex_c, &centre, &vertex_a).expect("equidistant"),
        )],
        nondegeneracy: Vec::new(),
        conclusions: vec![Constraint::new(
            "angle-acb-right",
            "CA is perpendicular to CB",
            perpendicular(&vertex_c, &vertex_a, &vertex_c, &vertex_b).expect("perpendicular"),
        )],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "the unit semicircle: A = (-1,0), B = (1,0), C = (0,1)".into(),
            assignment: at(&[
                ("ax", -1, 1),
                ("ay", 0, 1),
                ("bx", 1, 1),
                ("by", 0, 1),
                ("cx", 0, 1),
                ("cy", 1, 1),
            ]),
        }],
    }
}

/// The altitudes of a triangle are concurrent (the orthocentre).
fn altitudes_concurrent() -> GeometryProblem {
    let vertex_a = Pt::free("a");
    let vertex_b = Pt::free("b");
    let vertex_c = Pt::free("c");
    let meeting = Pt::free("p");
    GeometryProblem {
        id: "orthocentre-altitudes-concurrent".into(),
        title: "the altitudes of a triangle are concurrent".into(),
        statement: "If AP is perpendicular to BC and BP is perpendicular to CA, then CP is \
                    perpendicular to AB. NO non-degeneracy condition is required: the certificate \
                    has CONSTANT cofactors (-1, -1), so the statement is the polynomial identity \
                    (P-C).(B-A) + (P-A).(C-B) + (P-B).(A-C) = 0, valid for all four points. The \
                    triangle must be non-degenerate for such a P to EXIST and be unique, but that \
                    is an existence claim and this theorem does not make it."
            .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C"), ("p", "P")]),
        hypotheses: vec![
            Constraint::new(
                "ap-perp-bc",
                "AP is perpendicular to BC",
                perpendicular(&vertex_a, &meeting, &vertex_b, &vertex_c).expect("perpendicular"),
            ),
            Constraint::new(
                "bp-perp-ca",
                "BP is perpendicular to CA",
                perpendicular(&vertex_b, &meeting, &vertex_c, &vertex_a).expect("perpendicular"),
            ),
        ],
        nondegeneracy: Vec::new(),
        conclusions: vec![Constraint::new(
            "cp-perp-ab",
            "CP is perpendicular to AB",
            perpendicular(&vertex_c, &meeting, &vertex_a, &vertex_b).expect("perpendicular"),
        )],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "A = (0,0), B = (4,0), C = (1,3), orthocentre P = (1,1)".into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 4, 1),
                ("by", 0, 1),
                ("cx", 1, 1),
                ("cy", 3, 1),
                ("px", 1, 1),
                ("py", 1, 1),
            ]),
        }],
    }
}

/// The two median-incidence hypotheses shared by `medians_concurrent` and
/// `centroid_divides_medians`. Stated once so the two theorems provably differ
/// only in what they conclude.
fn median_hypotheses(vertex_a: &Pt, vertex_b: &Pt, vertex_c: &Pt, meeting: &Pt) -> Vec<Constraint> {
    let mid_bc = midpoint(vertex_b, vertex_c).expect("midpoint");
    let mid_ca = midpoint(vertex_c, vertex_a).expect("midpoint");
    vec![
        Constraint::new(
            "p-on-median-from-a",
            "P is collinear with A and the midpoint of BC",
            collinear(vertex_a, &mid_bc, meeting).expect("collinear"),
        ),
        Constraint::new(
            "p-on-median-from-b",
            "P is collinear with B and the midpoint of CA",
            collinear(vertex_b, &mid_ca, meeting).expect("collinear"),
        ),
    ]
}

/// The medians of a triangle are concurrent.
fn medians_concurrent() -> GeometryProblem {
    let vertex_a = Pt::free("a");
    let vertex_b = Pt::free("b");
    let vertex_c = Pt::free("c");
    let meeting = Pt::free("p");
    let mid_ab = midpoint(&vertex_a, &vertex_b).expect("midpoint");
    GeometryProblem {
        id: "medians-concurrent".into(),
        title: "the medians of a triangle are concurrent".into(),
        statement: "Let Ma, Mb, Mc be the midpoints of BC, CA, AB. If P is collinear with A and \
                    Ma, and collinear with B and Mb, then P is collinear with C and Mc. NO \
                    non-degeneracy condition is required for this incidence form. Compare \
                    `centroid-divides-medians`, which locates P and DOES require one."
            .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C"), ("p", "P")]),
        hypotheses: median_hypotheses(&vertex_a, &vertex_b, &vertex_c, &meeting),
        nondegeneracy: Vec::new(),
        conclusions: vec![Constraint::new(
            "p-on-median-from-c",
            "P is collinear with C and the midpoint of AB",
            collinear(&vertex_c, &mid_ab, &meeting).expect("collinear"),
        )],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "A = (0,0), B = (6,0), C = (0,6), centroid P = (2,2)".into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 6, 1),
                ("by", 0, 1),
                ("cx", 0, 1),
                ("cy", 6, 1),
                ("px", 2, 1),
                ("py", 2, 1),
            ]),
        }],
    }
}

/// The point where the medians meet is `(A+B+C)/3` — the first theorem here that
/// genuinely needs a side condition.
fn centroid_divides_medians() -> GeometryProblem {
    let vertex_a = Pt::free("a");
    let vertex_b = Pt::free("b");
    let vertex_c = Pt::free("c");
    let meeting = Pt::free("p");
    let three = MvPoly::constant(Rational::integer(3));
    let total = vertex_a
        .add(&vertex_b)
        .expect("sum")
        .add(&vertex_c)
        .expect("sum");
    GeometryProblem {
        id: "centroid-divides-medians".into(),
        title: "the medians meet at the centroid (A+B+C)/3".into(),
        statement:
            "If A, B, C are NOT collinear and P lies on the median from A and on the median \
                    from B, then 3P = A + B + C. The non-degeneracy condition is essential and not \
                    cosmetic: on a collapsed triangle the two medians can coincide (or one of the \
                    hypotheses can become vacuous), the hypotheses stop determining P, and the \
                    conclusion is FALSE for most of the P they admit."
                .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C"), ("p", "P")]),
        hypotheses: median_hypotheses(&vertex_a, &vertex_b, &vertex_c, &meeting),
        nondegeneracy: vec![Condition::new(
            "abc-not-collinear",
            "A, B, C are not collinear (the triangle has nonzero area)",
            collinear(&vertex_a, &vertex_b, &vertex_c).expect("collinear"),
        )],
        conclusions: vec![
            Constraint::new(
                "centroid-x",
                "3 P.x = A.x + B.x + C.x",
                three
                    .mul(&meeting.x)
                    .expect("product")
                    .sub(&total.x)
                    .expect("difference"),
            ),
            Constraint::new(
                "centroid-y",
                "3 P.y = A.y + B.y + C.y",
                three
                    .mul(&meeting.y)
                    .expect("product")
                    .sub(&total.y)
                    .expect("difference"),
            ),
        ],
        degenerate_witnesses: vec![DegenerateWitness {
            condition_id: "abc-not-collinear".into(),
            description: "A = (0,0), B = (1,0), C = (2,0) collinear, so B coincides with the \
                          midpoint of CA and the second hypothesis becomes vacuous; P = (7,0) then \
                          satisfies both medians while 3 P.x = 21 and A.x+B.x+C.x = 3"
                .into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 1, 1),
                ("by", 0, 1),
                ("cx", 2, 1),
                ("cy", 0, 1),
                ("px", 7, 1),
                ("py", 0, 1),
            ]),
        }],
        generic_witnesses: vec![GenericWitness {
            description: "A = (0,0), B = (6,0), C = (0,6), centroid P = (2,2)".into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 6, 1),
                ("by", 0, 1),
                ("cx", 0, 1),
                ("cy", 6, 1),
                ("px", 2, 1),
                ("py", 2, 1),
            ]),
        }],
    }
}

/// The two parallelism hypotheses of a parallelogram `ABCD`, shared by
/// `parallelogram_diagonals_bisect` and `rhombus_diagonals_perpendicular`.
fn parallelogram_hypotheses(corners: &[Pt; 4]) -> Vec<Constraint> {
    vec![
        Constraint::new(
            "ab-parallel-dc",
            "AB is parallel to DC",
            parallel(&corners[0], &corners[1], &corners[3], &corners[2]).expect("parallel"),
        ),
        Constraint::new(
            "bc-parallel-ad",
            "BC is parallel to AD",
            parallel(&corners[1], &corners[2], &corners[0], &corners[3]).expect("parallel"),
        ),
    ]
}

/// `A`, `B`, `D` are not collinear — the parallelogram is not flat.
fn not_flat(corners: &[Pt; 4]) -> Condition {
    Condition::new(
        "abd-not-collinear",
        "A, B, D are not collinear (the parallelogram is not flat)",
        collinear(&corners[0], &corners[1], &corners[3]).expect("collinear"),
    )
}

/// The four collinear points `(0,0)`, `(1,0)`, `(2,0)`, `(5,0)` — the shared
/// counterexample for the flat-parallelogram degeneracy.
fn flat_quadrilateral() -> BTreeMap<String, Rational> {
    at(&[
        ("ax", 0, 1),
        ("ay", 0, 1),
        ("bx", 1, 1),
        ("by", 0, 1),
        ("cx", 2, 1),
        ("cy", 0, 1),
        ("dx", 5, 1),
        ("dy", 0, 1),
    ])
}

/// The unit square `(0,0)`, `(1,0)`, `(1,1)`, `(0,1)`.
fn unit_square() -> BTreeMap<String, Rational> {
    at(&[
        ("ax", 0, 1),
        ("ay", 0, 1),
        ("bx", 1, 1),
        ("by", 0, 1),
        ("cx", 1, 1),
        ("cy", 1, 1),
        ("dx", 0, 1),
        ("dy", 1, 1),
    ])
}

/// The diagonals of a parallelogram bisect each other.
fn parallelogram_diagonals_bisect() -> GeometryProblem {
    let corners = [Pt::free("a"), Pt::free("b"), Pt::free("c"), Pt::free("d")];
    let diagonal_ac = midpoint(&corners[0], &corners[2]).expect("midpoint");
    let diagonal_bd = midpoint(&corners[1], &corners[3]).expect("midpoint");
    GeometryProblem {
        id: "parallelogram-diagonals-bisect".into(),
        title: "the diagonals of a parallelogram bisect each other".into(),
        statement: "If AB is parallel to DC, BC is parallel to AD, and A, B, D are NOT collinear, \
                    then the midpoint of AC equals the midpoint of BD. The non-degeneracy \
                    condition is essential: four collinear points satisfy both parallelism \
                    hypotheses vacuously and their diagonals generally do not bisect each other."
            .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C"), ("d", "D")]),
        hypotheses: parallelogram_hypotheses(&corners),
        nondegeneracy: vec![not_flat(&corners)],
        conclusions: vec![
            Constraint::new(
                "diagonal-midpoints-agree-x",
                "the midpoints of AC and BD share an abscissa",
                diagonal_ac.x.sub(&diagonal_bd.x).expect("difference"),
            ),
            Constraint::new(
                "diagonal-midpoints-agree-y",
                "the midpoints of AC and BD share an ordinate",
                diagonal_ac.y.sub(&diagonal_bd.y).expect("difference"),
            ),
        ],
        degenerate_witnesses: vec![DegenerateWitness {
            condition_id: "abd-not-collinear".into(),
            description: "A = (0,0), B = (1,0), C = (2,0), D = (5,0): every direction is parallel \
                          to every other, so both hypotheses hold, but the midpoint of AC is (1,0) \
                          and the midpoint of BD is (3,0)"
                .into(),
            assignment: flat_quadrilateral(),
        }],
        generic_witnesses: vec![GenericWitness {
            description: "the unit square (0,0), (1,0), (1,1), (0,1)".into(),
            assignment: unit_square(),
        }],
    }
}

/// The diagonals of a rhombus are perpendicular. Correctly stated; on the
/// frontier because the reduction declines. See [`frontier`].
fn rhombus_diagonals_perpendicular() -> GeometryProblem {
    let corners = [Pt::free("a"), Pt::free("b"), Pt::free("c"), Pt::free("d")];
    let mut hypotheses = parallelogram_hypotheses(&corners);
    hypotheses.push(Constraint::new(
        "ab-equals-bc",
        "|AB| = |BC|",
        equidistant(&corners[0], &corners[1], &corners[1], &corners[2]).expect("equidistant"),
    ));
    GeometryProblem {
        id: "rhombus-diagonals-perpendicular".into(),
        title: "the diagonals of a rhombus are perpendicular".into(),
        statement: "If AB is parallel to DC, BC is parallel to AD, |AB| = |BC|, and A, B, D are \
                    NOT collinear, then AC is perpendicular to BD. Without the non-degeneracy \
                    condition the statement is false: four collinear points with |AB| = |BC| \
                    satisfy every hypothesis and their diagonals are parallel, not perpendicular."
            .into(),
        coordinate_gloss: gloss(&[("a", "A"), ("b", "B"), ("c", "C"), ("d", "D")]),
        hypotheses,
        nondegeneracy: vec![not_flat(&corners)],
        conclusions: vec![Constraint::new(
            "diagonals-perpendicular",
            "AC is perpendicular to BD",
            perpendicular(&corners[0], &corners[2], &corners[1], &corners[3])
                .expect("perpendicular"),
        )],
        degenerate_witnesses: vec![DegenerateWitness {
            condition_id: "abd-not-collinear".into(),
            description: "A = (0,0), B = (1,0), C = (2,0), D = (5,0): |AB| = |BC| = 1 and both \
                          parallelism hypotheses hold, but AC.BD = (2,0).(4,0) = 8, so the \
                          diagonals are not perpendicular"
                .into(),
            assignment: flat_quadrilateral(),
        }],
        generic_witnesses: vec![GenericWitness {
            description: "the unit square (0,0), (1,0), (1,1), (0,1)".into(),
            assignment: unit_square(),
        }],
    }
}

/// Euler's line: the circumcentre, the centroid and the orthocentre are
/// collinear. Correctly stated; on the frontier because the reduction does not
/// terminate within any budget tried. See [`frontier`].
fn euler_line() -> GeometryProblem {
    let vertex_a = Pt::free("a");
    let vertex_b = Pt::free("b");
    let vertex_c = Pt::free("c");
    let circumcentre = Pt::free("o");
    let orthocentre = Pt::free("h");
    let barycentre = centroid(&vertex_a, &vertex_b, &vertex_c).expect("centroid");
    GeometryProblem {
        id: "euler-line".into(),
        title: "Euler's line: circumcentre, centroid and orthocentre are collinear".into(),
        statement: "Let O satisfy |OA| = |OB| = |OC| (the circumcentre), let H satisfy AH \
                    perpendicular to BC and BH perpendicular to CA (the orthocentre), let \
                    G = (A+B+C)/3 (the centroid), and let A, B, C NOT be collinear. Then O, G and \
                    H are collinear. The non-degeneracy condition is essential: when two vertices \
                    coincide the hypotheses stop determining O and H, and O, G, H are in general a \
                    genuine triangle."
            .into(),
        coordinate_gloss: gloss(&[
            ("a", "A"),
            ("b", "B"),
            ("c", "C"),
            ("o", "O (circumcentre)"),
            ("h", "H (orthocentre)"),
        ]),
        hypotheses: vec![
            Constraint::new(
                "oa-equals-ob",
                "|OA| = |OB|",
                equidistant(&circumcentre, &vertex_a, &circumcentre, &vertex_b)
                    .expect("equidistant"),
            ),
            Constraint::new(
                "ob-equals-oc",
                "|OB| = |OC|",
                equidistant(&circumcentre, &vertex_b, &circumcentre, &vertex_c)
                    .expect("equidistant"),
            ),
            Constraint::new(
                "ah-perp-bc",
                "AH is perpendicular to BC",
                perpendicular(&vertex_a, &orthocentre, &vertex_b, &vertex_c)
                    .expect("perpendicular"),
            ),
            Constraint::new(
                "bh-perp-ca",
                "BH is perpendicular to CA",
                perpendicular(&vertex_b, &orthocentre, &vertex_c, &vertex_a)
                    .expect("perpendicular"),
            ),
        ],
        nondegeneracy: vec![Condition::new(
            "abc-not-collinear",
            "A, B, C are not collinear (the triangle has nonzero area)",
            collinear(&vertex_a, &vertex_b, &vertex_c).expect("collinear"),
        )],
        conclusions: vec![Constraint::new(
            "ogh-collinear",
            "O, G and H are collinear",
            collinear(&circumcentre, &barycentre, &orthocentre).expect("collinear"),
        )],
        degenerate_witnesses: vec![DegenerateWitness {
            condition_id: "abc-not-collinear".into(),
            description: "A = B = (0,0) and C = (1,0): |OA| = |OB| is vacuous so O is only pinned \
                          to the line x = 1/2, and AH perpendicular to BC coincides with BH \
                          perpendicular to CA so H is only pinned to the line x = 0. Taking \
                          O = (1/2,0) and H = (0,1) with G = (1/3,0) gives a triangle, not a line"
                .into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 0, 1),
                ("by", 0, 1),
                ("cx", 1, 1),
                ("cy", 0, 1),
                ("ox", 1, 2),
                ("oy", 0, 1),
                ("hx", 0, 1),
                ("hy", 1, 1),
            ]),
        }],
        generic_witnesses: vec![GenericWitness {
            description: "A = (0,0), B = (4,0), C = (1,3): O = (2,1), H = (1,1), G = (5/3,1)"
                .into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 4, 1),
                ("by", 0, 1),
                ("cx", 1, 1),
                ("cy", 3, 1),
                ("ox", 2, 1),
                ("oy", 1, 1),
                ("hx", 1, 1),
                ("hy", 1, 1),
            ]),
        }],
    }
}

#[cfg(test)]
mod tests {
    use super::{corpus, frontier};
    use crate::geometry_certify::GeometryProblem;
    use std::collections::BTreeSet;

    /// Every stated configuration must be arithmetically consistent with the
    /// polynomials, whether or not the theorem certifies. This is what keeps the
    /// FRONTIER entries honest: a theorem we cannot prove must still be one whose
    /// statement survives its own witnesses.
    fn witnesses_are_consistent(problem: &GeometryProblem) {
        for witness in &problem.generic_witnesses {
            for hypothesis in &problem.hypotheses {
                assert!(
                    hypothesis
                        .poly
                        .evaluate(&witness.assignment)
                        .expect("assigned")
                        .is_zero(),
                    "{}: generic witness violates `{}`",
                    problem.id,
                    hypothesis.id
                );
            }
            for condition in &problem.nondegeneracy {
                assert!(
                    !condition
                        .poly
                        .evaluate(&witness.assignment)
                        .expect("assigned")
                        .is_zero(),
                    "{}: generic witness is degenerate for `{}`",
                    problem.id,
                    condition.id
                );
            }
            for conclusion in &problem.conclusions {
                assert!(
                    conclusion
                        .poly
                        .evaluate(&witness.assignment)
                        .expect("assigned")
                        .is_zero(),
                    "{}: generic witness falsifies `{}`",
                    problem.id,
                    conclusion.id
                );
            }
        }
        for witness in &problem.degenerate_witnesses {
            for hypothesis in &problem.hypotheses {
                assert!(
                    hypothesis
                        .poly
                        .evaluate(&witness.assignment)
                        .expect("assigned")
                        .is_zero(),
                    "{}: degenerate witness violates `{}`",
                    problem.id,
                    hypothesis.id
                );
            }
            let condition = problem
                .nondegeneracy
                .iter()
                .find(|condition| condition.id == witness.condition_id)
                .expect("the witness names a declared condition");
            assert!(
                condition
                    .poly
                    .evaluate(&witness.assignment)
                    .expect("assigned")
                    .is_zero(),
                "{}: degenerate witness does not violate `{}`",
                problem.id,
                condition.id
            );
            assert!(
                problem.conclusions.iter().any(|conclusion| {
                    !conclusion
                        .poly
                        .evaluate(&witness.assignment)
                        .expect("assigned")
                        .is_zero()
                }),
                "{}: degenerate witness for `{}` falsifies nothing, so the condition is not \
                 shown to be needed",
                problem.id,
                witness.condition_id
            );
        }
    }

    #[test]
    fn every_corpus_witness_is_consistent() {
        for problem in corpus() {
            witnesses_are_consistent(&problem);
        }
    }

    /// The frontier entries are unproved, not unchecked.
    #[test]
    fn every_frontier_witness_is_consistent() {
        for problem in frontier() {
            witnesses_are_consistent(&problem);
        }
    }

    #[test]
    fn ids_are_unique_across_the_corpus_and_the_frontier() {
        let mut seen = BTreeSet::new();
        for problem in corpus().into_iter().chain(frontier()) {
            assert!(
                seen.insert(problem.id.clone()),
                "duplicate id {}",
                problem.id
            );
            assert!(
                !problem.conclusions.is_empty(),
                "{}: nothing concluded",
                problem.id
            );
            assert!(
                !problem.generic_witnesses.is_empty(),
                "{}: no sanity configuration",
                problem.id
            );
        }
    }
}
