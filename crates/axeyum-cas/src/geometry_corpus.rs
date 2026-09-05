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

use crate::geometry_beyond::{
    conic_polar_is_tangent_problem, tetrahedron_circumcenter_problem,
    tetrahedron_medians_concurrent_problem,
};
use crate::geometry_certify::{
    Condition, Constraint, DegenerateWitness, GenericWitness, GeometryProblem, Pt, centroid,
    collinear, concyclic, dist_sq, equidistant, midpoint, parallel, perpendicular,
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
        rhombus_diagonals_perpendicular(),
        euler_line(),
        pappus_hexagon(),
        simson_line(),
        // Geometry beyond the rational plane (file 13 item 6):
        // `crate::geometry_beyond` states these, this module only lists them.
        tetrahedron_medians_concurrent_problem(),
        tetrahedron_circumcenter_problem(),
        conic_polar_is_tangent_problem(),
    ]
}

/// Theorems stated here, correctly as far as the encoding goes, that do **not**
/// have a committed certificate.
///
/// Entries stay in the tree rather than being deleted because the value of a
/// measured limit is that it is reproducible, and because a theorem here is
/// **unproved, not unchecked**: `every_frontier_witness_is_consistent` replays
/// every configuration a frontier entry states against its own polynomials, so a
/// mis-stated theorem cannot hide in this list waiting for a faster search.
///
/// `rhombus-diagonals-perpendicular` and `euler-line` left this list on
/// 2026-08-15, and `pappus-hexagon` left it the same day for a reason worth
/// recording, because the entry had said the opposite.
///
/// # What `pappus-hexagon` was doing here, and why it was wrong
///
/// Pappus sat here holding a *checker-verified* certificate — 292 s, three
/// non-degeneracy conditions — blocked not by a budget but by
/// `every_used_condition_set_is_minimal_absolutely`. The note said its three
/// conditions "can only be necessitated as a set": three attempts to find a
/// configuration isolating one had collapsed, each time because killing one
/// intersection forced the two *other* constructed points onto the very line the
/// freed point was confined to.
///
/// Every one of those observations was correct, and the conclusion drawn from
/// them was backwards. Those collapses are not an obstruction to minimality —
/// **they are a proof that each condition is individually redundant.** If, on
/// every configuration where `AF ∩ CD` or `BF ∩ CE` degenerates, the freed point
/// is trapped on the line through the other two, then the conclusion holds
/// *without* those conditions, and the three-element set was never minimal at
/// all. The ratchet was not refusing a claim we had not yet established; it was
/// refusing a claim that is false.
///
/// The corrected statement is stronger and much cleaner: **any one of the three
/// conditions suffices on its own, and none is dispensable jointly** — the empty
/// set does not suffice, since six collinear points make every incidence
/// hypothesis vacuous and leave `X`, `Y`, `Z` free to be a triangle. So this
/// theorem's minimal condition sets are the three singletons, and
/// `certify` now returns one of them.
///
/// Three independent confirmations, in ascending order of strength:
///
/// 1. A synthetic case analysis over the strata where a constructed point is
///    under-determined (a point is free only when its two incidence lines
///    coincide or one is vacuous, and each such collapse forces the other two
///    points onto that same line).
/// 2. An exhaustive decision over `F_p` for `p = 5, 7, 11, 13, 17, 19, 23`
///    (`examples/geometry_condition_subsets.rs`): of the eight possible
///    zero/nonzero patterns of the three conditions, the *only* one admitting a
///    configuration that satisfies every hypothesis and falsifies the conclusion
///    is the one with all three zero.
/// 3. The certificate itself, which is the decisive one — see below.
///
/// # Why the route reported three conditions, which is the transferable lesson
///
/// Not a budget. The block detector always found all three intersection blocks,
/// so the multiplier was always `c₁·c₂·c₃`, so every proper subset failed at
/// `invert_multiplier` on [`crate::geometry_certify::GeometryDecline::UndividableMultiplier`].
/// The route was reporting the smallest subset **its own decomposition could pay
/// for**, which is a property of the producer, not of the theorem.
///
/// `licensed_blocks` fixes it by filtering the decomposition to the blocks the
/// current subset licenses. With the one-condition subset, one block is kept, the
/// residue is 48 terms of degree 4 over the six untouched hypotheses, and
/// [`crate::cofactor_ansatz`] settles it in ~25 ms with every coefficient `±1`.
/// Buchberger was killed on that same residue after **7.5 minutes** without returning, which is why
/// the bounded-degree route is tried first.
///
/// Measured 2026-08-15,
/// `cargo run -p axeyum-cas --release --example geometry_linear_route -- pappus-hexagon`:
///
/// ```text
/// CERTIFIED in 6.7 ms  conditions=["ae-meets-bd"]  74 cofactor terms  checker=verified
/// ```
///
/// 292 s and three conditions became 6.7 ms and one, and the one is minimal
/// **absolutely** in ADR-0455's sense: the only proper subset of a singleton is
/// the empty set, and the committed degenerate counterexample refutes it outright
/// with no budget anywhere in the argument.
///
/// # What the previous note said was next, and how it turned out
///
/// This note used to end by naming **Simson's line** and its wrinkle: `|BC|² ≠ 0`
/// is *not* `B ≠ C` over an arbitrary field of characteristic zero, because of
/// the isotropic directions over ℂ, while over ℚ the two coincide — so the
/// configurations that would witness the necessity of `|BC|² ≠ 0` are not
/// rational, and [`DegenerateWitness`] held exact rationals.
///
/// Every word of that is right, and the conclusion drawn from it — that the
/// witness could not be stated — was a statement about the *type*, not about the
/// mathematics. [`DegenerateWitness`] now carries an optional imaginary part, the
/// witnesses exist, and `simson_line` is in [`corpus`] with all three isotropy
/// conditions, minimal over characteristic zero and each necessitated at an exact
/// `ℚ(i)` point. The real-plane picture is the *opposite* one and is recorded
/// beside it: over ℝ any single condition suffices, exactly as
/// `pappus_hexagon`'s did.
///
/// The transferable part is not about geometry. **When a search for a
/// counterexample keeps failing, check whether one is even expressible in the type
/// you are searching over before concluding anything from the failure.** Here the
/// search was not failing; it was not being run.
pub fn frontier() -> Vec<GeometryProblem> {
    Vec::new()
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
            imaginary: BTreeMap::new(),
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
            imaginary: BTreeMap::new(),
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

/// The diagonals of a rhombus are perpendicular — the corpus's first genuinely
/// **quadratic** hypothesis system, and the theorem that the monomial-order switch
/// moved off the frontier.
///
/// It differs from `parallelogram_diagonals_bisect` by exactly one hypothesis, the
/// quadratic `|AB| = |BC|`, and that one generator is the difference between a
/// 72 ms reduction and a 21 s one. Under `lex` it was not a difference of degree
/// but of outcome: 287.8 s and then the `ReductionSteps` ceiling.
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
            imaginary: BTreeMap::new(),
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
/// collinear.
///
/// The theorem this corpus reached by changing *algorithm* rather than budget.
/// Every hypothesis is affine in the four unknown coordinates `ox, oy, hx, hy`,
/// which is why
/// [`crate::geometry_certify::certify_by_linear_elimination`] settles it in
/// milliseconds where the Gröbner search diverges — see [`frontier`].
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
            imaginary: BTreeMap::new(),
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

/// The eight incidence hypotheses of Pappus, split out so the problem itself
/// stays readable: two "these three are collinear" for the carrier lines, then
/// two per intersection point.
fn pappus_hypotheses(first: &[Pt; 3], second: &[Pt; 3], crosses: &[Pt; 3]) -> Vec<Constraint> {
    let [vertex_a, vertex_b, vertex_c] = first;
    let [vertex_d, vertex_e, vertex_f] = second;
    let [cross_x, cross_y, cross_z] = crosses;
    vec![
        Constraint::new(
            "abc-collinear",
            "A, B, C lie on one line",
            collinear(vertex_a, vertex_b, vertex_c).expect("collinear"),
        ),
        Constraint::new(
            "def-collinear",
            "D, E, F lie on one line",
            collinear(vertex_d, vertex_e, vertex_f).expect("collinear"),
        ),
        Constraint::new(
            "x-on-ae",
            "X lies on the line AE",
            collinear(vertex_a, vertex_e, cross_x).expect("collinear"),
        ),
        Constraint::new(
            "x-on-bd",
            "X lies on the line BD",
            collinear(vertex_b, vertex_d, cross_x).expect("collinear"),
        ),
        Constraint::new(
            "y-on-af",
            "Y lies on the line AF",
            collinear(vertex_a, vertex_f, cross_y).expect("collinear"),
        ),
        Constraint::new(
            "y-on-cd",
            "Y lies on the line CD",
            collinear(vertex_c, vertex_d, cross_y).expect("collinear"),
        ),
        Constraint::new(
            "z-on-bf",
            "Z lies on the line BF",
            collinear(vertex_b, vertex_f, cross_z).expect("collinear"),
        ),
        Constraint::new(
            "z-on-ce",
            "Z lies on the line CE",
            collinear(vertex_c, vertex_e, cross_z).expect("collinear"),
        ),
    ]
}

/// The three non-degeneracy conditions of Pappus: each says one pair of lines
/// actually meets, and each is *exactly* the determinant of the 2x2 block that
/// pins the corresponding intersection point.
fn pappus_conditions(first: &[Pt; 3], second: &[Pt; 3]) -> Vec<Condition> {
    let [vertex_a, vertex_b, vertex_c] = first;
    let [vertex_d, vertex_e, vertex_f] = second;
    vec![
        Condition::new(
            "ae-meets-bd",
            "AE is not parallel to BD",
            parallel(vertex_a, vertex_e, vertex_b, vertex_d).expect("parallel"),
        ),
        Condition::new(
            "af-meets-cd",
            "AF is not parallel to CD",
            parallel(vertex_a, vertex_f, vertex_c, vertex_d).expect("parallel"),
        ),
        Condition::new(
            "bf-meets-ce",
            "BF is not parallel to CE",
            parallel(vertex_b, vertex_f, vertex_c, vertex_e).expect("parallel"),
        ),
    ]
}

/// Pappus's hexagon theorem: if `A, B, C` lie on one line and `D, E, F` on
/// another, the three "cross" intersections `X = AE ∩ BD`, `Y = AF ∩ CD` and
/// `Z = BF ∩ CE` are collinear.
///
/// Eighteen coordinates and eight hypotheses, six of which are linear in the
/// three intersection points — three 2×2 blocks whose determinants are exactly
/// the three "these two lines are not parallel" conditions.
///
/// # One condition, not three
///
/// All three conditions are *stated*, because all three are the honest reading of
/// the construction: each says the pair of lines defining one cross point
/// actually meets. Only one of them is *used*, and that is the theorem's real
/// content rather than an accident of the search.
///
/// The reason is worth stating because it took a wrong answer to find. The
/// incidence hypotheses assert that `X`, `Y`, `Z` **exist** as points on their
/// respective line pairs. So a configuration on which, say, `AF ∩ CD` degenerates
/// is not one where `Y` is missing — it is one where `Y` is *under-determined*,
/// free along a line. And every way that can happen (the two lines coincide, or
/// one of them is vacuous because its two defining points collide) drags `X` and
/// `Z` onto that very line, so the conclusion holds anyway. The condition is
/// carrying no weight. The same argument applies to each condition separately,
/// but not to all of them at once: with the whole configuration collapsed onto a
/// single line, every hypothesis is vacuous and the conclusion is plainly false,
/// which is exactly what [`degenerate_pappus`] exhibits.
///
/// So the minimal condition sets are the three singletons, `certify` returns the
/// first of them, and that minimality is **absolute** — the only proper subset of
/// a singleton is the empty one, and the committed counterexample refutes it with
/// no budget in the argument. See [`frontier`] for the measurement history and
/// for why the route reported three conditions before `licensed_blocks` existed.
fn pappus_hexagon() -> GeometryProblem {
    let on_first = [Pt::free("a"), Pt::free("b"), Pt::free("c")];
    let on_second = [Pt::free("d"), Pt::free("e"), Pt::free("f")];
    let crosses = [Pt::free("x"), Pt::free("y"), Pt::free("z")];
    let [cross_x, cross_y, cross_z] = &crosses;
    GeometryProblem {
        id: "pappus-hexagon".into(),
        title: "Pappus's hexagon theorem: the three cross intersections are collinear".into(),
        statement: "Let A, B, C be collinear and D, E, F be collinear. Let X lie on AE and on \
                    BD, Y on AF and on CD, and Z on BF and on CE. If AE is not parallel to BD, \
                    then X, Y and Z are collinear. ONE condition is enough, and it is needed: \
                    the other two stated conditions are individually redundant (by symmetry \
                    either of them would serve equally as the single condition), while with no \
                    condition at all the theorem is false -- six collinear points make every \
                    incidence hypothesis vacuous and leave X, Y, Z free to be a triangle."
            .into(),
        coordinate_gloss: gloss(&[
            ("a", "A"),
            ("b", "B"),
            ("c", "C"),
            ("d", "D"),
            ("e", "E"),
            ("f", "F"),
            ("x", "X (AE meet BD)"),
            ("y", "Y (AF meet CD)"),
            ("z", "Z (BF meet CE)"),
        ]),
        hypotheses: pappus_hypotheses(&on_first, &on_second, &crosses),
        nondegeneracy: pappus_conditions(&on_first, &on_second),
        conclusions: vec![Constraint::new(
            "xyz-collinear",
            "X, Y and Z are collinear",
            collinear(cross_x, cross_y, cross_z).expect("collinear"),
        )],
        degenerate_witnesses: vec![
            degenerate_pappus("ae-meets-bd"),
            degenerate_pappus("af-meets-cd"),
            degenerate_pappus("bf-meets-ce"),
        ],
        generic_witnesses: vec![GenericWitness {
            description: "A=(0,0), B=(1,0), C=(3,0) on the x-axis; D=(0,2), E=(2,3), F=(4,4) on \
                          a second line; X=(4/7,6/7), Y=(6/5,6/5), Z=(31/13,24/13)"
                .into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 1, 1),
                ("by", 0, 1),
                ("cx", 3, 1),
                ("cy", 0, 1),
                ("dx", 0, 1),
                ("dy", 2, 1),
                ("ex", 2, 1),
                ("ey", 3, 1),
                ("fx", 4, 1),
                ("fy", 4, 1),
                ("xx", 4, 7),
                ("xy", 6, 7),
                ("yx", 6, 5),
                ("yy", 6, 5),
                ("zx", 31, 13),
                ("zy", 24, 13),
            ]),
        }],
    }
}

/// The seven hypotheses of Simson's line: one concyclicity, then two per foot.
///
/// Each foot is stated by the pair "lies on the side line" and "the segment from
/// `P` is perpendicular to that side line". Both are **linear** in the foot's two
/// coordinates, so each foot is a 2x2 block, and the block's determinant is
/// `−|BC|²` (respectively `−|CA|²`, `−|AB|²`) — the very polynomials named as the
/// non-degeneracy conditions.
fn simson_hypotheses(
    vertex_a: &Pt,
    vertex_b: &Pt,
    vertex_c: &Pt,
    point_p: &Pt,
    feet: &[Pt; 3],
) -> Vec<Constraint> {
    let [foot_x, foot_y, foot_z] = feet;
    vec![
        Constraint::new(
            "abcp-concyclic",
            "A, B, C, P lie on a common circle or line",
            concyclic(vertex_a, vertex_b, vertex_c, point_p).expect("concyclic"),
        ),
        Constraint::new(
            "x-on-bc",
            "X lies on the line BC",
            collinear(vertex_b, vertex_c, foot_x).expect("collinear"),
        ),
        Constraint::new(
            "px-perp-bc",
            "PX is perpendicular to BC",
            perpendicular(point_p, foot_x, vertex_b, vertex_c).expect("perpendicular"),
        ),
        Constraint::new(
            "y-on-ca",
            "Y lies on the line CA",
            collinear(vertex_c, vertex_a, foot_y).expect("collinear"),
        ),
        Constraint::new(
            "py-perp-ca",
            "PY is perpendicular to CA",
            perpendicular(point_p, foot_y, vertex_c, vertex_a).expect("perpendicular"),
        ),
        Constraint::new(
            "z-on-ab",
            "Z lies on the line AB",
            collinear(vertex_a, vertex_b, foot_z).expect("collinear"),
        ),
        Constraint::new(
            "pz-perp-ab",
            "PZ is perpendicular to AB",
            perpendicular(point_p, foot_z, vertex_a, vertex_b).expect("perpendicular"),
        ),
    ]
}

/// The three non-degeneracy conditions of Simson's line, each the determinant of
/// one foot's 2x2 block up to sign.
///
/// `|BC|² ≠ 0` is **not** `B ≠ C` in general — over an algebraically closed field
/// the quadratic form `x² + y²` has the isotropic directions `(1, ±i)`, so a
/// nonzero vector can have zero square length. Over ℝ the two readings coincide,
/// and the ids and descriptions here name the algebra rather than the real-plane
/// gloss so that the difference stays visible in the artifact.
fn simson_conditions(vertex_a: &Pt, vertex_b: &Pt, vertex_c: &Pt) -> Vec<Condition> {
    vec![
        Condition::new(
            "bc-nonisotropic",
            "|BC|^2 is nonzero (over the reals: B and C are distinct)",
            dist_sq(vertex_b, vertex_c).expect("squared distance"),
        ),
        Condition::new(
            "ca-nonisotropic",
            "|CA|^2 is nonzero (over the reals: C and A are distinct)",
            dist_sq(vertex_c, vertex_a).expect("squared distance"),
        ),
        Condition::new(
            "ab-nonisotropic",
            "|AB|^2 is nonzero (over the reals: A and B are distinct)",
            dist_sq(vertex_a, vertex_b).expect("squared distance"),
        ),
    ]
}

/// Simson's line (Wallace, 1799): if `P` is concyclic with `A`, `B`, `C`, the
/// feet of the perpendiculars from `P` to the three side lines are collinear.
///
/// Fourteen coordinates and seven hypotheses. The circle is stated as a
/// [`concyclic`] determinant rather than through a centre, so `P ∈ Γ` costs no
/// centre variable, no radius variable, and no extra hypothesis.
///
/// # Three conditions, and the number depends on the FIELD, not on the budget
///
/// This is the first theorem in the corpus whose minimal condition set is
/// different over `ℝ` and over `ℂ`, and it is the theorem that forced the ledger
/// to say which one it means.
///
/// Over `ℝ` **one** condition suffices. `|BC|² = 0` is `B = C`, which makes lines
/// `CA` and `AB` the same line and hence `Y = Z`, and three points two of which
/// coincide are collinear whatever the third does. So the conclusion survives
/// every single collapse and fails only when all three vertices coincide — which
/// annihilates all three conditions at once. The same shape as
/// [`pappus_hexagon`], and by the same reasoning the minimal real sets would be
/// the three singletons.
///
/// Over `ℂ` **three** are needed, and the certificate is a statement about `ℂ`.
/// A cofactor identity with rational coefficients holds in every `ℚ`-algebra, so
/// what a certificate proves is a theorem of every field of characteristic zero;
/// it is not, and cannot be made, a statement about the real plane specifically.
/// There `|BC|² = 0` no longer implies `B = C` — `x² + y²` has the isotropic
/// directions `(1, ±i)` — so a single side can be a genuine line perpendicular to
/// itself, its foot floats free along it, the other two feet stay pinned, and the
/// conclusion fails. [`isotropic_simson`] exhibits exactly that, once per
/// condition, at exact `ℚ(i)` points.
///
/// So the condition set here is minimal **absolutely** in ADR-0455's sense and
/// independent of the producer's decomposition in ADR-0460's: every one of the
/// seven proper subsets is refuted by a committed configuration, with no budget,
/// no monomial order and no algorithm in the argument. What the reader must not
/// do is read that minimality as a claim about the real plane. Over `ℝ` two of
/// these three conditions are redundant, and the ledger says so out loud rather
/// than letting a `ℂ`-minimal set be quoted as an `ℝ`-minimal one.
///
/// Both halves are the literature's, not this lane's: Chou and Gao's CADE-11
/// paper uses *this theorem* as its motivating example of a statement that Wu's
/// method and Gröbner bases cannot confirm under `¬collinear(A,B,C)` alone, and
/// introduces `¬isotropic` on each side to fix it; Harrison's textbook run on
/// Simson notes that the squared-length conditions are redundant over `ℝ` and are
/// not over `ℂ`. What is new here is that both directions are *witnessed* rather
/// than asserted.
fn simson_line() -> GeometryProblem {
    let vertex_a = Pt::free("a");
    let vertex_b = Pt::free("b");
    let vertex_c = Pt::free("c");
    let point_p = Pt::free("p");
    let feet = [Pt::free("x"), Pt::free("y"), Pt::free("z")];
    let [foot_x, foot_y, foot_z] = &feet;
    GeometryProblem {
        id: "simson-line".into(),
        title: "Simson's line: the feet of the perpendiculars from a concyclic point are collinear"
            .into(),
        statement: "Let A, B, C, P satisfy the concyclicity determinant (they lie on a common \
                    circle or line). Let X lie on BC with PX perpendicular to BC, Y on CA with PY \
                    perpendicular to CA, and Z on AB with PZ perpendicular to AB. If |BC|^2, \
                    |CA|^2 and |AB|^2 are all nonzero, then X, Y and Z are collinear. Over the \
                    real plane those three conditions say exactly that A, B, C are pairwise \
                    distinct, so this is Simson's theorem in its classical form. All three are \
                    needed and the set is minimal, but that minimality is a statement about \
                    characteristic zero rather than about the real plane: over an algebraically \
                    closed field |BC|^2 = 0 does NOT imply B = C, because x^2 + y^2 has the \
                    isotropic directions (1, +-i), and a side line perpendicular to itself leaves \
                    its foot free while the other two stay pinned. Each condition's necessity is \
                    exhibited at exact Q(i) points. Over the REALS two of the three are \
                    redundant -- B = C forces lines CA and AB to coincide, so Y = Z and the three \
                    feet are collinear whatever X does -- and only the total collapse A = B = C \
                    breaks the theorem there, which the fourth committed configuration exhibits \
                    over Q."
            .into(),
        coordinate_gloss: gloss(&[
            ("a", "A"),
            ("b", "B"),
            ("c", "C"),
            ("p", "P (on the circle ABC)"),
            ("x", "X (foot on BC)"),
            ("y", "Y (foot on CA)"),
            ("z", "Z (foot on AB)"),
        ]),
        hypotheses: simson_hypotheses(&vertex_a, &vertex_b, &vertex_c, &point_p, &feet),
        nondegeneracy: simson_conditions(&vertex_a, &vertex_b, &vertex_c),
        conclusions: vec![Constraint::new(
            "xyz-collinear",
            "X, Y and Z are collinear (the Simson line)",
            collinear(foot_x, foot_y, foot_z).expect("collinear"),
        )],
        degenerate_witnesses: vec![
            // One isotropic witness per condition, and they are the SAME four
            // points relabelled: the theorem is symmetric under a cyclic
            // relabelling of the vertices, which carries the feet along with it,
            // so a single configuration establishes all three necessities.
            isotropic_simson(
                "bc-nonisotropic",
                "|BC|^2 = 0 at B != C: A=(1,0), B=(0,0), C=(1,i), P=(-i,1) all lie on the circle \
                 -(x^2+y^2) + x + i*y = 0. BC is isotropic, so X is unpinned and free along it \
                 (both of its hypotheses hold identically); Y=(1,1) on CA and Z=(-i,0) on AB stay \
                 pinned, and X=(0,0) leaves X, Y, Z a triangle. Over the reals no such \
                 configuration exists, which is the whole point of the witness",
                [(1, 0), (0, 0), (1, 0), (0, 1), (0, 0), (1, 1), (0, 0)],
                [(0, 0), (0, 0), (0, 1), (-1, 0), (0, 0), (0, 0), (-1, 0)],
            ),
            isotropic_simson(
                "ca-nonisotropic",
                "|CA|^2 = 0 at C != A: A=(1,i), B=(1,0), C=(0,0), P=(-i,1) all lie on the circle \
                 -(x^2+y^2) + x + i*y = 0. CA is isotropic, so Y is unpinned and free along it; \
                 X=(-i,0) on BC and Z=(1,1) on AB stay pinned, and Y=(0,0) leaves X, Y, Z a \
                 triangle",
                [(1, 0), (1, 0), (0, 0), (0, 1), (0, 0), (0, 0), (1, 1)],
                [(0, 1), (0, 0), (0, 0), (-1, 0), (-1, 0), (0, 0), (0, 0)],
            ),
            isotropic_simson(
                "ab-nonisotropic",
                "|AB|^2 = 0 at A != B: A=(0,0), B=(1,i), C=(1,0), P=(-i,1) all lie on the circle \
                 -(x^2+y^2) + x + i*y = 0. AB is isotropic, so Z is unpinned and free along it; \
                 X=(1,1) on BC and Y=(-i,0) on CA stay pinned, and Z=(0,0) leaves X, Y, Z a \
                 triangle",
                [(0, 0), (1, 0), (1, 0), (0, 1), (1, 1), (0, 0), (0, 0)],
                [(0, 0), (0, 1), (0, 0), (-1, 0), (0, 0), (-1, 0), (0, 0)],
            ),
            // The rational one, kept because it says something the three above do
            // not: over the REAL plane the theorem still needs a condition, and
            // the total collapse A = B = C is what breaks it there.
            degenerate_simson("bc-nonisotropic"),
        ],
        generic_witnesses: vec![GenericWitness {
            description: "A=(5,0), B=(0,5), C=(-3,4), P=(4,-3) on x^2+y^2=25; feet X=(6/5,27/5), \
                          Y=(27/5,-1/5), Z=(6,-1), which lie on the line 4x + 3y = 21"
                .into(),
            assignment: at(&[
                ("ax", 5, 1),
                ("ay", 0, 1),
                ("bx", 0, 1),
                ("by", 5, 1),
                ("cx", -3, 1),
                ("cy", 4, 1),
                ("px", 4, 1),
                ("py", -3, 1),
                ("xx", 6, 5),
                ("xy", 27, 5),
                ("yx", 27, 5),
                ("yy", -1, 5),
                ("zx", 6, 1),
                ("zy", -1, 1),
            ]),
        }],
    }
}

/// A `ℚ(i)` counterexample for one of Simson's three isotropy conditions.
///
/// `real` and `imaginary` give the `(x, y)` coordinates of `A`, `B`, `C`, `P`,
/// `X`, `Y`, `Z` in that order, so a point is `real[k].0 + i·imaginary[k].0` by
/// `real[k].1 + i·imaginary[k].1`.
///
/// # Why these cannot be rational
///
/// Over `ℝ` the theorem needs only *one* of the three conditions, because
/// `|BC|² = 0` forces `B = C`, which makes lines `CA` and `AB` the same line and
/// hence `Y = Z` — and three points two of which coincide are collinear whatever
/// the third does. So over `ℝ` a configuration isolating a single condition does
/// not exist, and the failure to find one is a theorem rather than a gap.
///
/// Over a field containing `i` it does exist, because `x² + y²` acquires the
/// isotropic directions `(1, ±i)` and `|BC|² = 0` no longer implies `B = C`. The
/// side line is then a genuine line perpendicular to itself, its foot's 2x2 block
/// is singular with the two hypotheses *consistent* rather than contradictory, and
/// that foot ranges over a whole line while the other two stay pinned. The
/// conclusion is affine in the free foot, so it fails somewhere.
///
/// This is the textbook obstruction rather than a local discovery: Chou and Gao
/// state Simson's theorem as their motivating example of a statement that cannot
/// be confirmed under `¬collinear(A,B,C)` alone and needs `¬isotropic` on each
/// side, and Harrison's run of Wu's method on Simson notes in as many words that
/// the squared-length conditions are redundant over `ℝ` and are not over `ℂ`.
/// What is added here is the *witness*: the redundancy and the necessity are
/// exhibited at exact points rather than asserted, on both sides of the field
/// question.
fn isotropic_simson(
    condition_id: &str,
    description: &str,
    real: [(i128, i128); 7],
    imaginary: [(i128, i128); 7],
) -> DegenerateWitness {
    const POINTS: [&str; 7] = ["a", "b", "c", "p", "x", "y", "z"];
    let spread = |values: [(i128, i128); 7]| -> BTreeMap<String, Rational> {
        POINTS
            .iter()
            .zip(values)
            .flat_map(|(name, (abscissa, ordinate))| {
                [
                    (format!("{name}x"), Rational::integer(abscissa)),
                    (format!("{name}y"), Rational::integer(ordinate)),
                ]
            })
            .collect()
    };
    DegenerateWitness {
        condition_id: condition_id.to_string(),
        description: description.to_string(),
        assignment: spread(real),
        imaginary: spread(imaginary),
    }
}

/// The one configuration that breaks Simson: `A = B = C = (0,0)` with `P = (1,0)`.
///
/// Every side line degenerates at once, so all six foot hypotheses are vacuous
/// (`collinear` and `perpendicular` both contract a zero direction vector) and the
/// concyclicity determinant has three equal rows. `X = (0,1)`, `Y = (2,0)`,
/// `Z = (4,0)` is then a genuine triangle.
///
/// It is offered for each of the three conditions because it annihilates each of
/// them, and one copy survives into the certificate: [`certify`] uses a single
/// condition, so `assemble` filters the list down to that one witness.
///
/// No configuration isolating a *single* condition exists **over ℝ**, and that is
/// a theorem rather than a gap — it is exactly why the other two conditions are
/// redundant. See [`simson_line`].
///
/// [`certify`]: crate::geometry_certify::certify
fn degenerate_simson(condition_id: &str) -> DegenerateWitness {
    DegenerateWitness {
        imaginary: BTreeMap::new(),
        condition_id: condition_id.to_string(),
        description: "A = B = C = (0,0) with P = (1,0): all three side lines collapse, so every \
                      foot hypothesis is vacuous and the concyclicity determinant has three equal \
                      rows; X=(0,1), Y=(2,0), Z=(4,0) is a triangle"
            .into(),
        assignment: at(&[
            ("ax", 0, 1),
            ("ay", 0, 1),
            ("bx", 0, 1),
            ("by", 0, 1),
            ("cx", 0, 1),
            ("cy", 0, 1),
            ("px", 1, 1),
            ("py", 0, 1),
            ("xx", 0, 1),
            ("xy", 1, 1),
            ("yx", 2, 1),
            ("yy", 0, 1),
            ("zx", 4, 1),
            ("zy", 0, 1),
        ]),
    }
}

/// The one configuration that breaks Pappus: `A=(0,0)`, `B=(1,0)`, `C=(3,0)`,
/// `D=(1,0)`, `E=(0,0)`, `F=(5,0)` — six points on the x-axis, so every
/// incidence hypothesis holds vacuously and all three conditions vanish, while
/// `X=(0,1)`, `Y=(2,0)`, `Z=(4,0)` is a genuine triangle.
///
/// It is offered for each of the three conditions because it annihilates each of
/// them, and one copy of it is all the certificate keeps: [`certify`] uses a
/// single condition, so `assemble` filters the list down to that one witness.
///
/// No configuration isolating a *single* condition exists, and that is a theorem
/// rather than a gap — it is precisely why the other two conditions are
/// redundant. See [`pappus_hexagon`].
///
/// [`certify`]: crate::geometry_certify::certify
fn degenerate_pappus(condition_id: &str) -> DegenerateWitness {
    DegenerateWitness {
        imaginary: BTreeMap::new(),
        condition_id: condition_id.to_string(),
        description: "all six points on the x-axis (D=B and E=A), so every incidence hypothesis \
                      is vacuous and X, Y, Z are unconstrained; X=(0,1), Y=(2,0), Z=(4,0) is a \
                      triangle"
            .into(),
        assignment: at(&[
            ("ax", 0, 1),
            ("ay", 0, 1),
            ("bx", 1, 1),
            ("by", 0, 1),
            ("cx", 3, 1),
            ("cy", 0, 1),
            ("dx", 1, 1),
            ("dy", 0, 1),
            ("ex", 0, 1),
            ("ey", 0, 1),
            ("fx", 5, 1),
            ("fy", 0, 1),
            ("xx", 0, 1),
            ("xy", 1, 1),
            ("yx", 2, 1),
            ("yy", 0, 1),
            ("zx", 4, 1),
            ("zy", 0, 1),
        ]),
    }
}

#[cfg(test)]
mod tests {
    use super::{MvPoly, corpus, euler_line, frontier};
    use crate::geometry_certify::{GeometryProblem, evaluate_gaussian};
    use axeyum_ir::Rational;
    use std::collections::{BTreeMap, BTreeSet};

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
            // Over `ℚ(i)`: a rational witness embeds with a zero imaginary part
            // and is decided by the same arithmetic as before, while
            // `simson-line`'s isotropic witnesses need the extension to exist at
            // all. Evaluating them over `ℚ` alone would silently drop the
            // imaginary part and confirm a DIFFERENT configuration.
            let point = witness.point().expect("the witness is a well-formed point");
            for hypothesis in &problem.hypotheses {
                assert!(
                    evaluate_gaussian(&hypothesis.poly, &point)
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
                evaluate_gaussian(&condition.poly, &point)
                    .expect("assigned")
                    .is_zero(),
                "{}: degenerate witness does not violate `{}`",
                problem.id,
                condition.id
            );
            assert!(
                problem.conclusions.iter().any(|conclusion| {
                    !evaluate_gaussian(&conclusion.poly, &point)
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

    /// The three isotropic witnesses do the job no rational configuration can:
    /// each keeps the OTHER two conditions nonzero while killing its own.
    ///
    /// This is the assertion that makes `simson-line`'s three-condition set
    /// minimal rather than merely reported, and it is stated separately from
    /// `witnesses_are_consistent` because that test only asks a witness to break
    /// the condition it names. A witness that also killed its neighbours would
    /// pass there and would establish nothing about minimality — which is exactly
    /// the shape of `pappus-hexagon`'s wrong three-condition answer.
    #[test]
    fn each_simson_isotropy_condition_is_necessary_over_the_gaussian_rationals() {
        let problem = corpus()
            .into_iter()
            .find(|problem| problem.id == "simson-line")
            .expect("simson-line is in the corpus");
        let mut isolated = 0usize;
        for witness in &problem.degenerate_witnesses {
            if !witness.is_gaussian() {
                continue;
            }
            let point = witness.point().expect("a well-formed point");
            for condition in &problem.nondegeneracy {
                let value = evaluate_gaussian(&condition.poly, &point).expect("assigned");
                let expected_zero = condition.id == witness.condition_id;
                assert_eq!(
                    value.is_zero(),
                    expected_zero,
                    "{}: the witness for `{}` must annihilate that condition and NO other, but \
                     `{}` came out {}",
                    problem.id,
                    witness.condition_id,
                    condition.id,
                    if value.is_zero() { "zero" } else { "nonzero" }
                );
            }
            isolated += 1;
        }
        assert_eq!(
            isolated,
            problem.nondegeneracy.len(),
            "every condition needs its own isolating witness, or the set is not shown minimal"
        );
    }

    #[test]
    fn every_corpus_witness_is_consistent() {
        for problem in corpus() {
            witnesses_are_consistent(&problem);
        }
    }

    /// The frontier entries are unproved, not unchecked.
    ///
    /// The list is empty as of 2026-08-15 — `euler-line` was the last entry and
    /// the linear-elimination route reached it — so this currently examines
    /// nothing. That is stated rather than hidden: a suite that silently
    /// exercises zero cases reads exactly like a passing one, and this repository
    /// has shipped several gates with that property. The assertion below fires the
    /// moment a frontier entry exists again, which is when it starts mattering.
    #[test]
    fn every_frontier_witness_is_consistent() {
        let entries = frontier();
        for problem in &entries {
            witnesses_are_consistent(problem);
        }
        assert!(
            entries.is_empty()
                || entries
                    .iter()
                    .all(|problem| !problem.conclusions.is_empty()),
            "a frontier entry that concludes nothing cannot be checked"
        );
    }

    /// `euler-line` holds at circumcentres and orthocentres constructed
    /// **independently of the certifier**, by Cramer's rule over the rationals,
    /// for a deterministic sweep of triangles.
    ///
    /// Written while the theorem was on the frontier, to keep it *unproved rather
    /// than unchecked*, and kept now that it is proved because it checks a
    /// different thing than the certificate does. The certificate establishes a
    /// polynomial identity; this establishes that the polynomials describe the
    /// configurations they are named after, at concrete points, computed by a
    /// route that shares nothing with the certifier.
    ///
    /// It also *is* the diagnosis the linear route acts on, in miniature: both
    /// systems are linear in the unknown centre with coefficients in `ℚ[ax..cy]`,
    /// and in both the determinant is a multiple of the very collinearity
    /// polynomial named as the non-degeneracy condition. That is why the theorem
    /// is true off the degeneracy locus, why the multiplier divides back out, and
    /// why `Buchberger`'s algorithm was being asked to rediscover Cramer's rule by
    /// monomial reduction.
    #[test]
    fn euler_line_holds_at_exactly_constructed_circumcentres() {
        let problem = euler_line();
        // Deterministic, and chosen so the sweep contains obtuse, right and
        // isosceles triangles as well as generic ones.
        let triangles: [[(i128, i128); 3]; 8] = [
            [(0, 0), (4, 0), (1, 3)],
            [(0, 0), (1, 0), (0, 1)],
            [(-2, -1), (5, 2), (1, 7)],
            [(0, 0), (6, 0), (3, 1)],
            [(3, -4), (-5, 2), (7, 9)],
            [(0, 0), (2, 0), (1, 5)],
            [(-1, -1), (4, -3), (2, 6)],
            [(10, 1), (-3, 4), (2, -8)],
        ];

        for corners in triangles {
            let assignment = euler_configuration(corners);
            for hypothesis in &problem.hypotheses {
                assert!(
                    vanishes_at(&hypothesis.poly, &assignment),
                    "euler-line: the constructed centres violate `{}` at {corners:?}",
                    hypothesis.id
                );
            }
            for condition in &problem.nondegeneracy {
                assert!(
                    !vanishes_at(&condition.poly, &assignment),
                    "euler-line: {corners:?} is degenerate for `{}`, so it proves nothing",
                    condition.id
                );
            }
            for conclusion in &problem.conclusions {
                assert!(
                    vanishes_at(&conclusion.poly, &assignment),
                    "euler-line: `{}` FAILS at {corners:?} -- the theorem as stated is wrong, \
                     not merely out of reach",
                    conclusion.id
                );
            }

            // The control on the control. A conclusion that vanishes at every
            // point one hands it is not evidence of anything until it is shown to
            // be capable of *not* vanishing: move the circumcentre off its
            // constructed position and O, G, H must stop being collinear. Without
            // this the sweep above would pass just as happily against the zero
            // polynomial.
            //
            // Both axes are tried and only one has to break, because a *unit step
            // along the Euler line itself* keeps the three points collinear —
            // which is not a weakness of the control, it is the theorem. The first
            // triangle here has a horizontal Euler line (`O = (2,1)`,
            // `G = (5/3,1)`, `H = (1,1)`), so moving `O` in x alone leaves the
            // conclusion satisfied. A line cannot be both horizontal and vertical,
            // so requiring one of the two is always a real demand.
            let broken = ["ox", "oy"].into_iter().any(|coordinate| {
                let mut perturbed = assignment.clone();
                let moved = assignment[coordinate]
                    .checked_add(Rational::integer(1))
                    .expect("no overflow");
                perturbed.insert(coordinate.to_string(), moved);
                problem
                    .conclusions
                    .iter()
                    .any(|conclusion| !vanishes_at(&conclusion.poly, &perturbed))
            });
            assert!(
                broken,
                "euler-line: moving the circumcentre off its constructed position along either \
                 axis left the conclusion satisfied at {corners:?}, so the sweep above proves \
                 nothing"
            );
        }
    }

    fn vanishes_at(poly: &MvPoly, assignment: &BTreeMap<String, Rational>) -> bool {
        poly.evaluate(assignment).expect("assigned").is_zero()
    }

    /// The `euler-line` coordinates for one integer triangle, with the
    /// circumcentre and orthocentre solved **exactly** by Cramer's rule.
    ///
    /// Both systems are linear in the unknown centre with coefficients in
    /// `ℚ[ax..cy]`, and in both the determinant is (twice) the collinearity
    /// polynomial the corpus names as the non-degeneracy condition — which is why
    /// the theorem is true off the degeneracy locus and undetermined on it.
    fn euler_configuration(corners: [(i128, i128); 3]) -> BTreeMap<String, Rational> {
        let [a, b, c] = corners.map(|(x, y)| (Rational::integer(x), Rational::integer(y)));
        let sub = |u: (Rational, Rational), v: (Rational, Rational)| {
            (
                u.0.checked_sub(v.0).expect("no overflow"),
                u.1.checked_sub(v.1).expect("no overflow"),
            )
        };
        let dot = |u: (Rational, Rational), v: (Rational, Rational)| {
            u.0.checked_mul(v.0)
                .and_then(|left| {
                    u.1.checked_mul(v.1)
                        .and_then(|right| left.checked_add(right))
                })
                .expect("no overflow")
        };
        let twice = |u: (Rational, Rational)| {
            let two = Rational::integer(2);
            (
                u.0.checked_mul(two).expect("no overflow"),
                u.1.checked_mul(two).expect("no overflow"),
            )
        };
        // Solve `[[row0], [row1]] · point = (first_rhs, second_rhs)` exactly.
        let solve = |row0: (Rational, Rational),
                     row1: (Rational, Rational),
                     first_rhs: Rational,
                     second_rhs: Rational| {
            let cross = |left: (Rational, Rational), right: (Rational, Rational)| {
                left.0
                    .checked_mul(right.1)
                    .and_then(|ad| {
                        left.1
                            .checked_mul(right.0)
                            .and_then(|bc| ad.checked_sub(bc))
                    })
                    .expect("no overflow")
            };
            let det = cross(row0, row1);
            assert!(!det.is_zero(), "the triangle must be non-degenerate");
            let abscissa = cross((first_rhs, row0.1), (second_rhs, row1.1))
                .checked_div(det)
                .expect("no overflow");
            let ordinate = cross((row0.0, first_rhs), (row1.0, second_rhs))
                .checked_div(det)
                .expect("no overflow");
            (abscissa, ordinate)
        };

        // Circumcentre: 2·O·(B−A) = |B|²−|A|²,  2·O·(C−B) = |C|²−|B|².
        let circumcentre = solve(
            twice(sub(b, a)),
            twice(sub(c, b)),
            dot(b, b).checked_sub(dot(a, a)).expect("no overflow"),
            dot(c, c).checked_sub(dot(b, b)).expect("no overflow"),
        );
        // Orthocentre: H·(C−B) = A·(C−B),  H·(A−C) = B·(A−C).
        let cb = sub(c, b);
        let ac = sub(a, c);
        let orthocentre = solve(cb, ac, dot(a, cb), dot(b, ac));

        [
            ("ax", a.0),
            ("ay", a.1),
            ("bx", b.0),
            ("by", b.1),
            ("cx", c.0),
            ("cy", c.1),
            ("ox", circumcentre.0),
            ("oy", circumcentre.1),
            ("hx", orthocentre.0),
            ("hy", orthocentre.1),
        ]
        .into_iter()
        .map(|(name, value)| (name.to_string(), value))
        .collect()
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
