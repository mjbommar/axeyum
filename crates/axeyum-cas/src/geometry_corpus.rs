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
        rhombus_diagonals_perpendicular(),
        euler_line(),
    ]
}

/// Theorems stated here, correctly as far as the encoding goes, that do **not**
/// have a committed certificate.
///
/// Historically that meant "the search does not reach them", and for
/// `rhombus-diagonals-perpendicular` and `euler-line` it did. It no longer has to:
/// `pappus-hexagon` is here with a certificate the independent checker *accepts*,
/// held back by an evidence bar rather than by a budget. Both reasons belong on
/// one list, because from the ledger's point of view they are the same status —
/// no fact, no artifact — and the difference is in the note, not the outcome.
///
/// Entries stay in the tree rather than being deleted because the value of a
/// measured limit is that it is reproducible, and because a theorem here is
/// **unproved, not unchecked**: `every_frontier_witness_is_consistent` replays
/// every configuration a frontier entry states against its own polynomials, so a
/// mis-stated theorem cannot hide in this list waiting for a faster search.
///
/// `rhombus-diagonals-perpendicular` left this list on 2026-08-15 — it declined
/// under `lex` and certifies under `grevlex` in 21 s — and `euler-line` left it
/// the same day, which is what the list is for.
///
/// # `euler-line` was not reached by a bigger budget, and that is the point
///
/// The `geometry-frontier` lane's ladder
/// (`cargo run -p axeyum-cas --release --example geometry_obstruction euler-line`)
/// established what obstructed it, and the answer was not a duration. Under
/// `grevlex`, with the full condition set:
///
/// | S-pairs processed | still queued | basis | widest polynomial |
/// |---|---|---|---|
/// | 9 | 66 | 12 | 41 |
/// | 33 | 210 | 21 | 278 |
/// | 65 | 528 | 33 | 477 |
///
/// The queue grew faster than it drained, because the basis never saturated and
/// each new element queues one pair against every existing one. Not width — the
/// rhombus, which *finishes*, carries a 733-monomial polynomial at the same rung
/// against `euler-line`'s 477. Not memory — 117 MB against a 6 GB cap. Under
/// `lex`, doubling 65 → 129 pairs tripled the backlog and cost ten times the wall
/// clock. That is divergence, and no ceiling reaches the end of it.
///
/// What reached it was **not** a ceiling. All four hypotheses are affine in the
/// four unknowns `ox, oy, hx, hy` over `ℚ[ax…cy]`, so
/// [`crate::geometry_certify::certify_by_linear_elimination`] solves the two 2×2
/// systems by Cramer's rule and substitutes: 0 S-pairs, no basis, a zero residue,
/// and a certificate in **6 ms** against a computation that had not returned in
/// 27 minutes. The determinants are `4·collinear(A,B,C)` and `collinear(A,B,C)`,
/// so the multiplier is `4·collinear(A,B,C)²` — a power of the theorem's own
/// non-degeneracy condition, which is exactly why the Rabinowitsch generator can
/// divide it back out and the certificate stays in the original generators.
///
/// # `pappus-hexagon` is here even though the search **reaches** it
///
/// This entry is not a record of a failure to compute. Measured 2026-08-15,
/// `cargo run -p axeyum-cas --release --example geometry_linear_route -- pappus-hexagon`:
///
/// ```text
/// blocks=3  multiplier=468 terms, degree 6  residue=720 terms
///     block [xx,xy] rows [2,3]  det = 8 terms
///     block [yx,yy] rows [4,5]  det = 8 terms
///     block [zx,zy] rows [6,7]  det = 8 terms
///     handover over the 2 unconsumed generators: 1 S-pair, basis 2, residue in the ideal
/// CERTIFIED in 292 s, conditions = all three, 3583 cofactor terms, checker verified
/// ```
///
/// Eighteen coordinates, eight hypotheses, three 2×2 blocks: `X` is pinned by
/// `collinear(A,E,X)` and `collinear(B,D,X)`, both linear in `X`, with determinant
/// exactly `det(E−A, D−B)` — the theorem's own first non-degeneracy condition. The
/// same for `Y` and `Z`. The residue that linear algebra cannot remove is 720
/// terms and reduces against the two collinearity hypotheses the blocks did not
/// consume in a **single S-pair**. The algebra is settled and the independent
/// checker accepts the certificate.
///
/// It is on this list anyway, because what blocks it is the **counterexamples**,
/// and that is a bar this corpus sets on purpose. The corpus requires one
/// exact rational configuration per condition a certificate consumes: satisfying
/// every hypothesis, annihilating that condition, and *falsifying* a conclusion.
/// Pappus has one for the condition set **as a whole** — six points on the x-axis
/// makes every incidence hypothesis vacuous and leaves `X`, `Y`, `Z` free to be a
/// triangle — and this lane found none isolating a *single* condition. Three
/// attempts, each collapsing for a different reason, all through one mechanism:
///
/// - `AE ∥ BD` with the lines distinct: no `X` exists, so the configuration does
///   not satisfy the hypotheses and is not a witness at all.
/// - `AE = BD` as lines, so `X` is free along it: that forces `A, B, D, E`
///   collinear, hence the second line equals the first, hence *every* condition
///   vanishes too.
/// - `A = E`, so `collinear(A,E,X)` is vacuous and `X` is free along `BD`: the
///   other two conditions do survive, but line `AF` becomes the second line, so
///   `Y = D`, and line `CE` becomes the first, so `Z = B` — and `X` is already on
///   line `BD = ZY`. The conclusion holds identically.
///
/// Killing one intersection forces the two *other* constructed points onto the
/// very line the freed point is confined to. Whether that is a theorem or an
/// accident of three attempts is open, and it is the question to settle before
/// promoting this.
///
/// The consequence for the ledger is precise, and it is why a theorem the route
/// certifies is nonetheless not filed: its condition set would be minimal only
/// **budget-relative** in ADR-0455's sense — the empty subset is refuted by the
/// committed counterexample, and the size-1 and size-2 subsets are *undecided*.
/// `every_used_condition_set_is_minimal_absolutely` enumerates every proper subset
/// and refuses that, deliberately, so the downgrade cannot happen silently.
///
/// So the decision waiting here is a real one and it is stated rather than made:
/// either find a configuration isolating a single condition (or a smaller
/// condition set), **or** relax that ratchet to a named, justified exception and
/// write a fact whose `notes` say the minimality is budget-relative — which
/// ADR-0455 explicitly permits when it is warranted. What the ratchet prevents is
/// making the strong claim by default, and it is doing exactly that here. A
/// practical note for whoever takes it: the 292 s is almost entirely the seven
/// *failed* condition subsets, each paying a residue reduction before the
/// multiplier refuses to divide; the subset that works is a small part of it.
///
/// **Simson's line** is the one after, with the same shape — three feet of
/// perpendiculars, three 2×2 blocks, determinants `−|BC|²`, `−|CA|²`, `−|AB|²` —
/// plus a wrinkle this corpus has already recorded: `|BC|² ≠ 0` is **not**
/// `B ≠ C` over an arbitrary field of characteristic zero, because of the
/// isotropic directions over ℂ. Over ℚ the two coincide, which is exactly the
/// problem: the configurations that would witness the necessity of `|BC|² ≠ 0`
/// are not rational, and [`DegenerateWitness`] holds exact rationals. Stating
/// Simson honestly needs either a witness type over a quadratic extension, or a
/// fact that names the real-plane assumption in its footprint and says what that
/// costs.
#[must_use]
pub fn frontier() -> Vec<GeometryProblem> {
    vec![pappus_hexagon()]
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
/// the three "these two lines are not parallel" conditions. See [`frontier`] for
/// what this is measuring and why it is not in [`corpus`].
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
                    AF not parallel to CD, and BF not parallel to CE, then X, Y and Z are \
                    collinear. The conditions are needed as a SET: when all six points are \
                    collinear every incidence hypothesis is vacuous and X, Y, Z may be any three \
                    points at all."
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

/// The one configuration that breaks Pappus: `A=(0,0)`, `B=(1,0)`, `C=(3,0)`,
/// `D=(1,0)`, `E=(0,0)`, `F=(5,0)` — six points on the x-axis, so every
/// incidence hypothesis holds vacuously and all three conditions vanish, while
/// `X=(0,1)`, `Y=(2,0)`, `Z=(4,0)` is a genuine triangle.
///
/// It is offered for each of the three conditions because it annihilates each of
/// them, and that is exactly as much as this lane could establish: see
/// [`frontier`] for why no configuration isolating a *single* condition was
/// found, and why that is what keeps this theorem out of [`corpus`].
fn degenerate_pappus(condition_id: &str) -> DegenerateWitness {
    DegenerateWitness {
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
    use crate::geometry_certify::GeometryProblem;
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
