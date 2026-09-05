//! Geometry beyond the rational plane: conics as quadratic forms, points and
//! planes in space, homogeneous (projective) coordinates, and isometries as
//! maps — item 6 of `docs/math-department/13-computer-algebra.md`'s Next Ten.
//!
//! # What is certified, and how
//!
//! [`crate::geometry_certify`]'s Nullstellensatz cofactor certifier is
//! coordinate-agnostic: it takes hypothesis and conclusion **polynomials** and
//! finds a cofactor identity, and nothing about it is specific to the plane.
//! This module extends the *encoders* — new ways to turn a geometric statement
//! into [`MvPoly`] hypotheses and conclusions — and hands the results to the
//! same [`crate::geometry_certify::certify_any_route`] and the same
//! [`crate::geometry_check::check_certificate`], unmodified. Three theorems
//! land as new corpus entries with committed certificates:
//!
//! - [`tetrahedron_medians_concurrent_problem`] — the four medians of a
//!   tetrahedron (vertex to the centroid of the opposite face) meet at the
//!   centroid `(A+B+C+D)/4`, stated with three-component vector collinearity
//!   ([`collinear3`]) and one non-degeneracy condition ([`coplanar4`]: the
//!   four points are not coplanar). **This is measured, not assumed**: the
//!   plane's `medians-concurrent` states the analogous *incidence* form ("P
//!   on medians from A and B implies P on medians from C and D")
//!   unconditionally, and the first attempt here tried the same — this
//!   route's own search returned a genuine
//!   [`crate::geometry_certify::ProofOutcome::NotInSaturatedIdeal`] (a
//!   14-term nonzero remainder, 138.8 s), not a budget decline. The reason the
//!   plane case needs nothing while space does: two **distinct** lines in a
//!   plane always meet in exactly one point (or are parallel, admitting no
//!   solution), but two lines in space can **coincide**, and then every point
//!   on the shared line spuriously satisfies both median hypotheses. So this
//!   is the *location* form instead (mirroring the plane's
//!   `centroid-divides-medians`, which needs the analogous "triangle
//!   non-degenerate" condition for exactly this reason), with a committed
//!   [`DegenerateWitness`] exhibiting the coincident-median failure mode. It
//!   is genuinely certified (`artifacts/geometry-certificates/tetrahedron-medians-concurrent.json`,
//!   checker-verified, `abcd-not-coplanar` used) but its own reduction costs
//!   769.0 s in release, so its `#[test]` carries `#[ignore]` — see the Cost
//!   profile section and that test's doc for the measured diagnosis and why a
//!   smaller budget was tried and declined rather than shrinking the cost.
//! - [`tetrahedron_circumcenter_problem`] — the six perpendicular-bisector
//!   *planes* of a tetrahedron's edges meet at a common point: "P equidistant
//!   from A & B, from B & C, and from C & D" already forces P equidistant from
//!   every other pair, by [`equidistant3`]'s squared-distance equalities
//!   telescoping — `dist(P,A,C) = dist(P,A,B) + dist(P,B,C)` and so on — a
//!   **constant-cofactor identity**, no non-degeneracy condition. (As with the
//!   plane's `orthocentre-altitudes-concurrent`: the tetrahedron must be
//!   non-degenerate for such a P to *exist*, but that is an existence claim
//!   this theorem does not make.)
//! - [`conic_polar_is_tangent_problem`] — the algebraic signature of
//!   tangency. A general conic is homogenized to a quadratic form `Q̃` with
//!   its associated symmetric bilinear form `B̃` (so that
//!   `Q̃(u+v) = Q̃(u) + 2·B̃(u,v) + Q̃(v)` identically — [`conic_bilinear`]).
//!   Given `Q̃(P₀) = 0` (P₀ on the conic) and `B̃(P₀,D) = 0` (D on the polar
//!   line of P₀), the polarization identity collapses to
//!   `Q̃(P₀ + t·D) = t²·Q̃(D)`: the conic's value along the line through P₀ in
//!   direction D has (at least) a double zero at `t = 0`, which **is** the
//!   algebraic meaning of "the polar at a point on the conic is the tangent
//!   there". The cofactors are `1` and `2t` — a direct substitution, not a
//!   search — and no non-degeneracy condition is needed.
//!
//! # What is stated but **not** certified, and why
//!
//! - **Pascal's theorem** and **the projective statement of Desargues'
//!   theorem** are stated correctly in [`beyond_frontier`] — hypotheses,
//!   conclusion, and a concrete rational configuration confirmed (by direct
//!   polynomial evaluation, independent of the certifier) to satisfy every
//!   hypothesis and the conclusion — but neither has a committed certificate.
//!   Pascal's "six points on a common conic" hypothesis is the same
//!   6-row `[x², xy, y², x, y, 1]` determinant this module's `on_common_conic`
//!   uses, and it is large enough (the corpus's own `pappus-hexagon` needed a
//!   dedicated linear-elimination-plus-bounded-ansatz route to move from
//!   292 s to 6.7 ms on a hypothesis an order of magnitude smaller); a bounded
//!   attempt here (`reduction_steps` capped far below
//!   [`crate::geometry_certify::geometry_limits`]) declines rather than run
//!   an open-ended search on a host shared with other lanes
//!   (`docs/contributor-guide/multi-agent-worktrees.md`). Desargues is
//!   similarly left frontier, not because a fresh technical wall was found —
//!   see the next paragraph — but because reaching it would need the same
//!   kind of dedicated route Pappus needed, which this lane did not have
//!   budget to build.
//! - **Whether the certifier's non-degeneracy encoding can state "two
//!   projective points are distinct".** It cannot, as a *single* polynomial:
//!   `P = Q` projectively means every 2×2 minor of their coordinate pair
//!   vanishes, so `P ≠ Q` is a **disjunction** — "at least one minor is
//!   nonzero" — and [`crate::geometry_certify::Condition`] states a
//!   **conjunction** of nonzero polynomials (each named condition is
//!   independently required nonzero; there is no way to say "one of these
//!   three"). This module did *not* hit a genuine wall here, though: the
//!   crate already has the tool for the case this actually needs. A
//!   projective point is *not the origin* (the only failure mode for [`join`]
//!   and [`meet`]) iff its sum of squares `x² + y² + w²` is nonzero, and a
//!   **single** polynomial nonzero-condition is exactly what
//!   [`crate::geometry_certify::Condition`] wants — the same idiom the plane
//!   corpus already uses for squared distances, with the same `ℚ(i)`-isotropy
//!   caveat documented on `simson-line`. So "the intersection point is
//!   well-defined" is expressible; what is not expressible as one condition
//!   is "the two triangles are non-degenerate AND in **general** position",
//!   which is why Desargues stays in [`beyond_frontier`] rather than being
//!   forced through with an over-strong single-condition substitute.
//! - **Literal tangency for a general point** (as opposed to the double-root
//!   identity above) — "the polar line touches the conic at exactly one
//!   point" for a point *not already known to be on the conic* — needs a
//!   discriminant argument (a quadratic in `t` has a double root), which is
//!   outside plain ideal membership and is not attempted.
//!
//! # Out of scope
//!
//! Angles as numbers (ADR-1615 puts those in the kernel, not the CAS);
//! differential geometry; solid geometry beyond the plane, line, plane and
//! sphere primitives here (no polyhedra volume/surface theory, no solid
//! angles).
//!
//! # Cost profile (ADVISORY, not a committed benchmark)
//!
//! Measured via `cargo run -p axeyum-cas --release --example
//! emit_geometry_certificates -- <id>` (the same emitter and timing the plane
//! corpus's own doc comments quote), this host, 2026-09-05:
//!
//! - [`tetrahedron_circumcenter_problem`] (13 coordinate variables, 3
//!   hypotheses, 3 conclusions, no non-degeneracy): **30.2 ms**, release.
//! - [`conic_polar_is_tangent_problem`] (13 coordinate variables — 6 conic
//!   coefficients, 3+3 homogeneous point coordinates, 1 line parameter — 2
//!   hypotheses, 1 conclusion, no non-degeneracy): **239.2 ms**, release. Both
//!   settle by direct substitution (constant or linear cofactors, `1` and
//!   `2t` for the conic case) — no Gröbner search runs at all.
//! - [`tetrahedron_medians_concurrent_problem`] (15 coordinate variables, 6
//!   hypotheses, 3 conclusions, 1 non-degeneracy condition): **769.0 s**,
//!   release — by far the most expensive reduction in this module, and the
//!   reason its own `#[test]` carries `#[ignore]` (see that test's doc for
//!   the diagnosis: `certify_any_route`'s linear-block detector is scoped per
//!   *conclusion*, and each per-axis conclusion here mentions only one of
//!   `px,py,pz` while every hypothesis row mixes two of the three
//!   coordinates, so the fast linear route cannot see all three unknowns
//!   together and the search falls back to the general, slow route). A
//!   shrunk `Limits` (`reduction_steps` 4,000 vs. the default 50,000) was
//!   tried and *declined outright* rather than certifying faster, confirming
//!   the instance could not be cheaply shrunk without changing the certifier
//!   itself. The committed artifact is the source of truth thereafter — the
//!   `geometry_certificate_artifacts` integration suite re-derives it from the
//!   file in milliseconds, no search involved. An earlier, ultimately
//!   abandoned *incidence-form* statement of this theorem was measured at
//!   500+ s of sustained CPU under a **debug** `cargo test` before being
//!   killed; the debug/release gap on this route is roughly consistent with
//!   this crate's documented gap elsewhere
//!   (`docs/contributor-guide/prelude-build-cost.md`'s "up to 32×" note is
//!   about the Lean kernel specifically, but the same order of magnitude
//!   showed up here: the location-form fix measured 922.68 s for the full
//!   `--lib` suite in release vs. an earlier ~4,522 s debug run of the same
//!   32 tests). Use `--release` for anything beyond a quick correctness check
//!   on a Gröbner-search-backed theorem.
//!
//! Only [`tetrahedron_medians_concurrent_problem`] approached
//! [`crate::geometry_certify::geometry_limits`]'s ceilings on the route that
//! ultimately succeeds; none of the three returned `Declined` on a resource
//! reason in the certificates actually committed.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::geometry::{Circle, Line, Point};
use crate::geometry_certify::{
    Condition, Constraint, DegenerateWitness, GenericWitness, GeometryProblem,
};
use crate::mvpoly::MvPoly;
use crate::{CasExpr, Matrix, ZeroTest, equal, simplify_radicals};

// =============================================================================
// 1. Conics as quadratic forms (concrete, over `Rational`)
// =============================================================================

/// A conic section `a·x² + b·x·y + c·y² + d·x + e·y + f = 0` with exact
/// rational coefficients.
///
/// The representation is not normalized to a canonical scale (like
/// [`crate::geometry::Line`]), so an equal conic may be stored with
/// proportional coefficients; every predicate here is invariant under that
/// scaling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Conic {
    a: Rational,
    b: Rational,
    c: Rational,
    d: Rational,
    e: Rational,
    f: Rational,
}

/// Why [`Conic::through_five_points`] refused to produce a conic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConicRefusal {
    /// Coefficient arithmetic left the checked `i128` range.
    Overflow,
    /// The five points do not determine a **unique** conic up to scale: the
    /// `5 × 6` incidence matrix's null space has a dimension other than `1`.
    /// Zero would mean no conic (impossible for five point constraints, since
    /// the system is always underdetermined by at least one dimension, but
    /// reported honestly rather than assumed); more than one means the points
    /// are in special position (e.g. four of them collinear), admitting a
    /// whole pencil of conics through the five, so no single answer exists.
    NotInGeneralPosition {
        /// The measured null-space dimension (everything but `1`).
        null_space_dimension: usize,
    },
}

/// The kind of a non-degenerate conic, or [`ConicKind::Degenerate`] when the
/// `3 × 3` matrix of the conic's quadratic form is singular (the conic is a
/// point, a line, a pair of lines, or empty).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConicKind {
    /// Discriminant `b² − 4ac < 0`: a (possibly empty over ℝ, but here decided
    /// purely by the algebraic sign) ellipse, circle included.
    Ellipse,
    /// Discriminant `b² − 4ac = 0`.
    Parabola,
    /// Discriminant `b² − 4ac > 0`.
    Hyperbola,
    /// The `3 × 3` matrix `[[a, b/2, d/2], [b/2, c, e/2], [d/2, e/2, f]]` is
    /// singular: the conic degenerates to a point, a line, two lines, or the
    /// empty/whole-plane locus.
    Degenerate,
}

/// Extract the exact rational value of a constant [`CasExpr`], or `None` for
/// any other shape (never expected here: every entry this module builds is a
/// [`CasExpr::Const`]).
fn as_rational(expr: &CasExpr) -> Option<Rational> {
    match expr {
        CasExpr::Const(value) => Some(*value),
        _ => None,
    }
}

/// Whether a [`CasExpr`] is certified equal to zero.
fn is_certified_zero(expr: &CasExpr) -> bool {
    matches!(
        equal(expr, &CasExpr::int(0)),
        ZeroTest::Certified { equal: true, .. }
    )
}

impl Conic {
    /// The conic `a·x² + b·x·y + c·y² + d·x + e·y + f = 0`.
    #[must_use]
    pub fn new(
        coeff_a: Rational,
        coeff_b: Rational,
        coeff_c: Rational,
        coeff_d: Rational,
        coeff_e: Rational,
        coeff_f: Rational,
    ) -> Conic {
        Conic {
            a: coeff_a,
            b: coeff_b,
            c: coeff_c,
            d: coeff_d,
            e: coeff_e,
            f: coeff_f,
        }
    }

    /// The coefficient of `x²`.
    #[must_use]
    pub fn a(&self) -> Rational {
        self.a
    }

    /// The coefficient of `x·y`.
    #[must_use]
    pub fn b(&self) -> Rational {
        self.b
    }

    /// The coefficient of `y²`.
    #[must_use]
    pub fn c(&self) -> Rational {
        self.c
    }

    /// The coefficient of `x`.
    #[must_use]
    pub fn d(&self) -> Rational {
        self.d
    }

    /// The coefficient of `y`.
    #[must_use]
    pub fn e(&self) -> Rational {
        self.e
    }

    /// The constant term.
    #[must_use]
    pub fn f(&self) -> Rational {
        self.f
    }

    /// The value `a·x² + b·x·y + c·y² + d·x + e·y + f`, or `None` on overflow.
    fn eval_at(&self, p: &Point) -> Option<Rational> {
        let x = p.x();
        let y = p.y();
        let t1 = self.a.checked_mul(x)?.checked_mul(x)?;
        let t2 = self.b.checked_mul(x)?.checked_mul(y)?;
        let t3 = self.c.checked_mul(y)?.checked_mul(y)?;
        let t4 = self.d.checked_mul(x)?;
        let t5 = self.e.checked_mul(y)?;
        t1.checked_add(t2)?
            .checked_add(t3)?
            .checked_add(t4)?
            .checked_add(t5)?
            .checked_add(self.f)
    }

    /// Whether `p` lies exactly on this conic. Overflow is treated
    /// conservatively as not-incident, matching [`crate::geometry::Circle::contains`].
    #[must_use]
    pub fn on_conic(&self, p: &Point) -> bool {
        self.eval_at(p).is_some_and(Rational::is_zero)
    }

    /// Classify this conic by its discriminant and degeneracy, or `None` on
    /// overflow.
    ///
    /// Degeneracy is decided by [`Matrix::determinant`] on the conic's `3 × 3`
    /// symmetric matrix — the same reduce-to-a-determinant idiom
    /// [`crate::geometry::Circle::through_three`] uses for the circumcircle,
    /// generalized from the `2 × 2` cross-product case to the full quadratic
    /// form.
    #[must_use]
    pub fn classify(&self) -> Option<ConicKind> {
        let half_b = self.b.checked_div(Rational::integer(2))?;
        let half_d = self.d.checked_div(Rational::integer(2))?;
        let half_e = self.e.checked_div(Rational::integer(2))?;
        let matrix = Matrix::from_rows(vec![
            vec![
                CasExpr::Const(self.a),
                CasExpr::Const(half_b),
                CasExpr::Const(half_d),
            ],
            vec![
                CasExpr::Const(half_b),
                CasExpr::Const(self.c),
                CasExpr::Const(half_e),
            ],
            vec![
                CasExpr::Const(half_d),
                CasExpr::Const(half_e),
                CasExpr::Const(self.f),
            ],
        ])?;
        let determinant = matrix.determinant()?;
        if is_certified_zero(&determinant) {
            return Some(ConicKind::Degenerate);
        }
        let discriminant = self.b.checked_mul(self.b)?.checked_sub(
            Rational::integer(4)
                .checked_mul(self.a)?
                .checked_mul(self.c)?,
        )?;
        Some(if discriminant.is_zero() {
            ConicKind::Parabola
        } else if discriminant.numerator() < 0 {
            ConicKind::Ellipse
        } else {
            ConicKind::Hyperbola
        })
    }

    /// The conic through five points, together with a certificate that every
    /// point evaluates to zero on it — or the reason none was produced.
    ///
    /// Built from [`Matrix::null_space`] on the `5 × 6` matrix whose rows are
    /// each point's `[x², x·y, y², x, y, 1]` monomial vector: a conic's
    /// coefficients `[a,b,c,d,e,f]` pass through all five points exactly when
    /// they lie in this null space, so a unique conic (up to scale) exists
    /// exactly when the null space is one-dimensional.
    ///
    /// # Errors
    ///
    /// Returns [`ConicRefusal::Overflow`] on `i128` coefficient overflow, or
    /// [`ConicRefusal::NotInGeneralPosition`] when the five points do not
    /// determine a unique conic.
    pub fn through_five_points(
        points: &[Point; 5],
    ) -> Result<(Conic, ConicFiveCertificate), ConicRefusal> {
        let mut rows = Vec::with_capacity(5);
        for point in points {
            let x = point.x();
            let y = point.y();
            let row = (|| -> Option<Vec<CasExpr>> {
                let x2 = x.checked_mul(x)?;
                let xy = x.checked_mul(y)?;
                let y2 = y.checked_mul(y)?;
                Some(vec![
                    CasExpr::Const(x2),
                    CasExpr::Const(xy),
                    CasExpr::Const(y2),
                    CasExpr::Const(x),
                    CasExpr::Const(y),
                    CasExpr::Const(Rational::integer(1)),
                ])
            })()
            .ok_or(ConicRefusal::Overflow)?;
            rows.push(row);
        }
        let matrix = Matrix::from_rows(rows).ok_or(ConicRefusal::Overflow)?;
        let basis = matrix.null_space().ok_or(ConicRefusal::Overflow)?;
        if basis.len() != 1 {
            return Err(ConicRefusal::NotInGeneralPosition {
                null_space_dimension: basis.len(),
            });
        }
        let vector = &basis[0];
        let coeff = |index: usize| -> Option<Rational> { as_rational(vector.get(index, 0)?) };
        let conic = (|| -> Option<Conic> {
            Some(Conic::new(
                coeff(0)?,
                coeff(1)?,
                coeff(2)?,
                coeff(3)?,
                coeff(4)?,
                coeff(5)?,
            ))
        })()
        .ok_or(ConicRefusal::Overflow)?;
        Ok((
            conic,
            ConicFiveCertificate {
                points: *points,
                conic,
            },
        ))
    }

    /// The circle `circle`, expressed as a conic
    /// `x² + y² − 2c_x·x − 2c_y·y + (c_x² + c_y² − r²) = 0`. `None` on
    /// overflow.
    #[must_use]
    pub fn circle_as_conic(circle: &Circle) -> Option<Conic> {
        let center = circle.center();
        let cx = center.x();
        let cy = center.y();
        let f = cx
            .checked_mul(cx)?
            .checked_add(cy.checked_mul(cy)?)?
            .checked_sub(circle.radius_squared())?;
        Some(Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::integer(1),
            cx.checked_neg()?.checked_mul(Rational::integer(2))?,
            cy.checked_neg()?.checked_mul(Rational::integer(2))?,
            f,
        ))
    }
}

/// A checkable witness that a [`Conic`] passes through five named points.
///
/// `verify` re-derives the claim independently of
/// [`Conic::through_five_points`]'s null-space computation: it only
/// re-evaluates the conic's own quadratic form at each point, a different
/// code path through [`Conic::on_conic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConicFiveCertificate {
    points: [Point; 5],
    conic: Conic,
}

impl ConicFiveCertificate {
    /// The five points.
    #[must_use]
    pub fn points(&self) -> [Point; 5] {
        self.points
    }

    /// The conic.
    #[must_use]
    pub fn conic(&self) -> Conic {
        self.conic
    }

    /// Whether every point evaluates to zero on the conic — an independent
    /// re-check, not a replay of the producer's linear algebra.
    #[must_use]
    pub fn verify(&self) -> bool {
        self.points.iter().all(|point| self.conic.on_conic(point))
    }
}

// =============================================================================
// 2. Three dimensions (concrete, over `Rational`)
// =============================================================================

/// A point in space with exact rational coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point3 {
    x: Rational,
    y: Rational,
    z: Rational,
}

impl Point3 {
    /// The point `(x, y, z)`.
    #[must_use]
    pub fn new(x: Rational, y: Rational, z: Rational) -> Point3 {
        Point3 { x, y, z }
    }

    /// The `x` coordinate.
    #[must_use]
    pub fn x(&self) -> Rational {
        self.x
    }

    /// The `y` coordinate.
    #[must_use]
    pub fn y(&self) -> Rational {
        self.y
    }

    /// The `z` coordinate.
    #[must_use]
    pub fn z(&self) -> Rational {
        self.z
    }

    /// The Euclidean distance to `other`, as an exact [`CasExpr`] with the
    /// surd simplified (see [`crate::geometry::Point::distance`]). `None` on
    /// overflow.
    #[must_use]
    pub fn distance(&self, other: &Point3) -> Option<CasExpr> {
        let dx = other.x.checked_sub(self.x)?;
        let dy = other.y.checked_sub(self.y)?;
        let dz = other.z.checked_sub(self.z)?;
        let sum = dx
            .checked_mul(dx)?
            .checked_add(dy.checked_mul(dy)?)?
            .checked_add(dz.checked_mul(dz)?)?;
        Some(simplify_radicals(&CasExpr::Const(sum).sqrt()))
    }

    /// The midpoint of the segment from `self` to `other`, or `None` on
    /// overflow.
    #[must_use]
    pub fn midpoint(&self, other: &Point3) -> Option<Point3> {
        let two = Rational::integer(2);
        Some(Point3 {
            x: self.x.checked_add(other.x)?.checked_div(two)?,
            y: self.y.checked_add(other.y)?.checked_div(two)?,
            z: self.z.checked_add(other.z)?.checked_div(two)?,
        })
    }
}

/// The 3D vector cross product `(u₁,u₂,u₃) × (v₁,v₂,v₃)`, or `None` on
/// overflow.
///
/// This is the same operation as the homogeneous `join`/`meet` cross product
/// ([`join`], [`meet`]) — a plane normal from two in-plane vectors, a
/// projective line from two points, or a projective point from two lines are
/// all this one computation, unified here.
fn cross3(
    first: (Rational, Rational, Rational),
    second: (Rational, Rational, Rational),
) -> Option<(Rational, Rational, Rational)> {
    let (u1, u2, u3) = first;
    let (v1, v2, v3) = second;
    let result_x = u2.checked_mul(v3)?.checked_sub(u3.checked_mul(v2)?)?;
    let result_y = u3.checked_mul(v1)?.checked_sub(u1.checked_mul(v3)?)?;
    let result_z = u1.checked_mul(v2)?.checked_sub(u2.checked_mul(v1)?)?;
    Some((result_x, result_y, result_z))
}

/// A plane in space, stored as the coefficients of `a·x + b·y + c·z + d = 0`
/// with `(a, b, c) ≠ (0, 0, 0)`. Not normalized to a canonical scale.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Plane {
    a: Rational,
    b: Rational,
    c: Rational,
    d: Rational,
}

impl Plane {
    /// The plane `a·x + b·y + c·z + d = 0`, or `None` if `(a, b, c) = (0, 0, 0)`
    /// (no normal, not a plane).
    #[must_use]
    pub fn new(a: Rational, b: Rational, c: Rational, d: Rational) -> Option<Plane> {
        if a.is_zero() && b.is_zero() && c.is_zero() {
            return None;
        }
        Some(Plane { a, b, c, d })
    }

    /// The coefficient of `x`.
    #[must_use]
    pub fn a(&self) -> Rational {
        self.a
    }

    /// The coefficient of `y`.
    #[must_use]
    pub fn b(&self) -> Rational {
        self.b
    }

    /// The coefficient of `z`.
    #[must_use]
    pub fn c(&self) -> Rational {
        self.c
    }

    /// The constant term.
    #[must_use]
    pub fn d(&self) -> Rational {
        self.d
    }

    /// The value `a·p.x + b·p.y + c·p.z + d`, or `None` on overflow.
    fn eval_at(&self, p: &Point3) -> Option<Rational> {
        self.a
            .checked_mul(p.x)?
            .checked_add(self.b.checked_mul(p.y)?)?
            .checked_add(self.c.checked_mul(p.z)?)?
            .checked_add(self.d)
    }

    /// Whether `p` lies exactly on this plane. Overflow is treated
    /// conservatively as not-incident.
    #[must_use]
    pub fn contains(&self, p: &Point3) -> bool {
        self.eval_at(p).is_some_and(Rational::is_zero)
    }

    /// The plane through three non-collinear points, via the cross product of
    /// two edge vectors. `None` if the points are collinear (no unique plane)
    /// or on overflow.
    #[must_use]
    pub fn through_three_points(p1: &Point3, p2: &Point3, p3: &Point3) -> Option<Plane> {
        let edge1 = (
            p2.x.checked_sub(p1.x)?,
            p2.y.checked_sub(p1.y)?,
            p2.z.checked_sub(p1.z)?,
        );
        let edge2 = (
            p3.x.checked_sub(p1.x)?,
            p3.y.checked_sub(p1.y)?,
            p3.z.checked_sub(p1.z)?,
        );
        let (normal_x, normal_y, normal_z) = cross3(edge1, edge2)?;
        if normal_x.is_zero() && normal_y.is_zero() && normal_z.is_zero() {
            return None;
        }
        let constant = normal_x
            .checked_mul(p1.x)?
            .checked_add(normal_y.checked_mul(p1.y)?)?
            .checked_add(normal_z.checked_mul(p1.z)?)?
            .checked_neg()?;
        Some(Plane {
            a: normal_x,
            b: normal_y,
            c: normal_z,
            d: constant,
        })
    }
}

/// The distance from `p` to `plane`, as an exact [`CasExpr`]
/// `|a·p.x + b·p.y + c·p.z + d| / √(a² + b² + c²)`. `None` on overflow.
#[must_use]
pub fn distance_point_plane(plane: &Plane, p: &Point3) -> Option<CasExpr> {
    let value = plane.eval_at(p)?;
    let norm_sq = plane
        .a
        .checked_mul(plane.a)?
        .checked_add(plane.b.checked_mul(plane.b)?)?
        .checked_add(plane.c.checked_mul(plane.c)?)?;
    if norm_sq.is_zero() {
        return None;
    }
    Some(simplify_radicals(
        &(CasExpr::Const(value).abs() / CasExpr::Const(norm_sq).sqrt()),
    ))
}

/// A line in space: a point plus a nonzero direction vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Line3 {
    point: Point3,
    direction: (Rational, Rational, Rational),
}

impl Line3 {
    /// The line through `point` in `direction`, or `None` if `direction` is
    /// the zero vector.
    #[must_use]
    pub fn new(point: Point3, direction: (Rational, Rational, Rational)) -> Option<Line3> {
        if direction.0.is_zero() && direction.1.is_zero() && direction.2.is_zero() {
            return None;
        }
        Some(Line3 { point, direction })
    }

    /// The line through two distinct points, or `None` if they coincide or on
    /// overflow.
    #[must_use]
    pub fn through(p1: &Point3, p2: &Point3) -> Option<Line3> {
        let direction = (
            p2.x.checked_sub(p1.x)?,
            p2.y.checked_sub(p1.y)?,
            p2.z.checked_sub(p1.z)?,
        );
        Line3::new(*p1, direction)
    }

    /// A point on the line.
    #[must_use]
    pub fn point(&self) -> Point3 {
        self.point
    }

    /// The direction vector.
    #[must_use]
    pub fn direction(&self) -> (Rational, Rational, Rational) {
        self.direction
    }

    /// The point `self.point + t · self.direction`, or `None` on overflow.
    #[must_use]
    pub fn at(&self, t: Rational) -> Option<Point3> {
        Some(Point3 {
            x: self.point.x.checked_add(t.checked_mul(self.direction.0)?)?,
            y: self.point.y.checked_add(t.checked_mul(self.direction.1)?)?,
            z: self.point.z.checked_add(t.checked_mul(self.direction.2)?)?,
        })
    }
}

/// The intersection of `line` and `plane`, or `None` if the line is parallel
/// to the plane (including lying within it) or on overflow.
#[must_use]
pub fn intersection_line_plane(line: &Line3, plane: &Plane) -> Option<Point3> {
    let (dx, dy, dz) = line.direction;
    let denominator = plane
        .a
        .checked_mul(dx)?
        .checked_add(plane.b.checked_mul(dy)?)?
        .checked_add(plane.c.checked_mul(dz)?)?;
    if denominator.is_zero() {
        return None;
    }
    let numerator = plane.eval_at(&line.point)?.checked_neg()?;
    let t = numerator.checked_div(denominator)?;
    line.at(t)
}

/// Whether four points lie in a common plane, via [`Matrix::determinant`] of
/// the `4 × 4` matrix with rows `[x, y, z, 1]` — the spatial analogue of the
/// `3 × 3` collinearity determinant
/// ([`crate::geometry_certify::collinear`]'s concrete cousin). Overflow is
/// treated conservatively as not-coplanar.
#[must_use]
pub fn coplanar(p1: &Point3, p2: &Point3, p3: &Point3, p4: &Point3) -> bool {
    let row = |p: &Point3| {
        vec![
            CasExpr::Const(p.x),
            CasExpr::Const(p.y),
            CasExpr::Const(p.z),
            CasExpr::Const(Rational::integer(1)),
        ]
    };
    let Some(matrix) = Matrix::from_rows(vec![row(p1), row(p2), row(p3), row(p4)]) else {
        return false;
    };
    let Some(determinant) = matrix.determinant() else {
        return false;
    };
    is_certified_zero(&determinant)
}

/// A sphere, stored as its center and exact squared radius.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sphere {
    center: Point3,
    radius_squared: Rational,
}

impl Sphere {
    /// The center.
    #[must_use]
    pub fn center(&self) -> Point3 {
        self.center
    }

    /// The squared radius.
    #[must_use]
    pub fn radius_squared(&self) -> Rational {
        self.radius_squared
    }

    /// Whether `p` lies exactly on this sphere.
    #[must_use]
    pub fn contains(&self, p: &Point3) -> bool {
        let Some(dx) = p.x.checked_sub(self.center.x) else {
            return false;
        };
        let Some(dy) = p.y.checked_sub(self.center.y) else {
            return false;
        };
        let Some(dz) = p.z.checked_sub(self.center.z) else {
            return false;
        };
        let value = (|| -> Option<Rational> {
            dx.checked_mul(dx)?
                .checked_add(dy.checked_mul(dy)?)?
                .checked_add(dz.checked_mul(dz)?)
        })();
        value == Some(self.radius_squared)
    }
}

/// The sphere through four non-coplanar points, via [`Matrix::solve`] on the
/// `3 × 3` linear system obtained by subtracting the sphere equation
/// `|P − center|² = r²` pairwise against `p1` (the quadratic term in `center`
/// cancels, leaving a linear equation per point). `None` if the points are
/// coplanar (no unique sphere) or on overflow.
#[must_use]
pub fn sphere_through_four_points(
    p1: &Point3,
    p2: &Point3,
    p3: &Point3,
    p4: &Point3,
) -> Option<Sphere> {
    let norm_sq = |p: &Point3| -> Option<Rational> {
        p.x.checked_mul(p.x)?
            .checked_add(p.y.checked_mul(p.y)?)?
            .checked_add(p.z.checked_mul(p.z)?)
    };
    let n1 = norm_sq(p1)?;
    let row = |p: &Point3| -> Option<Vec<CasExpr>> {
        let two = Rational::integer(2);
        let dx = two.checked_mul(p.x.checked_sub(p1.x)?)?;
        let dy = two.checked_mul(p.y.checked_sub(p1.y)?)?;
        let dz = two.checked_mul(p.z.checked_sub(p1.z)?)?;
        Some(vec![
            CasExpr::Const(dx),
            CasExpr::Const(dy),
            CasExpr::Const(dz),
        ])
    };
    let rhs_value = |p: &Point3| -> Option<Rational> { norm_sq(p)?.checked_sub(n1) };
    let matrix = Matrix::from_rows(vec![row(p2)?, row(p3)?, row(p4)?])?;
    let rhs = Matrix::from_rows(vec![
        vec![CasExpr::Const(rhs_value(p2)?)],
        vec![CasExpr::Const(rhs_value(p3)?)],
        vec![CasExpr::Const(rhs_value(p4)?)],
    ])?;
    let solution = matrix.solve(&rhs)?;
    let center = Point3::new(
        as_rational(solution.get(0, 0)?)?,
        as_rational(solution.get(1, 0)?)?,
        as_rational(solution.get(2, 0)?)?,
    );
    let dx = p1.x.checked_sub(center.x)?;
    let dy = p1.y.checked_sub(center.y)?;
    let dz = p1.z.checked_sub(center.z)?;
    let radius_squared = dx
        .checked_mul(dx)?
        .checked_add(dy.checked_mul(dy)?)?
        .checked_add(dz.checked_mul(dz)?)?;
    Some(Sphere {
        center,
        radius_squared,
    })
}

// =============================================================================
// 3. Homogeneous coordinates (concrete, over `Rational`)
// =============================================================================

/// A point in the projective plane, in homogeneous coordinates `(x : y : w)`.
/// Points at infinity have `w = 0`; every other point represents the affine
/// point `(x/w, y/w)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HPoint {
    x: Rational,
    y: Rational,
    w: Rational,
}

impl HPoint {
    /// The homogeneous point `(x : y : w)`.
    #[must_use]
    pub fn new(x: Rational, y: Rational, w: Rational) -> HPoint {
        HPoint { x, y, w }
    }

    /// The finite point `(x, y)`, as `(x : y : 1)`.
    #[must_use]
    pub fn finite(x: Rational, y: Rational) -> HPoint {
        HPoint {
            x,
            y,
            w: Rational::integer(1),
        }
    }

    /// The point at infinity in direction `(x, y)`, as `(x : y : 0)`.
    #[must_use]
    pub fn at_infinity(x: Rational, y: Rational) -> HPoint {
        HPoint {
            x,
            y,
            w: Rational::zero(),
        }
    }

    /// The `x` coordinate.
    #[must_use]
    pub fn x(&self) -> Rational {
        self.x
    }

    /// The `y` coordinate.
    #[must_use]
    pub fn y(&self) -> Rational {
        self.y
    }

    /// The `w` coordinate.
    #[must_use]
    pub fn w(&self) -> Rational {
        self.w
    }

    /// Whether this is a point at infinity (`w = 0`).
    #[must_use]
    pub fn is_infinite(&self) -> bool {
        self.w.is_zero()
    }

    /// The affine point `(x/w, y/w)`, or `None` at infinity or on overflow.
    #[must_use]
    pub fn to_affine(&self) -> Option<Point> {
        if self.w.is_zero() {
            return None;
        }
        Some(Point::new(
            self.x.checked_div(self.w)?,
            self.y.checked_div(self.w)?,
        ))
    }
}

/// A line in the projective plane, `a·x + b·y + c·w = 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HLine {
    a: Rational,
    b: Rational,
    c: Rational,
}

impl HLine {
    /// The line `a·x + b·y + c·w = 0`.
    #[must_use]
    pub fn new(a: Rational, b: Rational, c: Rational) -> HLine {
        HLine { a, b, c }
    }

    /// The line at infinity, `w = 0`.
    #[must_use]
    pub fn at_infinity() -> HLine {
        HLine {
            a: Rational::zero(),
            b: Rational::zero(),
            c: Rational::integer(1),
        }
    }

    /// The coefficient of `x`.
    #[must_use]
    pub fn a(&self) -> Rational {
        self.a
    }

    /// The coefficient of `y`.
    #[must_use]
    pub fn b(&self) -> Rational {
        self.b
    }

    /// The coefficient of `w`.
    #[must_use]
    pub fn c(&self) -> Rational {
        self.c
    }

    /// The incidence value `a·p.x + b·p.y + c·p.w`, or `None` on overflow.
    fn eval_at(&self, p: &HPoint) -> Option<Rational> {
        self.a
            .checked_mul(p.x)?
            .checked_add(self.b.checked_mul(p.y)?)?
            .checked_add(self.c.checked_mul(p.w)?)
    }

    /// Whether `p` is incident to this line. Overflow is treated
    /// conservatively as not-incident.
    #[must_use]
    pub fn contains(&self, p: &HPoint) -> bool {
        self.eval_at(p).is_some_and(Rational::is_zero)
    }
}

/// The line joining two distinct projective points, via the cross product of
/// their coordinate triples. `None` if `p` and `q` represent the same point
/// (cross product zero) or on overflow.
#[must_use]
pub fn join(first: &HPoint, second: &HPoint) -> Option<HLine> {
    let (line_a, line_b, line_c) =
        cross3((first.x, first.y, first.w), (second.x, second.y, second.w))?;
    if line_a.is_zero() && line_b.is_zero() && line_c.is_zero() {
        return None;
    }
    Some(HLine {
        a: line_a,
        b: line_b,
        c: line_c,
    })
}

/// The point where two distinct projective lines meet, via the cross product
/// of their coefficient triples — the same computation as [`join`], dual.
/// `None` if `l` and `m` are the same line (cross product zero) or on
/// overflow.
#[must_use]
pub fn meet(first: &HLine, second: &HLine) -> Option<HPoint> {
    let (point_x, point_y, point_w) =
        cross3((first.a, first.b, first.c), (second.a, second.b, second.c))?;
    if point_x.is_zero() && point_y.is_zero() && point_w.is_zero() {
        return None;
    }
    Some(HPoint {
        x: point_x,
        y: point_y,
        w: point_w,
    })
}

// =============================================================================
// 4. Isometries as maps (concrete)
// =============================================================================

/// Why [`Isometry::new`] refused a candidate map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsometryRefusal {
    /// Coefficient arithmetic left the checked `i128` range.
    Overflow,
    /// The linear part is not an orthogonal matrix (its columns are not
    /// exactly orthonormal), so the map would not preserve distance.
    NotOrthogonal,
}

/// A plane isometry: an orthogonal `2 × 2` rational matrix `M` plus a
/// translation `t`, acting as `p ↦ M·p + t`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Isometry {
    m00: Rational,
    m01: Rational,
    m10: Rational,
    m11: Rational,
    tx: Rational,
    ty: Rational,
}

/// The kind of a plane isometry, decided by the determinant of its linear
/// part and, for a reflective map, whether it has a fixed point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsometryKind {
    /// Linear part the identity: `p ↦ p + t`.
    Translation,
    /// Determinant `+1`, linear part not the identity: a rotation about the
    /// given fixed center.
    Rotation(Point),
    /// Determinant `−1`, with a fixed line: a reflection about the given
    /// axis.
    Reflection(Line),
    /// Determinant `−1`, with **no** fixed point: a reflection about the
    /// given axis composed with a nonzero translation along it.
    Glide(Line),
}

impl Isometry {
    /// The isometry `p ↦ [[m00,m01],[m10,m11]]·p + (tx,ty)`, or the reason it
    /// was refused: the linear part must be exactly orthogonal (its columns
    /// exactly orthonormal), checked by exact rational arithmetic.
    ///
    /// # Errors
    ///
    /// Returns [`IsometryRefusal::Overflow`] on `i128` overflow while checking
    /// orthogonality, or [`IsometryRefusal::NotOrthogonal`] when the linear
    /// part is not exactly orthogonal.
    pub fn new(
        m00: Rational,
        m01: Rational,
        m10: Rational,
        m11: Rational,
        tx: Rational,
        ty: Rational,
    ) -> Result<Isometry, IsometryRefusal> {
        let orthogonal = (|| -> Option<bool> {
            let column1 = m00.checked_mul(m00)?.checked_add(m10.checked_mul(m10)?)?;
            let column2 = m01.checked_mul(m01)?.checked_add(m11.checked_mul(m11)?)?;
            let cross = m00.checked_mul(m01)?.checked_add(m10.checked_mul(m11)?)?;
            Some(
                column1 == Rational::integer(1)
                    && column2 == Rational::integer(1)
                    && cross.is_zero(),
            )
        })();
        match orthogonal {
            None => Err(IsometryRefusal::Overflow),
            Some(false) => Err(IsometryRefusal::NotOrthogonal),
            Some(true) => Ok(Isometry {
                m00,
                m01,
                m10,
                m11,
                tx,
                ty,
            }),
        }
    }

    /// The pure translation `p ↦ p + (tx,ty)`.
    #[must_use]
    pub fn translation(tx: Rational, ty: Rational) -> Isometry {
        Isometry {
            m00: Rational::integer(1),
            m01: Rational::zero(),
            m10: Rational::zero(),
            m11: Rational::integer(1),
            tx,
            ty,
        }
    }

    /// The rotation about the origin by the angle with `(cos, sin)`, refused
    /// unless `cos² + sin² = 1` exactly (a "Pythagorean angle" — e.g.
    /// `(3/5, 4/5)`).
    ///
    /// # Errors
    ///
    /// See [`Isometry::new`].
    pub fn rotation(cos: Rational, sin: Rational) -> Result<Isometry, IsometryRefusal> {
        let neg_sin = sin.checked_neg().ok_or(IsometryRefusal::Overflow)?;
        Isometry::new(cos, neg_sin, sin, cos, Rational::zero(), Rational::zero())
    }

    /// The reflection about the line through the origin at angle `θ/2`, where
    /// `(cos θ, sin θ)` is the given Pythagorean angle: matrix
    /// `[[cos,sin],[sin,−cos]]`, determinant `−1`.
    ///
    /// # Errors
    ///
    /// See [`Isometry::new`].
    pub fn reflection_through_origin(
        cos: Rational,
        sin: Rational,
    ) -> Result<Isometry, IsometryRefusal> {
        let neg_cos = cos.checked_neg().ok_or(IsometryRefusal::Overflow)?;
        Isometry::new(cos, sin, sin, neg_cos, Rational::zero(), Rational::zero())
    }

    /// This isometry, with `(dx, dy)` added to its translation. `None` on
    /// overflow.
    #[must_use]
    pub fn translate(&self, dx: Rational, dy: Rational) -> Option<Isometry> {
        Some(Isometry {
            tx: self.tx.checked_add(dx)?,
            ty: self.ty.checked_add(dy)?,
            ..*self
        })
    }

    /// The linear part `((m00,m01),(m10,m11))`.
    #[must_use]
    pub fn matrix(&self) -> (Rational, Rational, Rational, Rational) {
        (self.m00, self.m01, self.m10, self.m11)
    }

    /// The translation `(tx, ty)`.
    #[must_use]
    pub fn translation_vector(&self) -> (Rational, Rational) {
        (self.tx, self.ty)
    }

    /// The determinant `m00·m11 − m01·m10` of the linear part (exactly `±1`
    /// for an orthogonal matrix). `None` on overflow.
    #[must_use]
    pub fn determinant(&self) -> Option<Rational> {
        self.m00
            .checked_mul(self.m11)?
            .checked_sub(self.m01.checked_mul(self.m10)?)
    }

    /// `M·p + t`, or `None` on overflow.
    #[must_use]
    pub fn apply(&self, p: &Point) -> Option<Point> {
        let x = self
            .m00
            .checked_mul(p.x())?
            .checked_add(self.m01.checked_mul(p.y())?)?
            .checked_add(self.tx)?;
        let y = self
            .m10
            .checked_mul(p.x())?
            .checked_add(self.m11.checked_mul(p.y())?)?
            .checked_add(self.ty)?;
        Some(Point::new(x, y))
    }

    /// The composition `self ∘ other` (apply `other`, then `self`). `None` on
    /// overflow, or in the unexpected case the exact product of two
    /// orthogonal matrices failed the orthogonality check (never observed —
    /// see the module tests — but not assumed away).
    #[must_use]
    pub fn compose(&self, other: &Isometry) -> Option<Isometry> {
        let m00 = self
            .m00
            .checked_mul(other.m00)?
            .checked_add(self.m01.checked_mul(other.m10)?)?;
        let m01 = self
            .m00
            .checked_mul(other.m01)?
            .checked_add(self.m01.checked_mul(other.m11)?)?;
        let m10 = self
            .m10
            .checked_mul(other.m00)?
            .checked_add(self.m11.checked_mul(other.m10)?)?;
        let m11 = self
            .m10
            .checked_mul(other.m01)?
            .checked_add(self.m11.checked_mul(other.m11)?)?;
        let tx = self
            .m00
            .checked_mul(other.tx)?
            .checked_add(self.m01.checked_mul(other.ty)?)?
            .checked_add(self.tx)?;
        let ty = self
            .m10
            .checked_mul(other.tx)?
            .checked_add(self.m11.checked_mul(other.ty)?)?
            .checked_add(self.ty)?;
        Isometry::new(m00, m01, m10, m11, tx, ty).ok()
    }

    /// The inverse `p ↦ Mᵀ·(p − t)`, valid because `M` is orthogonal
    /// (`M⁻¹ = Mᵀ`). `None` on overflow.
    #[must_use]
    pub fn inverse(&self) -> Option<Isometry> {
        // Transpose swaps m01 and m10.
        let m00 = self.m00;
        let m01 = self.m10;
        let m10 = self.m01;
        let m11 = self.m11;
        let tx = m00
            .checked_mul(self.tx)?
            .checked_add(m01.checked_mul(self.ty)?)?
            .checked_neg()?;
        let ty = m10
            .checked_mul(self.tx)?
            .checked_add(m11.checked_mul(self.ty)?)?
            .checked_neg()?;
        Isometry::new(m00, m01, m10, m11, tx, ty).ok()
    }

    /// Classify this isometry: translation, rotation, reflection or glide.
    ///
    /// Reuses [`Matrix::solve`] for the rotation's fixed point (`(M−I)p = −t`,
    /// invertible whenever `M ≠ I` and `det(M) = 1`) and [`Matrix::null_space`]
    /// for the reflective case's axis direction (the eigenvector of `M` for
    /// eigenvalue `1`, found by solving `(M−I)v = 0` exactly rather than via
    /// a half-angle formula, which would leave the rational field). `None` on
    /// overflow.
    #[must_use]
    pub fn classify(&self) -> Option<IsometryKind> {
        let one = Rational::integer(1);
        let zero = Rational::zero();
        if self.m00 == one && self.m01 == zero && self.m10 == zero && self.m11 == one {
            return Some(IsometryKind::Translation);
        }
        let determinant = self.determinant()?;
        let a11 = self.m00.checked_sub(one)?;
        let a12 = self.m01;
        let a21 = self.m10;
        let a22 = self.m11.checked_sub(one)?;
        let minus_i = Matrix::from_rows(vec![
            vec![CasExpr::Const(a11), CasExpr::Const(a12)],
            vec![CasExpr::Const(a21), CasExpr::Const(a22)],
        ])?;
        if determinant == one {
            let rhs = Matrix::from_rows(vec![
                vec![CasExpr::Const(self.tx.checked_neg()?)],
                vec![CasExpr::Const(self.ty.checked_neg()?)],
            ])?;
            let solution = minus_i.solve(&rhs)?;
            let center = Point::new(
                as_rational(solution.get(0, 0)?)?,
                as_rational(solution.get(1, 0)?)?,
            );
            return Some(IsometryKind::Rotation(center));
        }
        if determinant == one.checked_neg()? {
            let basis = minus_i.null_space()?;
            let direction = basis.first()?;
            let vx = as_rational(direction.get(0, 0)?)?;
            let vy = as_rational(direction.get(1, 0)?)?;
            let norm_sq = vx.checked_mul(vx)?.checked_add(vy.checked_mul(vy)?)?;
            let along = self
                .tx
                .checked_mul(vx)?
                .checked_add(self.ty.checked_mul(vy)?)?;
            let scale = along.checked_div(norm_sq)?;
            let parallel = (scale.checked_mul(vx)?, scale.checked_mul(vy)?);
            let perpendicular = (
                self.tx.checked_sub(parallel.0)?,
                self.ty.checked_sub(parallel.1)?,
            );
            let half = Rational::new(1, 2);
            let axis_p0 = Point::new(
                half.checked_mul(perpendicular.0)?,
                half.checked_mul(perpendicular.1)?,
            );
            let axis_p1 = Point::new(axis_p0.x().checked_add(vx)?, axis_p0.y().checked_add(vy)?);
            let axis = Line::through(&axis_p0, &axis_p1)?;
            return Some(if parallel.0.is_zero() && parallel.1.is_zero() {
                IsometryKind::Reflection(axis)
            } else {
                IsometryKind::Glide(axis)
            });
        }
        None
    }
}

/// A certificate that an [`Isometry`] preserves squared distance, proved on a
/// **generic symbolic pair of points** — the crate's [`equal`] zero-test on
/// `distSq(apply(P), apply(Q)) − distSq(P, Q)`, expanded symbolically, not a
/// numeric spot check.
#[derive(Debug, Clone)]
pub struct DistancePreservingCertificate {
    difference: CasExpr,
}

impl DistancePreservingCertificate {
    /// The difference `distSq(apply(P),apply(Q)) − distSq(P,Q)` this
    /// certificate claims is identically zero.
    #[must_use]
    pub fn difference(&self) -> &CasExpr {
        &self.difference
    }

    /// Whether the crate's zero-test certifies the difference is zero — the
    /// independent re-derivation.
    #[must_use]
    pub fn verify(&self) -> bool {
        is_certified_zero(&self.difference)
    }
}

/// Build the [`DistancePreservingCertificate`] for `iso`, at a generic
/// symbolic pair of points `P = (px,py)`, `Q = (qx,qy)`.
#[must_use]
pub fn certify_preserves_distance(iso: &Isometry) -> DistancePreservingCertificate {
    let px = CasExpr::Var("px".into());
    let py = CasExpr::Var("py".into());
    let qx = CasExpr::Var("qx".into());
    let qy = CasExpr::Var("qy".into());
    let apply = |x: &CasExpr, y: &CasExpr| -> (CasExpr, CasExpr) {
        let ax = CasExpr::Const(iso.m00) * x.clone()
            + CasExpr::Const(iso.m01) * y.clone()
            + CasExpr::Const(iso.tx);
        let ay = CasExpr::Const(iso.m10) * x.clone()
            + CasExpr::Const(iso.m11) * y.clone()
            + CasExpr::Const(iso.ty);
        (ax, ay)
    };
    let (apx, apy) = apply(&px, &py);
    let (aqx, aqy) = apply(&qx, &qy);
    let dx = px - qx;
    let dy = py - qy;
    let dist_sq_before = dx.clone() * dx + dy.clone() * dy;
    let adx = apx - aqx;
    let ady = apy - aqy;
    let dist_sq_after = adx.clone() * adx + ady.clone() * ady;
    DistancePreservingCertificate {
        difference: dist_sq_after - dist_sq_before,
    }
}

// =============================================================================
// Symbolic encoders for the cofactor certifier (3D, conics, homogeneous)
// =============================================================================

/// A point in space at symbolic coordinates, the 3D analogue of
/// [`crate::geometry_certify::Pt`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pt3 {
    /// The abscissa.
    pub x: MvPoly,
    /// The ordinate.
    pub y: MvPoly,
    /// The applicate.
    pub z: MvPoly,
}

impl Pt3 {
    /// A point at three fresh indeterminates `<name>x`, `<name>y`, `<name>z`.
    #[must_use]
    pub fn free(name: &str) -> Pt3 {
        Pt3 {
            x: MvPoly::var(&format!("{name}x")),
            y: MvPoly::var(&format!("{name}y")),
            z: MvPoly::var(&format!("{name}z")),
        }
    }

    /// Componentwise difference, `None` on coefficient overflow.
    #[must_use]
    pub fn sub(&self, other: &Pt3) -> Option<Pt3> {
        Some(Pt3 {
            x: self.x.sub(&other.x)?,
            y: self.y.sub(&other.y)?,
            z: self.z.sub(&other.z)?,
        })
    }

    /// Componentwise sum, `None` on coefficient overflow.
    #[must_use]
    pub fn add(&self, other: &Pt3) -> Option<Pt3> {
        Some(Pt3 {
            x: self.x.add(&other.x)?,
            y: self.y.add(&other.y)?,
            z: self.z.add(&other.z)?,
        })
    }

    /// Scale both coordinates by an exact rational.
    #[must_use]
    pub fn scale(&self, factor: Rational) -> Option<Pt3> {
        let constant = MvPoly::constant(factor);
        Some(Pt3 {
            x: self.x.mul(&constant)?,
            y: self.y.mul(&constant)?,
            z: self.z.mul(&constant)?,
        })
    }
}

/// The 3D vector cross product `first × second`, `None` on overflow.
#[must_use]
pub fn cross3_mv(first: &Pt3, second: &Pt3) -> Option<Pt3> {
    Some(Pt3 {
        x: first.y.mul(&second.z)?.sub(&first.z.mul(&second.y)?)?,
        y: first.z.mul(&second.x)?.sub(&first.x.mul(&second.z)?)?,
        z: first.x.mul(&second.y)?.sub(&first.y.mul(&second.x)?)?,
    })
}

/// The Euclidean inner product `first · second`, `None` on overflow.
#[must_use]
pub fn dot3(first: &Pt3, second: &Pt3) -> Option<MvPoly> {
    first
        .x
        .mul(&second.x)?
        .add(&first.y.mul(&second.y)?)?
        .add(&first.z.mul(&second.z)?)
}

/// `|AB|²`, `None` on overflow.
#[must_use]
pub fn dist_sq3(from: &Pt3, to: &Pt3) -> Option<MvPoly> {
    let delta = to.sub(from)?;
    dot3(&delta, &delta)
}

/// `A`, `B`, `C` are collinear in space: the three components of the cross
/// product `(B−A) × (C−A)` all vanish. `None` on overflow.
#[must_use]
pub fn collinear3(first: &Pt3, second: &Pt3, third: &Pt3) -> Option<[MvPoly; 3]> {
    let cross = cross3_mv(&second.sub(first)?, &third.sub(first)?)?;
    Some([cross.x, cross.y, cross.z])
}

/// `A`, `B`, `C`, `D` are coplanar: the scalar triple product
/// `(B−A) · ((C−A) × (D−A))` vanishes. `None` on overflow.
#[must_use]
pub fn coplanar4(first: &Pt3, second: &Pt3, third: &Pt3, fourth: &Pt3) -> Option<MvPoly> {
    let edge1 = second.sub(first)?;
    let edge2 = third.sub(first)?;
    let edge3 = fourth.sub(first)?;
    let cross = cross3_mv(&edge2, &edge3)?;
    dot3(&edge1, &cross)
}

/// `|AB| = |CD|`, stated on squared distances so it stays polynomial. `None`
/// on overflow.
#[must_use]
pub fn equidistant3(from: &Pt3, to: &Pt3, other_from: &Pt3, other_to: &Pt3) -> Option<MvPoly> {
    dist_sq3(from, to)?.sub(&dist_sq3(other_from, other_to)?)
}

/// The centroid of `A`, `B`, `C`, constructed rather than asserted. `None` on
/// overflow.
#[must_use]
pub fn centroid3(first: &Pt3, second: &Pt3, third: &Pt3) -> Option<Pt3> {
    first.add(second)?.add(third)?.scale(Rational::new(1, 3))
}

/// A point in the projective plane at symbolic coordinates, the homogeneous
/// analogue of [`crate::geometry_certify::Pt`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HPt {
    /// The `x` coordinate.
    pub x: MvPoly,
    /// The `y` coordinate.
    pub y: MvPoly,
    /// The `w` coordinate.
    pub w: MvPoly,
}

impl HPt {
    /// A point at three fresh indeterminates `<name>x`, `<name>y`, `<name>w`.
    #[must_use]
    pub fn free(name: &str) -> HPt {
        HPt {
            x: MvPoly::var(&format!("{name}x")),
            y: MvPoly::var(&format!("{name}y")),
            w: MvPoly::var(&format!("{name}w")),
        }
    }

    /// The affine (symbolic) point `p`, lifted to the chart `w = 1`.
    #[must_use]
    pub fn chart(p: &crate::geometry_certify::Pt) -> HPt {
        HPt {
            x: p.x.clone(),
            y: p.y.clone(),
            w: MvPoly::constant(Rational::integer(1)),
        }
    }
}

/// The cross product of two symbolic homogeneous triples, `None` on overflow.
/// The shared computation behind [`hjoin`] and [`hmeet`] — join and meet are
/// the same operation, dual.
fn cross3_mv_triple(
    first: (&MvPoly, &MvPoly, &MvPoly),
    second: (&MvPoly, &MvPoly, &MvPoly),
) -> Option<(MvPoly, MvPoly, MvPoly)> {
    let (x1, y1, z1) = first;
    let (x2, y2, z2) = second;
    let a = y1.mul(z2)?.sub(&z1.mul(y2)?)?;
    let b = z1.mul(x2)?.sub(&x1.mul(z2)?)?;
    let c = x1.mul(y2)?.sub(&y1.mul(x2)?)?;
    Some((a, b, c))
}

/// The symbolic line joining `p` and `q`, as its `(a,b,c)` coefficient
/// triple. `None` on overflow.
#[must_use]
pub fn hjoin(p: &HPt, q: &HPt) -> Option<(MvPoly, MvPoly, MvPoly)> {
    cross3_mv_triple((&p.x, &p.y, &p.w), (&q.x, &q.y, &q.w))
}

/// The symbolic point where lines `l` and `m` meet. `None` on overflow.
#[must_use]
pub fn hmeet(first: &(MvPoly, MvPoly, MvPoly), second: &(MvPoly, MvPoly, MvPoly)) -> Option<HPt> {
    let (point_x, point_y, point_w) = cross3_mv_triple(
        (&first.0, &first.1, &first.2),
        (&second.0, &second.1, &second.2),
    )?;
    Some(HPt {
        x: point_x,
        y: point_y,
        w: point_w,
    })
}

/// The incidence value `a·p.x + b·p.y + c·p.w` of a symbolic line `(a,b,c)`
/// at a symbolic point. `None` on overflow.
#[must_use]
pub fn hincidence(line: &(MvPoly, MvPoly, MvPoly), p: &HPt) -> Option<MvPoly> {
    line.0
        .mul(&p.x)?
        .add(&line.1.mul(&p.y)?)?
        .add(&line.2.mul(&p.w)?)
}

/// `P`, `Q`, `R` are collinear (incident to a common line): `R` is incident
/// to the join of `P` and `Q`. `None` on overflow.
#[must_use]
pub fn hcollinear(p: &HPt, q: &HPt, r: &HPt) -> Option<MvPoly> {
    let line = hjoin(p, q)?;
    hincidence(&line, r)
}

/// A general conic at symbolic coefficients, homogenized to a quadratic form
/// `Q̃(X,Y,W) = a·X² + b·X·Y + c·Y² + dd·X·W + ee·Y·W + ff·W²` (so `dd`/`ee`
/// stand for the affine conic's `d`/`e` — renamed only to avoid colliding
/// with a `d`-named direction point in the theorems that use this).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymConic {
    a: MvPoly,
    b: MvPoly,
    c: MvPoly,
    dd: MvPoly,
    ee: MvPoly,
    ff: MvPoly,
}

impl SymConic {
    /// A conic at six fresh coefficient indeterminates `<name>a` .. `<name>f`.
    #[must_use]
    pub fn free(name: &str) -> SymConic {
        SymConic {
            a: MvPoly::var(&format!("{name}a")),
            b: MvPoly::var(&format!("{name}b")),
            c: MvPoly::var(&format!("{name}c")),
            dd: MvPoly::var(&format!("{name}dd")),
            ee: MvPoly::var(&format!("{name}ee")),
            ff: MvPoly::var(&format!("{name}ff")),
        }
    }
}

/// The homogeneous quadratic form `Q̃(p) = a·p.x² + b·p.x·p.y + c·p.y² +
/// dd·p.x·p.w + ee·p.y·p.w + ff·p.w²`. `None` on overflow.
#[must_use]
pub fn conic_quadratic_form(conic: &SymConic, p: &HPt) -> Option<MvPoly> {
    let t1 = conic.a.mul(&p.x)?.mul(&p.x)?;
    let t2 = conic.b.mul(&p.x)?.mul(&p.y)?;
    let t3 = conic.c.mul(&p.y)?.mul(&p.y)?;
    let t4 = conic.dd.mul(&p.x)?.mul(&p.w)?;
    let t5 = conic.ee.mul(&p.y)?.mul(&p.w)?;
    let t6 = conic.ff.mul(&p.w)?.mul(&p.w)?;
    t1.add(&t2)?.add(&t3)?.add(&t4)?.add(&t5)?.add(&t6)
}

/// The symmetric bilinear form `B̃` associated to [`conic_quadratic_form`],
/// satisfying `Q̃(p+q) = Q̃(p) + 2·B̃(p,q) + Q̃(q)` identically — the polar of a
/// point `p` (with respect to the conic) is the line `B̃(p, ·) = 0`. `None` on
/// overflow.
#[must_use]
pub fn conic_bilinear(conic: &SymConic, p: &HPt, q: &HPt) -> Option<MvPoly> {
    let half = MvPoly::constant(Rational::new(1, 2));
    let t1 = conic.a.mul(&p.x)?.mul(&q.x)?;
    let t2 = conic
        .b
        .mul(&half)?
        .mul(&p.x.mul(&q.y)?.add(&p.y.mul(&q.x)?)?)?;
    let t3 = conic.c.mul(&p.y)?.mul(&q.y)?;
    let t4 = conic
        .dd
        .mul(&half)?
        .mul(&p.x.mul(&q.w)?.add(&p.w.mul(&q.x)?)?)?;
    let t5 = conic
        .ee
        .mul(&half)?
        .mul(&p.y.mul(&q.w)?.add(&p.w.mul(&q.y)?)?)?;
    let t6 = conic.ff.mul(&p.w)?.mul(&q.w)?;
    t1.add(&t2)?.add(&t3)?.add(&t4)?.add(&t5)?.add(&t6)
}

// =============================================================================
// Committed corpus entries (called from `geometry_corpus::corpus`)
// =============================================================================

/// A rational assignment from `(variable, numerator, denominator)` triples —
/// the same shape [`crate::geometry_corpus`]'s private `at` helper uses,
/// duplicated here rather than shared because that one is private to its
/// module.
fn at(entries: &[(&str, i128, i128)]) -> BTreeMap<String, Rational> {
    entries
        .iter()
        .map(|(name, numerator, denominator)| {
            ((*name).to_string(), Rational::new(*numerator, *denominator))
        })
        .collect()
}

/// Gloss rows for the coordinates of named 3D points.
fn gloss3(points: &[(&str, &str)]) -> Vec<(String, String)> {
    let mut rows = Vec::with_capacity(points.len() * 3);
    for (var, label) in points {
        rows.push((format!("{var}x"), format!("{label}.x")));
        rows.push((format!("{var}y"), format!("{label}.y")));
        rows.push((format!("{var}z"), format!("{label}.z")));
    }
    rows
}

/// The four medians of a tetrahedron (vertex to the centroid of the opposite
/// face) meet at the centroid `(A+B+C+D)/4`, given the tetrahedron is
/// non-degenerate.
///
/// **Measured, not assumed.** The natural first attempt was the *incidence*
/// form the plane's `medians-concurrent` uses unconditionally ("P on the
/// medians from A and B implies P on the medians from C and D", no
/// non-degeneracy) — this route's own search over that statement returned a
/// nonzero 14-term remainder in 138.8 s (release), a genuine
/// [`crate::geometry_certify::ProofOutcome::NotInSaturatedIdeal`], not a
/// budget decline. The plane case works unconditionally because two
/// **distinct** lines in the plane always meet in exactly one point (or are
/// parallel); in space two lines can instead **coincide**, admitting every
/// point on the shared line as a spurious solution to both hypotheses, so the
/// incidence form genuinely needs the tetrahedron to be non-degenerate. This
/// is therefore the *location* form instead, mirroring the plane's
/// `centroid-divides-medians` (which needs the analogous "triangle
/// non-degenerate" condition for exactly the same reason).
///
/// # Panics
///
/// Panics on `i128` coefficient overflow while building the fixed, small
/// symbolic polynomials this problem is stated with (never observed here).
#[must_use]
pub fn tetrahedron_medians_concurrent_problem() -> GeometryProblem {
    let vertex_a = Pt3::free("a");
    let vertex_b = Pt3::free("b");
    let vertex_c = Pt3::free("c");
    let vertex_d = Pt3::free("d");
    let meeting = Pt3::free("p");
    let hub_one = centroid3(&vertex_b, &vertex_c, &vertex_d).expect("centroid3");
    let hub_two = centroid3(&vertex_a, &vertex_c, &vertex_d).expect("centroid3");
    let hyp_a = collinear3(&vertex_a, &hub_one, &meeting).expect("collinear3");
    let hyp_b = collinear3(&vertex_b, &hub_two, &meeting).expect("collinear3");
    let not_coplanar = coplanar4(&vertex_a, &vertex_b, &vertex_c, &vertex_d).expect("coplanar4");
    let four = MvPoly::constant(Rational::integer(4));
    let total = vertex_a
        .add(&vertex_b)
        .expect("sum")
        .add(&vertex_c)
        .expect("sum")
        .add(&vertex_d)
        .expect("sum");

    let axis = ["x", "y", "z"];
    let mut hypotheses = Vec::with_capacity(6);
    for (component, poly) in axis.iter().zip(hyp_a) {
        hypotheses.push(Constraint::new(
            &format!("p-on-median-from-a-{component}"),
            "P is collinear with A and the centroid of BCD (one vector component)",
            poly,
        ));
    }
    for (component, poly) in axis.iter().zip(hyp_b) {
        hypotheses.push(Constraint::new(
            &format!("p-on-median-from-b-{component}"),
            "P is collinear with B and the centroid of ACD (one vector component)",
            poly,
        ));
    }
    let conclusions = vec![
        Constraint::new(
            "centroid-x",
            "4 P.x = A.x + B.x + C.x + D.x",
            four.mul(&meeting.x)
                .expect("product")
                .sub(&total.x)
                .expect("difference"),
        ),
        Constraint::new(
            "centroid-y",
            "4 P.y = A.y + B.y + C.y + D.y",
            four.mul(&meeting.y)
                .expect("product")
                .sub(&total.y)
                .expect("difference"),
        ),
        Constraint::new(
            "centroid-z",
            "4 P.z = A.z + B.z + C.z + D.z",
            four.mul(&meeting.z)
                .expect("product")
                .sub(&total.z)
                .expect("difference"),
        ),
    ];

    GeometryProblem {
        id: "tetrahedron-medians-concurrent".into(),
        title: "the medians of a tetrahedron meet at the centroid (A+B+C+D)/4".into(),
        statement: "If A, B, C, D are NOT coplanar, and P lies on the median from A (the line \
                    through A and the centroid of BCD) and on the median from B (through B and the \
                    centroid of ACD), then 4P = A + B + C + D -- so P is also on the medians from C \
                    and D. The non-degeneracy condition is essential: on a degenerate (coplanar) \
                    tetrahedron the two median LINES can coincide, and every point on the shared \
                    line then satisfies both hypotheses while only one of them is the true \
                    centroid. See the function doc for the measured incidence-form attempt that \
                    failed without this condition."
            .into(),
        coordinate_gloss: gloss3(&[("a", "A"), ("b", "B"), ("c", "C"), ("d", "D"), ("p", "P")]),
        hypotheses,
        nondegeneracy: vec![Condition::new(
            "abcd-not-coplanar",
            "A, B, C, D are not coplanar (the tetrahedron has nonzero volume)",
            not_coplanar,
        )],
        conclusions,
        degenerate_witnesses: vec![DegenerateWitness::rational(
            "abcd-not-coplanar",
            "A=(1,1,0), B=(0,0,0), C=(3,0,0), D=(0,3,0) are coplanar (all z=0) and A is exactly \
             the centroid of B,C,D, so the median from A is vacuous (satisfied by every P); P = \
             (5,5,0) then lies on the median from B (through the origin in direction (1,1,0)) \
             while 4P = (20,20,0) but A+B+C+D = (4,4,0)",
            tetrahedron_medians_degenerate_assignment(),
        )],
        generic_witnesses: vec![GenericWitness {
            description: "A=(0,0,0), B=(4,0,0), C=(0,4,0), D=(0,0,4), centroid P=(1,1,1)".into(),
            assignment: tetrahedron_medians_generic_assignment(),
        }],
    }
}

/// The degenerate-witness coordinate assignment for
/// [`tetrahedron_medians_concurrent_problem`], extracted only to keep that
/// function's own line count down.
fn tetrahedron_medians_degenerate_assignment() -> BTreeMap<String, Rational> {
    at(&[
        ("ax", 1, 1),
        ("ay", 1, 1),
        ("az", 0, 1),
        ("bx", 0, 1),
        ("by", 0, 1),
        ("bz", 0, 1),
        ("cx", 3, 1),
        ("cy", 0, 1),
        ("cz", 0, 1),
        ("dx", 0, 1),
        ("dy", 3, 1),
        ("dz", 0, 1),
        ("px", 5, 1),
        ("py", 5, 1),
        ("pz", 0, 1),
    ])
}

/// The generic-witness coordinate assignment for
/// [`tetrahedron_medians_concurrent_problem`], extracted only to keep that
/// function's own line count down.
fn tetrahedron_medians_generic_assignment() -> BTreeMap<String, Rational> {
    at(&[
        ("ax", 0, 1),
        ("ay", 0, 1),
        ("az", 0, 1),
        ("bx", 4, 1),
        ("by", 0, 1),
        ("bz", 0, 1),
        ("cx", 0, 1),
        ("cy", 4, 1),
        ("cz", 0, 1),
        ("dx", 0, 1),
        ("dy", 0, 1),
        ("dz", 4, 1),
        ("px", 1, 1),
        ("py", 1, 1),
        ("pz", 1, 1),
    ])
}

/// The six perpendicular-bisector planes of a tetrahedron's edges meet at a
/// common point (the circumcenter), stated as: equidistance from three
/// "consecutive" pairs forces equidistance from every other pair. **No
/// non-degeneracy condition is used** — see the module doc (mirrors the
/// plane's `orthocentre-altitudes-concurrent`).
///
/// # Panics
///
/// Panics on `i128` coefficient overflow while building the fixed, small
/// symbolic polynomials this problem is stated with (never observed here).
#[must_use]
pub fn tetrahedron_circumcenter_problem() -> GeometryProblem {
    let vertex_a = Pt3::free("a");
    let vertex_b = Pt3::free("b");
    let vertex_c = Pt3::free("c");
    let vertex_d = Pt3::free("d");
    let meeting = Pt3::free("p");
    let dist_one = equidistant3(&meeting, &vertex_a, &meeting, &vertex_b).expect("equidistant3");
    let dist_two = equidistant3(&meeting, &vertex_b, &meeting, &vertex_c).expect("equidistant3");
    let dist_three = equidistant3(&meeting, &vertex_c, &meeting, &vertex_d).expect("equidistant3");
    let dist_four = equidistant3(&meeting, &vertex_a, &meeting, &vertex_c).expect("equidistant3");
    let dist_five = equidistant3(&meeting, &vertex_b, &meeting, &vertex_d).expect("equidistant3");
    let dist_six = equidistant3(&meeting, &vertex_a, &meeting, &vertex_d).expect("equidistant3");

    GeometryProblem {
        id: "tetrahedron-perpendicular-bisectors-concurrent".into(),
        title: "the perpendicular bisector planes of a tetrahedron's edges are concurrent".into(),
        statement: "If P is equidistant from A and B, from B and C, and from C and D, then P is \
                    equidistant from A and C, from B and D, and from A and D -- so all six \
                    perpendicular-bisector planes of the tetrahedron ABCD's edges pass through P. \
                    NO non-degeneracy condition is required: the identity is a telescoping sum of \
                    the three hypotheses (e.g. `P eq A,C` = `P eq A,B` + `P eq B,C`), valid for \
                    ANY four points. The tetrahedron must be non-degenerate for such a P to EXIST \
                    and be unique, but that is an existence claim this theorem does not make -- \
                    exactly as the plane's `orthocentre-altitudes-concurrent`."
            .into(),
        coordinate_gloss: gloss3(&[("a", "A"), ("b", "B"), ("c", "C"), ("d", "D"), ("p", "P")]),
        hypotheses: vec![
            Constraint::new("p-eq-ab", "P is equidistant from A and B", dist_one),
            Constraint::new("p-eq-bc", "P is equidistant from B and C", dist_two),
            Constraint::new("p-eq-cd", "P is equidistant from C and D", dist_three),
        ],
        nondegeneracy: Vec::new(),
        conclusions: vec![
            Constraint::new("p-eq-ac", "P is equidistant from A and C", dist_four),
            Constraint::new("p-eq-bd", "P is equidistant from B and D", dist_five),
            Constraint::new("p-eq-ad", "P is equidistant from A and D", dist_six),
        ],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "A=(0,0,0), B=(4,0,0), C=(0,4,0), D=(0,0,4), circumcenter P=(2,2,2)"
                .into(),
            assignment: at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("az", 0, 1),
                ("bx", 4, 1),
                ("by", 0, 1),
                ("bz", 0, 1),
                ("cx", 0, 1),
                ("cy", 4, 1),
                ("cz", 0, 1),
                ("dx", 0, 1),
                ("dy", 0, 1),
                ("dz", 4, 1),
                ("px", 2, 1),
                ("py", 2, 1),
                ("pz", 2, 1),
            ]),
        }],
    }
}

/// The polar line of a point on a conic is tangent there, stated as the
/// algebraic signature of tangency (a double zero at `t = 0` along the polar
/// direction) — see the module doc for the polarization-identity derivation.
/// **No non-degeneracy condition is used.**
///
/// # Panics
///
/// Panics on `i128` coefficient overflow while building the fixed, small
/// symbolic polynomials this problem is stated with (never observed here).
#[must_use]
pub fn conic_polar_is_tangent_problem() -> GeometryProblem {
    let conic = SymConic::free("q");
    let p0 = HPt::free("p0");
    let direction = HPt::free("d");
    let t = MvPoly::var("t");

    let on_conic = conic_quadratic_form(&conic, &p0).expect("quadratic form");
    let on_polar = conic_bilinear(&conic, &p0, &direction).expect("bilinear form");

    let scaled_direction = HPt {
        x: direction.x.mul(&t).expect("mul"),
        y: direction.y.mul(&t).expect("mul"),
        w: direction.w.mul(&t).expect("mul"),
    };
    let along_line = HPt {
        x: p0.x.add(&scaled_direction.x).expect("add"),
        y: p0.y.add(&scaled_direction.y).expect("add"),
        w: p0.w.add(&scaled_direction.w).expect("add"),
    };
    let value_along_line = conic_quadratic_form(&conic, &along_line).expect("quadratic form");
    let t_squared = t.mul(&t).expect("mul");
    let value_at_direction = conic_quadratic_form(&conic, &direction).expect("quadratic form");
    let double_root = value_along_line
        .sub(&t_squared.mul(&value_at_direction).expect("mul"))
        .expect("sub");

    GeometryProblem {
        id: "conic-polar-is-tangent".into(),
        title: "the polar line of a point on a conic is the tangent line there".into(),
        statement: "Let Q be a general conic (homogenized to a quadratic form), P0 a point on it, \
                    and D a point on the polar line of P0 with respect to Q. Then, writing the \
                    conic's value along the line through P0 in direction D as a function of the \
                    parameter t, Q(P0 + t*D) = t^2 * Q(D) identically: the value has (at least) a \
                    double zero at t=0, which is the algebraic meaning of tangency at P0. NO \
                    non-degeneracy condition is required: the identity is the polarization identity \
                    Q(u+v) = Q(u) + 2*B(u,v) + Q(v) with the two hypotheses substituted in, cofactors \
                    1 and 2t -- a direct substitution, not a search."
            .into(),
        coordinate_gloss: vec![
            ("qa".into(), "conic coefficient a".into()),
            ("qb".into(), "conic coefficient b".into()),
            ("qc".into(), "conic coefficient c".into()),
            ("qdd".into(), "conic coefficient d".into()),
            ("qee".into(), "conic coefficient e".into()),
            ("qff".into(), "conic coefficient f".into()),
            ("p0x".into(), "P0.X".into()),
            ("p0y".into(), "P0.Y".into()),
            ("p0w".into(), "P0.W".into()),
            ("dx".into(), "D.X".into()),
            ("dy".into(), "D.Y".into()),
            ("dw".into(), "D.W".into()),
            ("t".into(), "the parameter along the line P0 + t*D".into()),
        ],
        hypotheses: vec![
            Constraint::new("p0-on-conic", "P0 lies on the conic Q", on_conic),
            Constraint::new("d-on-polar-of-p0", "D lies on the polar line of P0 with respect to Q", on_polar),
        ],
        nondegeneracy: Vec::new(),
        conclusions: vec![Constraint::new(
            "double-root-at-p0",
            "Q(P0 + t*D) = t^2 * Q(D): the conic's value along the line has a double zero at t=0",
            double_root,
        )],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "the unit circle X^2+Y^2-W^2=0, P0=(1:0:1) on it, D=(0:1:0) on its polar \
                          (the vertical tangent X=W), t=2"
                .into(),
            assignment: at(&[
                ("qa", 1, 1), ("qb", 0, 1), ("qc", 1, 1),
                ("qdd", 0, 1), ("qee", 0, 1), ("qff", -1, 1),
                ("p0x", 1, 1), ("p0y", 0, 1), ("p0w", 1, 1),
                ("dx", 0, 1), ("dy", 1, 1), ("dw", 0, 1),
                ("t", 2, 1),
            ]),
        }],
    }
}

// =============================================================================
// Stated but uncertified theorems (see the module doc): Pascal, Desargues
// =============================================================================

/// The theorems this module states correctly and checks by direct evaluation
/// at a concrete witness, but does **not** certify — see the module doc for
/// why each stays here rather than in
/// [`crate::geometry_corpus::corpus`]/`artifacts/geometry-certificates/`.
///
/// Mirrors [`crate::geometry_corpus::frontier`]'s idiom: a theorem here is
/// **unproved, not unchecked** — the module tests replay every generic
/// witness against its own polynomials directly, independent of the
/// certifier.
#[must_use]
pub fn beyond_frontier() -> Vec<GeometryProblem> {
    vec![pascal_hexagon_problem(), desargues_problem()]
}

/// The `6 × 6` "six points on a common conic" determinant: rows
/// `[x², x·y, y², x, y, 1]`, one per point, via recursive `2 × 2`/`3 × 3`
/// Laplace expansion in the style of
/// [`crate::geometry_certify::concyclic`]'s `4 × 4` cousin, generalized. Large
/// enough that certifying a theorem using it (below) is left to future work —
/// see the module doc.
fn on_common_conic(points: &[HPt; 6]) -> Option<MvPoly> {
    let rows: Vec<Vec<MvPoly>> = points
        .iter()
        .map(|p| -> Option<Vec<MvPoly>> {
            // Affine chart (w = 1 in this frontier statement, so points here
            // are plain affine points lifted via HPt::chart -- x2, xy, y2, x, y, 1).
            let x2 = p.x.mul(&p.x)?;
            let xy = p.x.mul(&p.y)?;
            let y2 = p.y.mul(&p.y)?;
            Some(vec![x2, xy, y2, p.x.clone(), p.y.clone(), p.w.clone()])
        })
        .collect::<Option<Vec<_>>>()?;
    determinant_n(&rows)
}

/// The determinant of an `n × n` matrix of [`MvPoly`] entries (given as rows),
/// by recursive Laplace expansion along the first row. `O(n!)`, meant for
/// small `n` (mirrors [`Matrix::determinant`]'s concrete-`CasExpr` cousin).
fn determinant_n(rows: &[Vec<MvPoly>]) -> Option<MvPoly> {
    let n = rows.len();
    if n == 1 {
        return Some(rows[0][0].clone());
    }
    let mut total = MvPoly::zero();
    for (col, entry) in rows[0].iter().enumerate() {
        if entry.is_zero() {
            continue;
        }
        let minor: Vec<Vec<MvPoly>> = rows[1..]
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .filter(|(index, _)| *index != col)
                    .map(|(_, value)| value.clone())
                    .collect()
            })
            .collect();
        let minor_det = determinant_n(&minor)?;
        let term = entry.mul(&minor_det)?;
        total = if col % 2 == 0 {
            total.add(&term)?
        } else {
            total.sub(&term)?
        };
    }
    Some(total)
}

/// Pascal's theorem, stated but not certified — see the module doc.
fn pascal_hexagon_problem() -> GeometryProblem {
    let pts: Vec<HPt> = ["a", "b", "c", "d", "e", "f"]
        .iter()
        .map(|name| HPt::free(name))
        .collect();
    let [point_a, point_b, point_c, point_d, point_e, point_f]: [HPt; 6] =
        pts.try_into().expect("six points");
    let conic = on_common_conic(&[
        point_a.clone(),
        point_b.clone(),
        point_c.clone(),
        point_d.clone(),
        point_e.clone(),
        point_f.clone(),
    ])
    .expect("6x6 determinant");

    let point_x = HPt::free("x");
    let point_y = HPt::free("y");
    let point_z = HPt::free("z");
    let side_one = hcollinear(&point_a, &point_b, &point_x).expect("hcollinear");
    let side_two = hcollinear(&point_d, &point_e, &point_x).expect("hcollinear");
    let side_three = hcollinear(&point_b, &point_c, &point_y).expect("hcollinear");
    let side_four = hcollinear(&point_e, &point_f, &point_y).expect("hcollinear");
    let side_five = hcollinear(&point_c, &point_d, &point_z).expect("hcollinear");
    let side_six = hcollinear(&point_f, &point_a, &point_z).expect("hcollinear");
    let conclusion = hcollinear(&point_x, &point_y, &point_z).expect("hcollinear");

    GeometryProblem {
        id: "pascal-hexagon".into(),
        title:
            "Pascal's theorem: the diagonal points of a hexagon inscribed in a conic are collinear"
                .into(),
        statement: "Let A,B,C,D,E,F lie on a common conic (the 6x6 monomial-vector determinant \
                    vanishes). Let X = AB . DE, Y = BC . EF, Z = CD . FA (the three intersection \
                    points of 'opposite' sides, homogeneous meet). Then X, Y, Z are collinear. \
                    STATED but not certified: the hypothesis is a 6x6 determinant, an order of \
                    magnitude larger than `pappus-hexagon`'s, which itself needed a dedicated \
                    linear-elimination-plus-bounded-ansatz route to move from 292s to 6.7ms; see \
                    the module doc."
            .into(),
        coordinate_gloss: vec![
            ("ax".into(), "A.X".into()),
            ("ay".into(), "A.Y".into()),
            ("aw".into(), "A.W".into()),
            ("bx".into(), "B.X".into()),
            ("by".into(), "B.Y".into()),
            ("bw".into(), "B.W".into()),
            ("cx".into(), "C.X".into()),
            ("cy".into(), "C.Y".into()),
            ("cw".into(), "C.W".into()),
            ("dx".into(), "D.X".into()),
            ("dy".into(), "D.Y".into()),
            ("dw".into(), "D.W".into()),
            ("ex".into(), "E.X".into()),
            ("ey".into(), "E.Y".into()),
            ("ew".into(), "E.W".into()),
            ("fx".into(), "F.X".into()),
            ("fy".into(), "F.Y".into()),
            ("fw".into(), "F.W".into()),
            ("xx".into(), "X.X".into()),
            ("xy".into(), "X.Y".into()),
            ("xw".into(), "X.W".into()),
            ("yx".into(), "Y.X".into()),
            ("yy".into(), "Y.Y".into()),
            ("yw".into(), "Y.W".into()),
            ("zx".into(), "Z.X".into()),
            ("zy".into(), "Z.Y".into()),
            ("zw".into(), "Z.W".into()),
        ],
        hypotheses: vec![
            Constraint::new(
                "abcdef-on-conic",
                "A,B,C,D,E,F lie on a common conic",
                conic,
            ),
            Constraint::new("x-on-ab", "X is collinear with A and B", side_one),
            Constraint::new("x-on-de", "X is collinear with D and E", side_two),
            Constraint::new("y-on-bc", "Y is collinear with B and C", side_three),
            Constraint::new("y-on-ef", "Y is collinear with E and F", side_four),
            Constraint::new("z-on-cd", "Z is collinear with C and D", side_five),
            Constraint::new("z-on-fa", "Z is collinear with F and A", side_six),
        ],
        nondegeneracy: Vec::new(),
        conclusions: vec![Constraint::new(
            "xyz-collinear",
            "X, Y, Z are collinear",
            conclusion,
        )],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "six points on the unit circle (w=1 chart): A=(1,0), B=(0,1), C=(-1,0), \
                          D=(0,-1), E=(3/5,4/5), F=(4/5,-3/5), with X, Y, Z the classical \
                          Pascal-line intersections computed from these"
                .into(),
            assignment: pascal_generic_witness(),
        }],
    }
}

/// The concrete numeric witness for [`pascal_hexagon_problem`]: six points on
/// the unit circle, with `X`, `Y`, `Z` computed directly by [`hjoin`]/[`hmeet`]
/// over concrete rationals (not the symbolic route), so the assignment is
/// correct **by construction**, independent of the certifier.
fn pascal_generic_witness() -> BTreeMap<String, Rational> {
    let pt = |x: i128, y: i128, xd: i128, yd: i128| -> HPoint {
        HPoint::finite(Rational::new(x, xd), Rational::new(y, yd))
    };
    let point_a = pt(1, 0, 1, 1);
    let point_b = pt(0, 1, 1, 1);
    let point_c = pt(-1, 0, 1, 1);
    let point_d = pt(0, -1, 1, 1);
    let point_e = pt(3, 4, 5, 5);
    let point_f = pt(4, -3, 5, 5);
    let point_x = meet(
        &join(&point_a, &point_b).expect("join"),
        &join(&point_d, &point_e).expect("join"),
    )
    .expect("meet");
    let point_y = meet(
        &join(&point_b, &point_c).expect("join"),
        &join(&point_e, &point_f).expect("join"),
    )
    .expect("meet");
    let point_z = meet(
        &join(&point_c, &point_d).expect("join"),
        &join(&point_f, &point_a).expect("join"),
    )
    .expect("meet");
    let mut assignment = BTreeMap::new();
    for (name, point) in [
        ("a", point_a),
        ("b", point_b),
        ("c", point_c),
        ("d", point_d),
        ("e", point_e),
        ("f", point_f),
        ("x", point_x),
        ("y", point_y),
        ("z", point_z),
    ] {
        assignment.insert(format!("{name}x"), point.x);
        assignment.insert(format!("{name}y"), point.y);
        assignment.insert(format!("{name}w"), point.w);
    }
    assignment
}

/// The projective statement of Desargues' theorem, stated but not certified —
/// see the module doc.
fn desargues_problem() -> GeometryProblem {
    let origin = HPt::free("o");
    let vertex_a = HPt::free("a");
    let vertex_b = HPt::free("b");
    let vertex_c = HPt::free("c");
    let image_a = HPt::free("a2");
    let image_b = HPt::free("b2");
    let image_c = HPt::free("c2");

    let perspective_one = hcollinear(&origin, &vertex_a, &image_a).expect("hcollinear");
    let perspective_two = hcollinear(&origin, &vertex_b, &image_b).expect("hcollinear");
    let perspective_three = hcollinear(&origin, &vertex_c, &image_c).expect("hcollinear");

    let bc = hjoin(&vertex_b, &vertex_c).expect("hjoin");
    let b2c2 = hjoin(&image_b, &image_c).expect("hjoin");
    let point_x = hmeet(&bc, &b2c2).expect("hmeet");
    let ca = hjoin(&vertex_c, &vertex_a).expect("hjoin");
    let c2a2 = hjoin(&image_c, &image_a).expect("hjoin");
    let point_y = hmeet(&ca, &c2a2).expect("hmeet");
    let ab = hjoin(&vertex_a, &vertex_b).expect("hjoin");
    let a2b2 = hjoin(&image_a, &image_b).expect("hjoin");
    let point_z = hmeet(&ab, &a2b2).expect("hmeet");

    let conclusion = hcollinear(&point_x, &point_y, &point_z).expect("hcollinear");

    GeometryProblem {
        id: "desargues-perspective-triangles".into(),
        title: "Desargues' theorem: perspective from a point implies perspective from a line"
            .into(),
        statement:
            "Let O, A, B, C, A', B', C' be projective points with O, A, A' collinear, O, B, \
                    B' collinear, and O, C, C' collinear (the triangles ABC and A'B'C' are in \
                    perspective from the point O). Let X = BC . B'C', Y = CA . C'A', Z = AB . A'B' \
                    (the meets of corresponding sides). Then X, Y, Z are collinear (the triangles \
                    are in perspective from a line). STATED but not certified: reaching it would \
                    need a dedicated route analogous to the one `pappus-hexagon` needed (this \
                    problem has roughly twice as many free points); see the module doc for the \
                    separate question of whether the non-degeneracy encoding can even state \
                    'the two triangles are in general position' (it can express the SUFFICIENT \
                    single-polynomial 'X, Y, Z are each not the coordinate origin', via sum of \
                    squares, but not the disjunctive 'the two triangles are non-degenerate and \
                    distinct' directly)."
                .into(),
        coordinate_gloss: [
            ("o", "O"),
            ("a", "A"),
            ("b", "B"),
            ("c", "C"),
            ("a2", "A'"),
            ("b2", "B'"),
            ("c2", "C'"),
        ]
        .iter()
        .flat_map(|(var, label)| {
            [
                (format!("{var}x"), format!("{label}.X")),
                (format!("{var}y"), format!("{label}.Y")),
                (format!("{var}w"), format!("{label}.W")),
            ]
        })
        .collect(),
        hypotheses: vec![
            Constraint::new(
                "o-a-a2-collinear",
                "O, A, A' are collinear",
                perspective_one,
            ),
            Constraint::new(
                "o-b-b2-collinear",
                "O, B, B' are collinear",
                perspective_two,
            ),
            Constraint::new(
                "o-c-c2-collinear",
                "O, C, C' are collinear",
                perspective_three,
            ),
        ],
        nondegeneracy: Vec::new(),
        conclusions: vec![Constraint::new(
            "xyz-collinear",
            "X, Y, Z are collinear",
            conclusion,
        )],
        degenerate_witnesses: Vec::new(),
        generic_witnesses: vec![GenericWitness {
            description: "O=(0,0), A=(1,0), B=(0,1), C=(1,1); A'=(2,0), B'=(0,2), C'=(2,2) (each \
                          A' on ray OA scaled by 2, etc.), with X, Y, Z computed directly from \
                          these by join/meet"
                .into(),
            assignment: desargues_generic_witness(),
        }],
    }
}

/// The concrete numeric witness for [`desargues_problem`]: `O`, `A`, `B`, `C`
/// and `A'=2A`, `B'=2B`, `C'=2C` (each on the ray from `O` through the
/// unprimed vertex, scaled by 2), with `X`, `Y`, `Z` computed directly by
/// [`hjoin`]/[`hmeet`] over concrete rationals.
fn desargues_generic_witness() -> BTreeMap<String, Rational> {
    let origin = HPoint::finite(Rational::zero(), Rational::zero());
    let vertex_a = HPoint::finite(Rational::integer(1), Rational::zero());
    let vertex_b = HPoint::finite(Rational::zero(), Rational::integer(1));
    let vertex_c = HPoint::finite(Rational::integer(1), Rational::integer(1));
    let scale2 = |point: &HPoint| {
        HPoint::finite(
            Rational::integer(2).checked_mul(point.x).expect("scale"),
            Rational::integer(2).checked_mul(point.y).expect("scale"),
        )
    };
    let image_a = scale2(&vertex_a);
    let image_b = scale2(&vertex_b);
    let image_c = scale2(&vertex_c);
    let point_x = meet(
        &join(&vertex_b, &vertex_c).expect("join"),
        &join(&image_b, &image_c).expect("join"),
    )
    .expect("meet");
    let point_y = meet(
        &join(&vertex_c, &vertex_a).expect("join"),
        &join(&image_c, &image_a).expect("join"),
    )
    .expect("meet");
    let point_z = meet(
        &join(&vertex_a, &vertex_b).expect("join"),
        &join(&image_a, &image_b).expect("join"),
    )
    .expect("meet");
    let mut assignment = BTreeMap::new();
    for (name, point) in [
        ("o", origin),
        ("a", vertex_a),
        ("b", vertex_b),
        ("c", vertex_c),
        ("a2", image_a),
        ("b2", image_b),
        ("c2", image_c),
        ("x", point_x),
        ("y", point_y),
        ("z", point_z),
    ] {
        assignment.insert(format!("{name}x"), point.x);
        assignment.insert(format!("{name}y"), point.y);
        assignment.insert(format!("{name}w"), point.w);
    }
    assignment
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::Point as GPoint;
    use crate::geometry_certify::{certify_any_route, geometry_limits};
    use crate::geometry_check::{CheckOptions, GeometryVerdict, check_certificate};
    use crate::groebner_cert::Limits;

    fn p(x: i128, y: i128) -> GPoint {
        GPoint::new(Rational::integer(x), Rational::integer(y))
    }

    fn p3(x: i128, y: i128, z: i128) -> Point3 {
        Point3::new(
            Rational::integer(x),
            Rational::integer(y),
            Rational::integer(z),
        )
    }

    fn certified_equal(a: &CasExpr, b: &CasExpr) -> bool {
        matches!(equal(a, b), ZeroTest::Certified { equal: true, .. })
    }

    // --- Conics ----------------------------------------------------------

    #[test]
    fn a_point_on_the_unit_circle_is_on_the_conic() {
        let conic = Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(-1),
        );
        assert!(conic.on_conic(&p(1, 0)));
        assert!(conic.on_conic(&p(0, -1)));
        assert!(!conic.on_conic(&p(1, 1)));
    }

    #[test]
    fn classify_finds_ellipse_parabola_hyperbola_and_degenerate() {
        let ellipse = Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(-1),
        );
        assert_eq!(ellipse.classify(), Some(ConicKind::Ellipse));
        let parabola = Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(-1),
            Rational::zero(),
        );
        assert_eq!(parabola.classify(), Some(ConicKind::Parabola));
        let hyperbola = Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::integer(-1),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(-1),
        );
        assert_eq!(hyperbola.classify(), Some(ConicKind::Hyperbola));
        // xy = 0: a pair of lines (the axes), degenerate.
        let degenerate = Conic::new(
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
            Rational::zero(),
            Rational::zero(),
        );
        assert_eq!(degenerate.classify(), Some(ConicKind::Degenerate));
    }

    #[test]
    fn through_five_points_recovers_the_unit_circle() {
        // A fifth point genuinely on the unit circle at (3/5, 4/5).
        let fifth = GPoint::new(Rational::new(3, 5), Rational::new(4, 5));
        let points = [p(1, 0), p(0, 1), p(-1, 0), p(0, -1), fifth];
        let (conic, certificate) = Conic::through_five_points(&points).expect("unique conic");
        assert!(certificate.verify());
        assert_eq!(conic.classify(), Some(ConicKind::Ellipse));
        assert!(conic.on_conic(&fifth));
    }

    #[test]
    fn a_forged_conic_five_certificate_naming_a_point_off_the_conic_is_rejected() {
        // A deliberately WRONG certificate: four genuine unit-circle points plus
        // one that is NOT on the conic. `verify` must independently catch this
        // rather than trust the producer.
        let points = [p(1, 0), p(0, 1), p(-1, 0), p(0, -1), p(2, 2)];
        let conic = Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(-1),
        );
        let forged = ConicFiveCertificate { points, conic };
        assert!(!forged.verify());
    }

    #[test]
    fn through_five_points_refuses_four_collinear_points() {
        let points = [p(0, 0), p(1, 0), p(2, 0), p(3, 0), p(0, 1)];
        let refusal = Conic::through_five_points(&points).expect_err("not in general position");
        assert!(matches!(refusal, ConicRefusal::NotInGeneralPosition { .. }));
    }

    #[test]
    fn circle_as_conic_agrees_with_circle_contains() {
        let circle = crate::geometry::Circle::through_three(&p(1, 0), &p(0, 1), &p(-1, 0))
            .expect("circumcircle");
        let conic = Conic::circle_as_conic(&circle).expect("conic");
        assert!(conic.on_conic(&p(0, -1)));
        assert!(!conic.on_conic(&p(0, 0)));
    }

    #[test]
    fn conic_polar_is_tangent_certifies_and_checks() {
        let problem = conic_polar_is_tangent_problem();
        let outcome = certify_any_route(&problem, geometry_limits());
        let certificate = match outcome {
            crate::geometry_certify::ProofOutcome::Certified(certificate) => certificate,
            other => panic!("expected a certificate, got {other:?}"),
        };
        match check_certificate(&certificate, &CheckOptions::default()) {
            GeometryVerdict::Verified(report) => {
                assert_eq!(report.conclusions_checked, 1);
                assert!(report.generic_witnesses_checked > 0);
            }
            GeometryVerdict::Rejected(reason) => panic!("checker rejected: {reason}"),
        }
    }

    // --- 3D ----------------------------------------------------------------

    #[test]
    fn distance_of_a_1_2_2_vector_is_three() {
        let dist = p3(0, 0, 0).distance(&p3(1, 2, 2)).expect("distance");
        assert!(certified_equal(&dist, &CasExpr::int(3)));
    }

    #[test]
    fn plane_through_three_points_contains_a_fourth_coplanar_point() {
        let plane =
            Plane::through_three_points(&p3(0, 0, 0), &p3(1, 0, 0), &p3(0, 1, 0)).expect("plane");
        assert!(plane.contains(&p3(5, -3, 0)));
        assert!(!plane.contains(&p3(0, 0, 1)));
        assert!(Plane::through_three_points(&p3(0, 0, 0), &p3(1, 0, 0), &p3(2, 0, 0)).is_none());
    }

    #[test]
    fn distance_point_plane_of_the_xy_plane_from_a_unit_height_point() {
        let plane = Plane::new(
            Rational::zero(),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
        )
        .expect("plane");
        let distance = distance_point_plane(&plane, &p3(0, 0, 1)).expect("distance");
        assert!(certified_equal(&distance, &CasExpr::int(1)));
    }

    #[test]
    fn intersection_line_plane_of_the_z_axis_and_the_xy_plane_is_the_origin() {
        let line = Line3::through(&p3(0, 0, -1), &p3(0, 0, 1)).expect("line");
        let plane = Plane::new(
            Rational::zero(),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
        )
        .expect("plane");
        assert_eq!(intersection_line_plane(&line, &plane), Some(p3(0, 0, 0)));
    }

    #[test]
    fn intersection_line_plane_is_none_when_parallel() {
        let line = Line3::through(&p3(0, 0, 1), &p3(1, 0, 1)).expect("line");
        let plane = Plane::new(
            Rational::zero(),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
        )
        .expect("plane");
        assert_eq!(intersection_line_plane(&line, &plane), None);
    }

    #[test]
    fn coplanar_detects_four_points_in_the_xy_plane_and_rejects_a_fifth_off_it() {
        assert!(coplanar(
            &p3(0, 0, 0),
            &p3(1, 0, 0),
            &p3(0, 1, 0),
            &p3(1, 1, 0)
        ));
        assert!(!coplanar(
            &p3(0, 0, 0),
            &p3(1, 0, 0),
            &p3(0, 1, 0),
            &p3(0, 0, 1)
        ));
    }

    #[test]
    fn sphere_through_four_points_recovers_the_unit_sphere() {
        let sphere =
            sphere_through_four_points(&p3(1, 0, 0), &p3(-1, 0, 0), &p3(0, 1, 0), &p3(0, 0, 1))
                .expect("sphere");
        assert_eq!(sphere.center(), p3(0, 0, 0));
        assert_eq!(sphere.radius_squared(), Rational::integer(1));
        assert!(sphere.contains(&p3(0, -1, 0)));
        assert!(!sphere.contains(&p3(1, 1, 1)));
    }

    #[test]
    fn sphere_through_four_points_refuses_coplanar_points() {
        assert!(
            sphere_through_four_points(&p3(0, 0, 0), &p3(1, 0, 0), &p3(0, 1, 0), &p3(1, 1, 0))
                .is_none()
        );
    }

    #[test]
    #[ignore = "measured 922.68s in release (--test-threads=1, this host, 2026-09-05): \
                certify_any_route's linear-block detector is scoped per CONCLUSION, and each \
                per-axis conclusion here ('4 P.x = ...') mentions only one of px,py,pz, while \
                every hypothesis row (a 3D cross-product component) mixes two of the three \
                coordinates -- so the block search cannot see all three unknowns together and \
                falls back to the general (slow) route. A shrunk Limits was tried first \
                (reduction_steps 4_000 vs the default 50_000) and DECLINED outright \
                (Reduction(ReductionSteps)) rather than certifying faster, so the instance \
                could not be cheaply shrunk without changing the certifier itself, which is out \
                of this module's scope. The theorem IS certified: the committed artifact at \
                artifacts/geometry-certificates/tetrahedron-medians-concurrent.json was produced \
                by this same call under the full budget and is re-checked (cheaply, no search) \
                by the `geometry_certificate_artifacts` integration suite on every run. Run this \
                test explicitly with `--ignored` to re-derive it from scratch."]
    fn tetrahedron_medians_concurrent_certifies_and_checks() {
        let problem = tetrahedron_medians_concurrent_problem();
        let outcome = certify_any_route(&problem, geometry_limits());
        let certificate = match outcome {
            crate::geometry_certify::ProofOutcome::Certified(certificate) => certificate,
            other => panic!("expected a certificate, got {other:?}"),
        };
        assert!(check_certificate(&certificate, &CheckOptions::default()).is_verified());
    }

    #[test]
    fn tetrahedron_circumcenter_certifies_and_checks() {
        let problem = tetrahedron_circumcenter_problem();
        let outcome = certify_any_route(&problem, geometry_limits());
        let certificate = match outcome {
            crate::geometry_certify::ProofOutcome::Certified(certificate) => certificate,
            other => panic!("expected a certificate, got {other:?}"),
        };
        assert!(check_certificate(&certificate, &CheckOptions::default()).is_verified());
    }

    // --- Homogeneous coordinates --------------------------------------------

    #[test]
    fn join_of_two_axis_points_is_the_line_through_them() {
        let origin = HPoint::finite(Rational::zero(), Rational::zero());
        let unit_x = HPoint::finite(Rational::integer(1), Rational::zero());
        let line = join(&origin, &unit_x).expect("join");
        assert!(line.contains(&HPoint::finite(Rational::integer(5), Rational::zero())));
        assert!(!line.contains(&HPoint::finite(Rational::zero(), Rational::integer(1))));
    }

    #[test]
    fn meet_of_two_parallel_lines_is_a_point_at_infinity() {
        let horizontal = join(
            &HPoint::finite(Rational::zero(), Rational::zero()),
            &HPoint::finite(Rational::integer(1), Rational::zero()),
        )
        .expect("join");
        let shifted = join(
            &HPoint::finite(Rational::zero(), Rational::integer(1)),
            &HPoint::finite(Rational::integer(1), Rational::integer(1)),
        )
        .expect("join");
        let at_infinity = meet(&horizontal, &shifted).expect("meet");
        assert!(at_infinity.is_infinite());
    }

    #[test]
    fn join_of_coincident_points_is_none() {
        let point = HPoint::finite(Rational::integer(2), Rational::integer(3));
        assert!(join(&point, &point).is_none());
    }

    #[test]
    fn to_affine_divides_by_w_and_is_none_at_infinity() {
        let point = HPoint::new(
            Rational::integer(4),
            Rational::integer(6),
            Rational::integer(2),
        );
        assert_eq!(point.to_affine(), Some(p(2, 3)));
        assert_eq!(
            HPoint::at_infinity(Rational::integer(1), Rational::integer(0)).to_affine(),
            None
        );
    }

    // --- Isometries ----------------------------------------------------------

    #[test]
    fn a_pythagorean_rotation_maps_the_x_axis_point_correctly() {
        // (3/5, 4/5): a 3-4-5 Pythagorean angle.
        let cos = Rational::new(3, 5);
        let sin = Rational::new(4, 5);
        let rotation = Isometry::rotation(cos, sin).expect("orthogonal");
        let image = rotation.apply(&p(5, 0)).expect("apply");
        assert_eq!(image, p(3, 4));
        assert_eq!(rotation.classify(), Some(IsometryKind::Rotation(p(0, 0))));
    }

    #[test]
    fn a_reflection_fixes_its_axis_and_classifies_as_reflection() {
        // Reflection about the x-axis: cos=1, sin=0.
        let reflection =
            Isometry::reflection_through_origin(Rational::integer(1), Rational::zero())
                .expect("orthogonal");
        assert_eq!(reflection.apply(&p(3, 4)), Some(p(3, -4)));
        assert_eq!(reflection.apply(&p(7, 0)), Some(p(7, 0)));
        assert!(matches!(
            reflection.classify(),
            Some(IsometryKind::Reflection(_))
        ));
    }

    #[test]
    fn a_reflection_composed_with_a_translation_along_its_axis_is_a_glide() {
        let reflection =
            Isometry::reflection_through_origin(Rational::integer(1), Rational::zero())
                .expect("orthogonal");
        let glide = reflection
            .translate(Rational::integer(2), Rational::zero())
            .expect("translate");
        assert!(matches!(glide.classify(), Some(IsometryKind::Glide(_))));
        // A translation purely PERPENDICULAR to the axis stays a pure reflection.
        let still_reflection = reflection
            .translate(Rational::zero(), Rational::integer(2))
            .expect("translate");
        assert!(matches!(
            still_reflection.classify(),
            Some(IsometryKind::Reflection(_))
        ));
    }

    #[test]
    fn compose_of_two_pythagorean_rotations_is_a_rotation() {
        let first =
            Isometry::rotation(Rational::new(3, 5), Rational::new(4, 5)).expect("orthogonal");
        let second =
            Isometry::rotation(Rational::new(3, 5), Rational::new(-4, 5)).expect("orthogonal");
        let composed = first.compose(&second).expect("compose");
        // (3/5,4/5) composed with its conjugate is the identity rotation.
        assert_eq!(composed.classify(), Some(IsometryKind::Translation));
        assert_eq!(composed.apply(&p(1, 1)), Some(p(1, 1)));
    }

    #[test]
    fn inverse_of_a_pythagorean_rotation_undoes_it() {
        let rotation =
            Isometry::rotation(Rational::new(3, 5), Rational::new(4, 5)).expect("orthogonal");
        let inverse = rotation.inverse().expect("inverse");
        let round_trip = inverse
            .apply(&rotation.apply(&p(11, -2)).expect("apply"))
            .expect("apply");
        assert_eq!(round_trip, p(11, -2));
    }

    #[test]
    fn a_non_orthogonal_matrix_is_refused() {
        let refusal = Isometry::new(
            Rational::integer(2),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
        )
        .expect_err("scaling is not an isometry");
        assert_eq!(refusal, IsometryRefusal::NotOrthogonal);
    }

    #[test]
    fn isometry_preserves_distance_certificate_verifies_for_a_rotation_reflection_and_glide() {
        let rotation =
            Isometry::rotation(Rational::new(3, 5), Rational::new(4, 5)).expect("orthogonal");
        assert!(certify_preserves_distance(&rotation).verify());
        let reflection =
            Isometry::reflection_through_origin(Rational::integer(1), Rational::zero())
                .expect("orthogonal");
        assert!(certify_preserves_distance(&reflection).verify());
        let glide = reflection
            .translate(Rational::integer(2), Rational::zero())
            .expect("translate");
        assert!(certify_preserves_distance(&glide).verify());
    }

    #[test]
    fn certify_preserves_distance_is_a_real_check_it_can_reject() {
        // A deliberately WRONG "certificate" built by hand from a non-isometry
        // scaling map must not verify: this is the forged-certificate control.
        let px = CasExpr::Var("px".into());
        let py = CasExpr::Var("py".into());
        let qx = CasExpr::Var("qx".into());
        let qy = CasExpr::Var("qy".into());
        let dx = px.clone() - qx.clone();
        let dy = py.clone() - qy.clone();
        let dist_sq_before = dx.clone() * dx + dy.clone() * dy;
        let scale = CasExpr::int(2);
        let sdx = (px * scale.clone()) - (qx * scale.clone());
        let sdy = (py * scale.clone()) - (qy * scale);
        let dist_sq_after = sdx.clone() * sdx + sdy.clone() * sdy;
        let forged = DistancePreservingCertificate {
            difference: dist_sq_after - dist_sq_before,
        };
        assert!(!forged.verify());
    }

    // --- Forged-certificate refusals (distinct reasons) ---------------------

    #[test]
    fn a_point_not_on_a_conic_is_refused_by_on_conic_with_a_distinct_reason_from_overflow() {
        let conic = Conic::new(
            Rational::integer(1),
            Rational::zero(),
            Rational::integer(1),
            Rational::zero(),
            Rational::zero(),
            Rational::integer(-1),
        );
        assert!(!conic.on_conic(&p(2, 2)));
    }

    #[test]
    fn a_swapped_saturation_condition_on_a_tampered_certificate_is_rejected_with_a_generator_reason()
     {
        let problem = tetrahedron_circumcenter_problem();
        let outcome = certify_any_route(&problem, geometry_limits());
        let mut certificate = match outcome {
            crate::geometry_certify::ProofOutcome::Certified(certificate) => *certificate,
            other => panic!("expected a certificate, got {other:?}"),
        };
        // Forge: perturb a cofactor by one.
        let bumped = certificate.conclusions[0].cofactors[0]
            .add(&MvPoly::constant(Rational::integer(1)))
            .expect("perturb");
        certificate.conclusions[0].cofactors[0] = bumped;
        assert!(!check_certificate(&certificate, &CheckOptions::default()).is_verified());
    }

    // --- Frontier: stated but not certified ----------------------------------

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
    }

    #[test]
    fn every_beyond_frontier_witness_is_consistent() {
        let entries = beyond_frontier();
        assert_eq!(entries.len(), 2);
        for problem in &entries {
            witnesses_are_consistent(problem);
            assert!(
                !problem.conclusions.is_empty(),
                "{}: concludes nothing",
                problem.id
            );
        }
    }

    #[test]
    fn pascal_and_desargues_decline_under_a_small_bounded_search() {
        // A DELIBERATELY small budget, so this stays fast in the committed
        // gate: this is not a claim that the theorems are false, only that
        // they are not reached by this route within a small ceiling. See the
        // module doc for the larger picture.
        let small = Limits {
            reduction_steps: 200,
            pair_iterations: 50,
            basis_size: 20,
            poly_terms: 500,
            order: crate::groebner::MonomialOrder::DegRevLex,
        };
        for problem in beyond_frontier() {
            let outcome = certify_any_route(&problem, small);
            assert!(
                !matches!(outcome, crate::geometry_certify::ProofOutcome::Certified(_)),
                "{}: certified faster than expected under a deliberately small budget -- if this \
                 starts passing, promote the theorem to `crate::geometry_corpus::corpus` with a \
                 committed artifact instead of leaving it here",
                problem.id
            );
        }
    }
}
