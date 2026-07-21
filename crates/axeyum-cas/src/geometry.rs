//! Analytic geometry over exact rational coordinates — a small, self-contained
//! `geometry` fragment in the spirit of a computer-algebra geometry module.
//!
//! Every point lives in the plane with exact [`Rational`] coordinates, so all
//! positional predicates (collinearity, incidence, parallelism, intersection)
//! are decided **exactly** by rational arithmetic — no floating point, no
//! tolerance. Distances are the one quantity that leaves the rational field
//! (they involve a square root), so they are returned as an exact [`CasExpr`]
//! with the surd simplified to lowest terms via [`crate::simplify_radicals`]
//! (for example `distance((0,0),(3,4)) = 5` and `distance((0,0),(1,1)) = √2`).
//! Everything else stays inside [`Rational`].
//!
//! Overflow of the underlying `i128` rational arithmetic is reported honestly:
//! predicate-shaped constructors return `None`, and the total numeric helpers
//! panic as a documented usage error (the crate's bounded-arithmetic stance).

use axeyum_ir::Rational;

use crate::{CasExpr, simplify_radicals};

/// A point in the plane with exact rational coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point {
    x: Rational,
    y: Rational,
}

impl Point {
    /// The point `(x, y)`.
    #[must_use]
    pub fn new(x: Rational, y: Rational) -> Point {
        Point { x, y }
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

    /// The Euclidean distance `√((Δx)² + (Δy)²)` to `other`, as an exact
    /// [`CasExpr`] with the surd simplified (a perfect square collapses to a
    /// rational constant, e.g. `√25 → 5`; otherwise a reduced radical such as
    /// `√2` is returned). `None` on `i128` rational overflow.
    #[must_use]
    pub fn distance(&self, other: &Point) -> Option<CasExpr> {
        let dx = other.x.checked_sub(self.x)?;
        let dy = other.y.checked_sub(self.y)?;
        let sum = dx.checked_mul(dx)?.checked_add(dy.checked_mul(dy)?)?;
        Some(simplify_radicals(&CasExpr::Const(sum).sqrt()))
    }

    /// The midpoint of the segment from `self` to `other`.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow while averaging the coordinates (a usage error
    /// under the crate's bounded-arithmetic stance).
    #[must_use]
    pub fn midpoint(&self, other: &Point) -> Point {
        Point {
            x: average(self.x, other.x).expect("midpoint coordinate overflow"),
            y: average(self.y, other.y).expect("midpoint coordinate overflow"),
        }
    }

    /// The slope `Δy / Δx` of the segment from `self` to `other`, or `None` for
    /// a vertical segment (`Δx = 0`) or on `i128` overflow.
    #[must_use]
    pub fn slope(&self, other: &Point) -> Option<Rational> {
        let dx = other.x.checked_sub(self.x)?;
        if dx.is_zero() {
            return None;
        }
        other.y.checked_sub(self.y)?.checked_div(dx)
    }

    /// Whether `a`, `b`, `c` are collinear, decided by the zero cross-product
    /// `(b − a) × (c − a) = 0`. Overflow is treated conservatively as
    /// not-collinear.
    #[must_use]
    pub fn collinear(a: &Point, b: &Point, c: &Point) -> bool {
        cross(a, b, c).is_some_and(Rational::is_zero)
    }

    /// The unsigned area of triangle `a b c`, via the shoelace / cross-product
    /// formula `½·|(b − a) × (c − a)|`. Exact.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow while forming the cross-product or halving it
    /// (a usage error under the crate's bounded-arithmetic stance).
    #[must_use]
    pub fn triangle_area(a: &Point, b: &Point, c: &Point) -> Rational {
        let twice = cross(a, b, c).expect("triangle-area cross-product overflow");
        let magnitude = if twice.numerator() < 0 {
            twice
                .checked_neg()
                .expect("triangle-area magnitude overflow")
        } else {
            twice
        };
        magnitude
            .checked_div(Rational::integer(2))
            .expect("triangle-area halving overflow")
    }
}

/// The average `(a + b) / 2`, or `None` on `i128` overflow.
fn average(a: Rational, b: Rational) -> Option<Rational> {
    a.checked_add(b)?.checked_div(Rational::integer(2))
}

/// The scalar cross-product `(first − origin) × (second − origin)`, or `None`
/// on `i128` overflow.
fn cross(origin: &Point, first: &Point, second: &Point) -> Option<Rational> {
    let ax = first.x.checked_sub(origin.x)?;
    let ay = first.y.checked_sub(origin.y)?;
    let bx = second.x.checked_sub(origin.x)?;
    let by = second.y.checked_sub(origin.y)?;
    ax.checked_mul(by)?.checked_sub(ay.checked_mul(bx)?)
}

/// The 2×2 determinant `a1·b2 − b1·a2`, or `None` on `i128` overflow.
fn det2(a1: Rational, b1: Rational, a2: Rational, b2: Rational) -> Option<Rational> {
    a1.checked_mul(b2)?.checked_sub(b1.checked_mul(a2)?)
}

/// A line in the plane, stored as the coefficients of `a·x + b·y + c = 0` with
/// `(a, b) ≠ (0, 0)`. The representation is exact but **not** normalized to a
/// canonical scale, so equal lines may carry proportional coefficients; the
/// geometric predicates ([`Line::is_parallel`], [`Line::contains`], …) are
/// invariant under that scaling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Line {
    a: Rational,
    b: Rational,
    c: Rational,
}

impl Line {
    /// The line through the distinct points `p` and `q`, or `None` if `p == q`
    /// (no unique line) or on `i128` overflow.
    #[must_use]
    pub fn through(start: &Point, end: &Point) -> Option<Line> {
        let a = start.y.checked_sub(end.y)?;
        let b = end.x.checked_sub(start.x)?;
        if a.is_zero() && b.is_zero() {
            return None;
        }
        // c = −(a·start.x + b·start.y), so that `start` (and hence `end`) lies
        // on the line.
        let c = a
            .checked_mul(start.x)?
            .checked_add(b.checked_mul(start.y)?)?
            .checked_neg()?;
        Some(Line { a, b, c })
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

    /// The constant term.
    #[must_use]
    pub fn c(&self) -> Rational {
        self.c
    }

    /// The value `a·p.x + b·p.y + c`, or `None` on `i128` overflow.
    fn eval_at(&self, p: &Point) -> Option<Rational> {
        self.a
            .checked_mul(p.x)?
            .checked_add(self.b.checked_mul(p.y)?)?
            .checked_add(self.c)
    }

    /// Whether the point `p` lies on this line. Overflow is treated
    /// conservatively as not-incident.
    #[must_use]
    pub fn contains(&self, p: &Point) -> bool {
        self.eval_at(p).is_some_and(Rational::is_zero)
    }

    /// Whether this line is parallel to `other`, i.e. their normals are
    /// proportional (`a1·b2 − a2·b1 = 0`). Coincident lines count as parallel.
    #[must_use]
    pub fn is_parallel(&self, other: &Line) -> bool {
        det2(self.a, self.b, other.a, other.b).is_some_and(Rational::is_zero)
    }

    /// Whether this line is perpendicular to `other`, i.e. their normals are
    /// orthogonal (`a1·a2 + b1·b2 = 0`).
    #[must_use]
    pub fn is_perpendicular(&self, other: &Line) -> bool {
        let dot = self
            .a
            .checked_mul(other.a)
            .and_then(|term| term.checked_add(self.b.checked_mul(other.b)?));
        dot.is_some_and(Rational::is_zero)
    }

    /// The intersection point of this line and `other`, or `None` if they are
    /// parallel (including coincident) or on `i128` overflow.
    #[must_use]
    pub fn intersection(&self, other: &Line) -> Option<Point> {
        let det = det2(self.a, self.b, other.a, other.b)?;
        if det.is_zero() {
            return None;
        }
        // Cramer's rule on { a1·x + b1·y = −c1 , a2·x + b2·y = −c2 }.
        let x_num = self
            .b
            .checked_mul(other.c)?
            .checked_sub(other.b.checked_mul(self.c)?)?;
        let y_num = other
            .a
            .checked_mul(self.c)?
            .checked_sub(self.a.checked_mul(other.c)?)?;
        Some(Point {
            x: x_num.checked_div(det)?,
            y: y_num.checked_div(det)?,
        })
    }
}

/// A circle, stored as its center and its exact **squared** radius (the radius
/// itself is generally irrational, but the squared radius stays rational).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Circle {
    center: Point,
    radius_squared: Rational,
}

impl Circle {
    /// The circle circumscribing the triangle `a b c` (passing through all
    /// three), or `None` if the points are collinear (no finite circumcircle)
    /// or on `i128` overflow.
    #[must_use]
    pub fn through_three(a: &Point, b: &Point, c: &Point) -> Option<Circle> {
        let ax = a.x;
        let ay = a.y;
        let bx = b.x;
        let by = b.y;
        let cx = c.x;
        let cy = c.y;
        // det = 2·((b − a) × (c − a)); zero exactly when the points are collinear.
        let det = cyclic(ax, bx, cx, ay, by, cy)?.checked_mul(Rational::integer(2))?;
        if det.is_zero() {
            return None;
        }
        // Squared magnitudes of the three points.
        let na = ax.checked_mul(ax)?.checked_add(ay.checked_mul(ay)?)?;
        let nb = bx.checked_mul(bx)?.checked_add(by.checked_mul(by)?)?;
        let nc = cx.checked_mul(cx)?.checked_add(cy.checked_mul(cy)?)?;
        // Circumcenter by the standard determinant formulae.
        let ux = cyclic(na, nb, nc, ay, by, cy)?.checked_div(det)?;
        let uy = cyclic(na, nb, nc, ax, bx, cx)?
            .checked_neg()?
            .checked_div(det)?;
        let center = Point { x: ux, y: uy };
        let rx = ax.checked_sub(ux)?;
        let ry = ay.checked_sub(uy)?;
        let radius_squared = rx.checked_mul(rx)?.checked_add(ry.checked_mul(ry)?)?;
        Some(Circle {
            center,
            radius_squared,
        })
    }

    /// The center of the circle.
    #[must_use]
    pub fn center(&self) -> Point {
        self.center
    }

    /// The squared radius of the circle.
    #[must_use]
    pub fn radius_squared(&self) -> Rational {
        self.radius_squared
    }

    /// The squared distance from the center to `p`, or `None` on overflow.
    fn squared_distance_to(&self, p: &Point) -> Option<Rational> {
        let dx = p.x.checked_sub(self.center.x)?;
        let dy = p.y.checked_sub(self.center.y)?;
        dx.checked_mul(dx)?.checked_add(dy.checked_mul(dy)?)
    }

    /// Whether the point `p` lies exactly on this circle. Overflow is treated
    /// conservatively as not-incident.
    #[must_use]
    pub fn contains(&self, p: &Point) -> bool {
        self.squared_distance_to(p) == Some(self.radius_squared)
    }
}

/// The cyclic combination `n1·(u2 − u3) + n2·(u3 − u1) + n3·(u1 − u2)`, or
/// `None` on `i128` overflow. Building block for the circumcenter and the
/// (twice-)area determinant.
fn cyclic(
    n1: Rational,
    n2: Rational,
    n3: Rational,
    u1: Rational,
    u2: Rational,
    u3: Rational,
) -> Option<Rational> {
    let t1 = n1.checked_mul(u2.checked_sub(u3)?)?;
    let t2 = n2.checked_mul(u3.checked_sub(u1)?)?;
    let t3 = n3.checked_mul(u1.checked_sub(u2)?)?;
    t1.checked_add(t2)?.checked_add(t3)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ZeroTest, equal};

    /// An integer-coordinate point, for concise fixtures.
    fn p(x: i128, y: i128) -> Point {
        Point::new(Rational::integer(x), Rational::integer(y))
    }

    /// Certified equality of two `CasExpr` values.
    fn certified_equal(a: &CasExpr, b: &CasExpr) -> bool {
        matches!(equal(a, b), ZeroTest::Certified { equal: true, .. })
    }

    #[test]
    fn distance_of_a_3_4_5_triangle_is_the_integer_5() {
        let dist = p(0, 0).distance(&p(3, 4)).unwrap();
        assert!(certified_equal(&dist, &CasExpr::int(5)));
    }

    #[test]
    fn distance_of_the_unit_diagonal_is_root_two() {
        let dist = p(0, 0).distance(&p(1, 1)).unwrap();
        assert!(certified_equal(&dist, &CasExpr::int(2).sqrt()));
    }

    #[test]
    fn midpoint_is_the_coordinatewise_average() {
        assert_eq!(p(0, 0).midpoint(&p(2, 4)), p(1, 2));
    }

    #[test]
    fn slope_is_rise_over_run_and_none_when_vertical() {
        assert_eq!(p(0, 0).slope(&p(2, 1)), Some(Rational::new(1, 2)));
        assert_eq!(p(0, 0).slope(&p(0, 5)), None);
    }

    #[test]
    fn collinearity_via_the_zero_cross_product() {
        assert!(Point::collinear(&p(0, 0), &p(1, 1), &p(2, 2)));
        assert!(!Point::collinear(&p(0, 0), &p(1, 1), &p(2, 3)));
    }

    #[test]
    fn line_through_two_points_contains_a_third_on_it() {
        let line = Line::through(&p(0, 0), &p(1, 1)).unwrap();
        assert!(line.contains(&p(2, 2)));
        assert!(!line.contains(&p(2, 3)));
        // Degenerate: no unique line through a repeated point.
        assert!(Line::through(&p(1, 1), &p(1, 1)).is_none());
    }

    #[test]
    fn parallel_and_perpendicular_predicates() {
        let diagonal = Line::through(&p(0, 0), &p(1, 1)).unwrap(); // y = x
        let shifted = Line::through(&p(0, 1), &p(1, 2)).unwrap(); // y = x + 1
        let anti = Line::through(&p(0, 0), &p(1, -1)).unwrap(); // y = -x
        assert!(diagonal.is_parallel(&shifted));
        assert!(!diagonal.is_parallel(&anti));
        assert!(diagonal.is_perpendicular(&anti));
        assert!(!diagonal.is_perpendicular(&shifted));
        // Parallel lines do not intersect.
        assert_eq!(diagonal.intersection(&shifted), None);
    }

    #[test]
    fn intersection_of_the_axes_is_the_origin() {
        let horizontal = Line::through(&p(0, 0), &p(1, 0)).unwrap(); // the x-axis
        let vertical = Line::through(&p(0, 0), &p(0, 1)).unwrap(); // the y-axis
        assert_eq!(horizontal.intersection(&vertical), Some(p(0, 0)));
    }

    #[test]
    fn triangle_area_via_the_shoelace_formula() {
        assert_eq!(
            Point::triangle_area(&p(0, 0), &p(4, 0), &p(0, 3)),
            Rational::integer(6)
        );
    }

    #[test]
    fn circumscribed_circle_of_three_points_is_the_unit_circle() {
        let circle = Circle::through_three(&p(1, 0), &p(0, 1), &p(-1, 0)).unwrap();
        assert_eq!(circle.center(), p(0, 0));
        assert_eq!(circle.radius_squared(), Rational::integer(1));
        assert!(circle.contains(&p(0, -1)));
        assert!(!circle.contains(&p(0, 0)));
        // Collinear points have no circumcircle.
        assert!(Circle::through_three(&p(0, 0), &p(1, 0), &p(2, 0)).is_none());
    }
}
