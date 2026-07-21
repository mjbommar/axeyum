//! Sets of real numbers as normalized unions of disjoint rational intervals —
//! the `SymPy` `sets` analogue over the exact-rational core.
//!
//! A [`RealSet`] models a subset of the real line as a canonical, ascending
//! `Vec` of pairwise-disjoint, non-adjacent [`Interval`] pieces. Each piece is a
//! rational interval with independently open or closed endpoints, either of which
//! may be unbounded (`None` meaning `−∞` on the lower side or `+∞` on the upper);
//! a single point `a` is the degenerate closed interval `[a, a]`. Because the
//! representation is normalized to a unique canonical form, structural equality of
//! the piece vectors coincides with set equality, and the Boolean algebra of sets
//! (union, intersection, complement within `ℝ`, difference) is exact and total.
//!
//! All endpoint bookkeeping is exact: `[1, 2]` and `(2, 3]` merge to `[1, 3]`
//! (they share the closed point `2`), whereas `[1, 2)` and `(2, 3]` stay disjoint
//! (neither contains `2`). Arithmetic on endpoints uses the checked `Rational`
//! operations, so an out-of-range measure is reported as `None` rather than a
//! panic or a wrong answer.

use std::cmp::Ordering;

use axeyum_ir::Rational;

/// A single rational interval with independently open or closed endpoints.
///
/// A `None` bound denotes an unbounded side: `lower = None` is `−∞` and
/// `upper = None` is `+∞`. An unbounded side is never "closed" (there is no
/// endpoint to include), so its `*_closed` flag is conventionally `false`. The
/// single point `a` is the degenerate closed interval `[a, a]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    /// The lower endpoint value, or `None` for `−∞`.
    pub lower: Option<Rational>,
    /// Whether the lower endpoint is included (`[`) rather than excluded (`(`).
    pub lower_closed: bool,
    /// The upper endpoint value, or `None` for `+∞`.
    pub upper: Option<Rational>,
    /// Whether the upper endpoint is included (`]`) rather than excluded (`)`).
    pub upper_closed: bool,
}

impl Interval {
    /// The closed interval `[a, b]`.
    #[must_use]
    pub fn closed(a: Rational, b: Rational) -> Interval {
        Interval {
            lower: Some(a),
            lower_closed: true,
            upper: Some(b),
            upper_closed: true,
        }
    }

    /// The open interval `(a, b)`.
    #[must_use]
    pub fn open(a: Rational, b: Rational) -> Interval {
        Interval {
            lower: Some(a),
            lower_closed: false,
            upper: Some(b),
            upper_closed: false,
        }
    }

    /// The half-open interval `[a, b)` (lower closed, upper open).
    #[must_use]
    pub fn closed_open(a: Rational, b: Rational) -> Interval {
        Interval {
            lower: Some(a),
            lower_closed: true,
            upper: Some(b),
            upper_closed: false,
        }
    }

    /// The half-open interval `(a, b]` (lower open, upper closed).
    #[must_use]
    pub fn open_closed(a: Rational, b: Rational) -> Interval {
        Interval {
            lower: Some(a),
            lower_closed: false,
            upper: Some(b),
            upper_closed: true,
        }
    }

    /// The degenerate closed interval `[a, a]` containing exactly the point `a`.
    #[must_use]
    pub fn point(a: Rational) -> Interval {
        Interval::closed(a, a)
    }

    /// The whole real line `(−∞, +∞)`.
    #[must_use]
    pub fn universe() -> Interval {
        Interval {
            lower: None,
            lower_closed: false,
            upper: None,
            upper_closed: false,
        }
    }

    /// Returns `true` if this interval contains no real number.
    ///
    /// Only a bounded interval can be empty: `(a, a)`, `[a, a)`, and `(a, a]` are
    /// empty, and any interval with `lower > upper` is empty. A point `[a, a]` and
    /// any interval with an unbounded side are non-empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        match (self.lower, self.upper) {
            (Some(lv), Some(uv)) => match lv.cmp(&uv) {
                Ordering::Greater => true,
                Ordering::Equal => !(self.lower_closed && self.upper_closed),
                Ordering::Less => false,
            },
            _ => false,
        }
    }

    /// Returns `true` if the real number `x` lies inside this interval, honoring
    /// the open/closed status of each endpoint.
    #[must_use]
    pub fn contains(&self, x: Rational) -> bool {
        let lower_ok = match self.lower {
            None => true,
            Some(lv) => {
                if self.lower_closed {
                    x >= lv
                } else {
                    x > lv
                }
            }
        };
        let upper_ok = match self.upper {
            None => true,
            Some(uv) => {
                if self.upper_closed {
                    x <= uv
                } else {
                    x < uv
                }
            }
        };
        lower_ok && upper_ok
    }
}

/// A subset of the real line as a normalized, ascending union of pairwise-disjoint
/// intervals.
///
/// The invariant maintained by every constructor and operation is that
/// `intervals` is sorted by lower endpoint, contains no empty pieces, and no two
/// pieces overlap or touch (adjacent pieces sharing a closed point are merged).
/// This canonical form makes structural equality equivalent to set equality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealSet {
    /// Disjoint, non-adjacent, ascending interval pieces (the normalized form).
    intervals: Vec<Interval>,
}

impl RealSet {
    /// The empty set `∅`.
    #[must_use]
    pub fn empty() -> RealSet {
        RealSet {
            intervals: Vec::new(),
        }
    }

    /// The set consisting of a single interval (empty if the interval is empty).
    #[must_use]
    pub fn interval(interval: Interval) -> RealSet {
        RealSet::from_intervals(vec![interval])
    }

    /// The singleton set `{a}`.
    #[must_use]
    pub fn point(a: Rational) -> RealSet {
        RealSet::interval(Interval::point(a))
    }

    /// The whole real line `ℝ`.
    #[must_use]
    pub fn universe() -> RealSet {
        RealSet::interval(Interval::universe())
    }

    /// Builds a `RealSet` from arbitrary intervals, normalizing to canonical form:
    /// empty pieces are dropped, pieces are sorted, and overlapping or adjacent
    /// pieces are merged.
    #[must_use]
    pub fn from_intervals(intervals: Vec<Interval>) -> RealSet {
        RealSet {
            intervals: normalize(intervals),
        }
    }

    /// The union `self ∪ other`.
    #[must_use]
    pub fn union(&self, other: &RealSet) -> RealSet {
        let mut pieces = self.intervals.clone();
        pieces.extend(other.intervals.iter().copied());
        RealSet::from_intervals(pieces)
    }

    /// The intersection `self ∩ other`.
    #[must_use]
    pub fn intersection(&self, other: &RealSet) -> RealSet {
        let mut pieces = Vec::new();
        for a in &self.intervals {
            for b in &other.intervals {
                let piece = intersect_intervals(a, b);
                if !piece.is_empty() {
                    pieces.push(piece);
                }
            }
        }
        RealSet::from_intervals(pieces)
    }

    /// The complement `ℝ ∖ self`, taken within the real line.
    #[must_use]
    pub fn complement(&self) -> RealSet {
        if self.intervals.is_empty() {
            return RealSet::universe();
        }
        let mut pieces = Vec::new();
        // The running lower bound for the next gap piece, starting at `−∞`.
        let mut lower: Option<Rational> = None;
        let mut lower_closed = false;
        let mut reached_infinity = false;
        for iv in &self.intervals {
            if iv.lower.is_some() {
                // The gap between the running frontier and this piece's start; the
                // gap's upper endpoint is this piece's lower endpoint, flipped.
                let piece = Interval {
                    lower,
                    lower_closed,
                    upper: iv.lower,
                    upper_closed: !iv.lower_closed,
                };
                if !piece.is_empty() {
                    pieces.push(piece);
                }
            }
            if iv.upper.is_none() {
                // This piece runs to `+∞`; nothing remains to the right.
                reached_infinity = true;
                break;
            }
            lower = iv.upper;
            lower_closed = !iv.upper_closed;
        }
        if !reached_infinity {
            let piece = Interval {
                lower,
                lower_closed,
                upper: None,
                upper_closed: false,
            };
            if !piece.is_empty() {
                pieces.push(piece);
            }
        }
        RealSet::from_intervals(pieces)
    }

    /// The difference `self ∖ other`.
    #[must_use]
    pub fn difference(&self, other: &RealSet) -> RealSet {
        self.intersection(&other.complement())
    }

    /// Returns `true` if the real number `x` belongs to this set.
    #[must_use]
    pub fn contains(&self, x: Rational) -> bool {
        self.intervals.iter().any(|iv| iv.contains(x))
    }

    /// Returns `true` if this set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    /// Returns `true` if every point of `self` is also in `other`.
    #[must_use]
    pub fn is_subset(&self, other: &RealSet) -> bool {
        self.difference(other).is_empty()
    }

    /// Returns `true` if `self` and `other` denote the same set of reals. Because
    /// the representation is canonical, this is exact structural equality.
    #[must_use]
    pub fn is_equal(&self, other: &RealSet) -> bool {
        self.intervals == other.intervals
    }

    /// The total finite length (Lebesgue measure) of this set, or `None` if the
    /// set is unbounded (infinite measure) or the exact sum overflows `i128`.
    /// Isolated points contribute length zero.
    #[must_use]
    pub fn measure(&self) -> Option<Rational> {
        let mut total = Rational::zero();
        for iv in &self.intervals {
            let lv = iv.lower?;
            let uv = iv.upper?;
            let length = uv.checked_sub(lv)?;
            total = total.checked_add(length)?;
        }
        Some(total)
    }

    /// The interval pieces of this set in canonical ascending order.
    #[must_use]
    pub fn intervals(&self) -> &[Interval] {
        &self.intervals
    }
}

/// The finite set `{p₀, p₁, …}` of the given points (duplicates and order do not
/// matter; the result is normalized).
#[must_use]
pub fn finite_set(points: &[Rational]) -> RealSet {
    let pieces = points.iter().map(|&p| Interval::point(p)).collect();
    RealSet::from_intervals(pieces)
}

/// Compares the lower endpoints of two intervals, treating "more to the left" as
/// smaller: `−∞` is smallest, and at an equal value a closed lower endpoint (which
/// includes the point) precedes an open one.
fn cmp_lower_bound(a: &Interval, b: &Interval) -> Ordering {
    match (a.lower, b.lower) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(av), Some(bv)) => av.cmp(&bv).then_with(|| b.lower_closed.cmp(&a.lower_closed)),
    }
}

/// Compares the upper endpoints of two intervals, treating "more to the right" as
/// larger: `+∞` is largest, and at an equal value a closed upper endpoint (which
/// includes the point) exceeds an open one.
fn cmp_upper_bound(a: &Interval, b: &Interval) -> Ordering {
    match (a.upper, b.upper) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(av), Some(bv)) => av.cmp(&bv).then_with(|| a.upper_closed.cmp(&b.upper_closed)),
    }
}

/// Returns `true` if `left` (the piece with the smaller lower endpoint) overlaps
/// or is adjacent to `right`, so the two should merge into one piece. Adjacency
/// requires the shared value to be closed on at least one side.
fn intervals_touch(left: &Interval, right: &Interval) -> bool {
    match (left.upper, right.lower) {
        // `left` extends to `+∞`, or `right` starts at `−∞`: they meet.
        (None, _) | (_, None) => true,
        (Some(uv), Some(lv)) => match uv.cmp(&lv) {
            Ordering::Greater => true,
            Ordering::Equal => left.upper_closed || right.lower_closed,
            Ordering::Less => false,
        },
    }
}

/// The intersection of two intervals: the greater lower endpoint and the lesser
/// upper endpoint. The result may be empty (caller filters via [`Interval::is_empty`]).
fn intersect_intervals(a: &Interval, b: &Interval) -> Interval {
    let (lower, lower_closed) = if cmp_lower_bound(a, b) == Ordering::Greater {
        (a.lower, a.lower_closed)
    } else {
        (b.lower, b.lower_closed)
    };
    let (upper, upper_closed) = if cmp_upper_bound(a, b) == Ordering::Less {
        (a.upper, a.upper_closed)
    } else {
        (b.upper, b.upper_closed)
    };
    Interval {
        lower,
        lower_closed,
        upper,
        upper_closed,
    }
}

/// Normalizes arbitrary intervals into canonical form: drop empty pieces, sort by
/// endpoint, and merge overlapping or adjacent pieces.
fn normalize(mut intervals: Vec<Interval>) -> Vec<Interval> {
    intervals.retain(|iv| !iv.is_empty());
    intervals.sort_by(|a, b| cmp_lower_bound(a, b).then_with(|| cmp_upper_bound(a, b)));
    let mut result: Vec<Interval> = Vec::new();
    for iv in intervals {
        if let Some(last) = result.last_mut()
            && intervals_touch(last, &iv)
        {
            // Extend the running piece to the larger of the two upper endpoints.
            if cmp_upper_bound(last, &iv) == Ordering::Less {
                last.upper = iv.upper;
                last.upper_closed = iv.upper_closed;
            }
            continue;
        }
        result.push(iv);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::{Interval, RealSet, finite_set};
    use axeyum_ir::Rational;

    /// The integer `n` as a rational.
    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }

    #[test]
    fn union_merges_adjacent_shared_closed_point() {
        // [1, 2] ∪ (2, 3] = [1, 3]: they share the closed point 2.
        let a = RealSet::interval(Interval::closed(r(1), r(2)));
        let b = RealSet::interval(Interval::open_closed(r(2), r(3)));
        assert!(a.union(&b).is_equal(&RealSet::interval(Interval::closed(r(1), r(3)))));
    }

    #[test]
    fn union_keeps_disjoint_open_gap() {
        // [1, 2) ∪ (2, 3] stays disjoint: neither piece contains 2.
        let a = RealSet::interval(Interval::closed_open(r(1), r(2)));
        let b = RealSet::interval(Interval::open_closed(r(2), r(3)));
        let u = a.union(&b);
        assert!(!u.is_equal(&RealSet::interval(Interval::closed(r(1), r(3)))));
        assert!(!u.contains(r(2)));
        assert_eq!(u.intervals().len(), 2);
    }

    #[test]
    fn intersection_of_overlapping_closed_intervals() {
        // [0, 2] ∩ [1, 3] = [1, 2].
        let a = RealSet::interval(Interval::closed(r(0), r(2)));
        let b = RealSet::interval(Interval::closed(r(1), r(3)));
        assert!(a.intersection(&b).is_equal(&RealSet::interval(Interval::closed(r(1), r(2)))));
    }

    #[test]
    fn intersection_endpoint_openness_is_exact() {
        // (0, 2] ∩ [2, 3) = [2, 2] = {2}.
        let a = RealSet::interval(Interval::open_closed(r(0), r(2)));
        let b = RealSet::interval(Interval::closed_open(r(2), r(3)));
        assert!(a.intersection(&b).is_equal(&RealSet::point(r(2))));
    }

    #[test]
    fn complement_within_reals() {
        // complement( (−∞, 0] ∪ [1, ∞) ) = (0, 1).
        let s = RealSet::from_intervals(vec![
            Interval {
                lower: None,
                lower_closed: false,
                upper: Some(r(0)),
                upper_closed: true,
            },
            Interval {
                lower: Some(r(1)),
                lower_closed: true,
                upper: None,
                upper_closed: false,
            },
        ]);
        assert!(s.complement().is_equal(&RealSet::interval(Interval::open(r(0), r(1)))));
    }

    #[test]
    fn double_complement_is_identity() {
        let s = RealSet::from_intervals(vec![
            Interval::closed(r(0), r(1)),
            Interval::open(r(3), r(5)),
        ]);
        assert!(s.complement().complement().is_equal(&s));
    }

    #[test]
    fn difference_carves_out_a_closed_middle() {
        // [0, 3] ∖ [1, 2] = [0, 1) ∪ (2, 3].
        let a = RealSet::interval(Interval::closed(r(0), r(3)));
        let b = RealSet::interval(Interval::closed(r(1), r(2)));
        let expect = RealSet::from_intervals(vec![
            Interval::closed_open(r(0), r(1)),
            Interval::open_closed(r(2), r(3)),
        ]);
        assert!(a.difference(&b).is_equal(&expect));
    }

    #[test]
    fn measure_sums_disjoint_lengths() {
        // measure( [0, 1] ∪ [2, 4] ) = 1 + 2 = 3.
        let s = RealSet::from_intervals(vec![
            Interval::closed(r(0), r(1)),
            Interval::closed(r(2), r(4)),
        ]);
        assert_eq!(s.measure(), Some(r(3)));
    }

    #[test]
    fn measure_is_none_when_unbounded() {
        assert_eq!(RealSet::universe().measure(), None);
        let half_line = RealSet::interval(Interval {
            lower: Some(r(0)),
            lower_closed: true,
            upper: None,
            upper_closed: false,
        });
        assert_eq!(half_line.measure(), None);
    }

    #[test]
    fn contains_respects_endpoints() {
        let s = RealSet::interval(Interval::open_closed(r(0), r(2)));
        assert!(!s.contains(r(0)));
        assert!(s.contains(Rational::new(1, 2)));
        assert!(s.contains(r(2)));
        assert!(!s.contains(r(3)));
    }

    #[test]
    fn de_morgan_complement_of_union() {
        // complement(A ∪ B) = complement(A) ∩ complement(B).
        let a = RealSet::interval(Interval::closed(r(0), r(2)));
        let b = RealSet::interval(Interval::closed(r(1), r(3)));
        let lhs = a.union(&b).complement();
        let rhs = a.complement().intersection(&b.complement());
        assert!(lhs.is_equal(&rhs));
    }

    #[test]
    fn subset_and_equality() {
        let a = RealSet::interval(Interval::closed(r(1), r(2)));
        let b = RealSet::interval(Interval::closed(r(0), r(3)));
        assert!(a.is_subset(&b));
        assert!(!b.is_subset(&a));
        assert!(a.is_equal(&a));
        assert!(a.union(&b).is_equal(&b));
        // Openness matters for subset: (1, 2) ⊆ [1, 2] but not conversely.
        let open = RealSet::interval(Interval::open(r(1), r(2)));
        let closed = RealSet::interval(Interval::closed(r(1), r(2)));
        assert!(open.is_subset(&closed));
        assert!(!closed.is_subset(&open));
    }

    #[test]
    fn point_merges_into_adjacent_open_interval() {
        // {2} ∪ (2, 3] = [2, 3]: the closed point closes the open lower end.
        let s = RealSet::from_intervals(vec![
            Interval::point(r(2)),
            Interval::open_closed(r(2), r(3)),
        ]);
        assert!(s.is_equal(&RealSet::interval(Interval::closed(r(2), r(3)))));
    }

    #[test]
    fn finite_set_has_zero_measure() {
        let s = finite_set(&[r(1), r(2), r(3)]);
        assert_eq!(s.intervals().len(), 3);
        assert_eq!(s.measure(), Some(Rational::zero()));
        assert!(s.contains(r(2)));
        assert!(!s.contains(Rational::new(3, 2)));
    }

    #[test]
    fn universe_and_empty_edge_cases() {
        assert!(RealSet::empty().is_empty());
        assert_eq!(RealSet::empty().measure(), Some(Rational::zero()));
        assert!(RealSet::empty().complement().is_equal(&RealSet::universe()));
        assert!(RealSet::universe().complement().is_empty());
        assert!(RealSet::universe().contains(Rational::new(-5, 7)));
        // Intersecting with the empty set annihilates; union with it is identity.
        let a = RealSet::interval(Interval::closed(r(0), r(1)));
        assert!(a.intersection(&RealSet::empty()).is_empty());
        assert!(a.union(&RealSet::empty()).is_equal(&a));
    }
}
