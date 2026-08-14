//! Van der Waerden numbers `w(r; k_1, …, k_r)`, diagonal and off-diagonal.
//!
//! An **arithmetic progression** of length `k` inside `[1, n]` is a set
//! `{a, a + d, …, a + (k − 1)d}` with `d >= 1`. Van der Waerden's theorem says
//! that for any `k_1, …, k_r` there is a least `N` such that every
//! `r`-colouring of `[1, N]` has, for **some** colour `c`, a monochromatic
//! progression of length `k_c` in colour `c`. That least `N` is
//! `w(r; k_1, …, k_r)`; when every `k_c` is the same `k` it is the *diagonal*
//! number, written `W(r, k)` here.
//!
//! The off-diagonal row `w(2; 3, t)` — colour 1 avoids 3-term progressions,
//! colour 2 avoids `t`-term progressions — is off-diagonal by nature and is the
//! reason this family exists in a crate whose per-colour machinery was built
//! for [`OffDiagonalSchur`](crate::offdiag::OffDiagonalSchur).
//!
//! # Symmetry breaking: the distinction is explicit, not incidental
//!
//! Colour classes may be ordered by least element only between colours that
//! forbid the same sets. This family therefore reports
//! [`ColouringFamily::colour_dependent`] as `false` exactly when every `k_c` is
//! equal — the diagonal case, where the colours *are* interchangeable, the
//! stock uniform encoder applies, and the full whole-palette symmetry break is
//! available and worth a lot — and `true` otherwise, where
//! [`ColouringFamily::symmetry_blocks`] hands the encoder the colours grouped
//! by progression length. For `w(2; 3, t)` with `t != 3` those blocks are
//! `{1}` and `{2}`: **no** colour symmetry at all. Inheriting the default
//! whole-palette break there would delete genuine colourings and report a wrong
//! `unsat`; `tests/vdw.rs` carries the negative control that fires.
//!
//! # Subsumption does not apply here, and that is worth knowing
//!
//! The off-diagonal Schur family is dominated by a subsumption reduction: for
//! `S ⊆ S'` the clause over `S` implies the clause over `S'`, and on `L(8)`
//! over `[1,87]` that removes 97% of the clauses. **It removes nothing here.**
//! Every progression of length `k` is a set of exactly `k` distinct points, so
//! no two of them nest, and a progression is determined by its set (its least
//! two elements give `a` and `d`), so there are no duplicates either. The
//! forbidden list of one colour is already a subsumption-minimal antichain.
//! [`VanDerWaerden::subsumed_pair`] measures this rather than asserting it, and
//! `progressions_are_already_an_antichain` runs it.
//!
//! The consequence is that the clause count is exactly the progression count,
//! `Σ_d (n − (k−1)d)`, which is `O(n² / k)` and tiny: `w(2; 3, 20)` at
//! `n = 388` is about 41,000 clauses over 776 variables. This family is
//! **solver-bound**, not encoder-bound — the exact opposite of the Schur one.

use crate::SearchError;
use crate::colouring::ColouringProblem;
use crate::family::ColouringFamily;

/// Largest `n` this family will build an instance for.
///
/// `w(2; 6, 6) = 1132` is the largest van der Waerden number known exactly, so
/// this leaves room above every value in the literature while still refusing a
/// typo that would try to allocate for millions of points.
pub const MAX_POINTS: usize = 4096;

/// The van der Waerden family: colour `c` must avoid progressions of length
/// `k[c - 1]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VanDerWaerden {
    k: Vec<usize>,
}

impl VanDerWaerden {
    /// Builds the family from one progression length per colour.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] for an empty list or any
    /// `k_c < 3`. Length 2 would forbid every pair of same-coloured points,
    /// which is a graph-colouring problem and not this family; length 1 is
    /// vacuous.
    pub fn new(k: Vec<usize>) -> Result<Self, SearchError> {
        if k.is_empty() {
            return Err(SearchError::InvalidParameter {
                what: "van der Waerden needs at least one colour".to_string(),
            });
        }
        if let Some(&bad) = k.iter().find(|&&value| value < 3) {
            return Err(SearchError::InvalidParameter {
                what: format!("van der Waerden needs every k >= 3, got {bad}"),
            });
        }
        Ok(Self { k })
    }

    /// The diagonal family `W(colours, k)`: every colour avoids the same
    /// progression length.
    ///
    /// # Errors
    ///
    /// As [`VanDerWaerden::new`], plus [`SearchError::InvalidParameter`] for
    /// zero colours.
    pub fn diagonal(colours: usize, k: usize) -> Result<Self, SearchError> {
        if colours == 0 {
            return Err(SearchError::InvalidParameter {
                what: "van der Waerden needs at least one colour".to_string(),
            });
        }
        Self::new(vec![k; colours])
    }

    /// The two-colour off-diagonal family `w(2; k1, k2)`.
    ///
    /// # Errors
    ///
    /// As [`VanDerWaerden::new`].
    pub fn off_diagonal(k1: usize, k2: usize) -> Result<Self, SearchError> {
        Self::new(vec![k1, k2])
    }

    /// The progression length of each colour, `k()[c - 1]` for colour `c`.
    pub fn k(&self) -> &[usize] {
        &self.k
    }

    /// Whether every colour forbids the same progression length.
    pub fn is_diagonal(&self) -> bool {
        self.k.iter().all(|&value| value == self.k[0])
    }

    /// Every arithmetic progression of length `k` inside `1..=points`, in
    /// encoding order: common difference ascending, then first term ascending.
    ///
    /// The order is part of the encoding contract, so a stored CNF regenerates
    /// byte for byte.
    pub fn progressions(k: usize, points: usize) -> Vec<Vec<usize>> {
        let mut sets = Vec::new();
        if k < 2 || points == 0 {
            return sets;
        }
        let span = k - 1;
        let mut step = 1usize;
        while span * step < points {
            let last_start = points - span * step;
            for start in 1..=last_start {
                sets.push((0..k).map(|term| start + term * step).collect());
            }
            step += 1;
        }
        sets
    }

    /// The number of length-`k` progressions inside `1..=points`, in closed
    /// form: `Σ_{d >= 1} (n − (k−1)d)` over the `d` with `(k−1)d < n`.
    ///
    /// Kept separate from [`VanDerWaerden::progressions`] so that
    /// `progression_count_matches_the_enumeration` can compare a formula
    /// against an enumeration instead of comparing an enumeration with itself.
    pub fn progression_count(k: usize, points: usize) -> usize {
        if k < 2 || points == 0 {
            return 0;
        }
        let span = k - 1;
        let steps = (points - 1) / span;
        // Σ_{d=1}^{steps} (points − span·d).
        steps * points - span * steps * (steps + 1) / 2
    }

    /// A pair of distinct length-`k` progressions inside `1..=points` where the
    /// first is a subset of the second, if one exists.
    ///
    /// This is a **measurement**, not an assertion: it is the question "does
    /// the subsumption reduction that carried the off-diagonal Schur family
    /// have anything to remove here?" asked of the actual sets. It is `O(N²)`
    /// in the number of progressions, so it is for small instances and tests.
    pub fn subsumed_pair(k: usize, points: usize) -> Option<(Vec<usize>, Vec<usize>)> {
        let sets = Self::progressions(k, points);
        for (i, left) in sets.iter().enumerate() {
            for right in sets.iter().skip(i + 1) {
                if left.iter().all(|point| right.contains(point)) {
                    return Some((left.clone(), right.clone()));
                }
                if right.iter().all(|point| left.contains(point)) {
                    return Some((right.clone(), left.clone()));
                }
            }
        }
        None
    }

    /// The colours grouped by progression length: colours `c` and `c'` land in
    /// the same block exactly when `k_c == k_{c'}`, and only those are
    /// interchangeable.
    ///
    /// Blocks are ordered by their least colour and each block is ascending.
    pub fn parameter_blocks(&self) -> Vec<Vec<usize>> {
        let mut blocks: Vec<(usize, Vec<usize>)> = Vec::new();
        for (index, &value) in self.k.iter().enumerate() {
            let colour = index + 1;
            match blocks.iter_mut().find(|(parameter, _)| *parameter == value) {
                Some((_, members)) => members.push(colour),
                None => blocks.push((value, vec![colour])),
            }
        }
        blocks.into_iter().map(|(_, members)| members).collect()
    }

    /// The value this family has in the literature, or `None` when it is not a
    /// published cell.
    ///
    /// **This is a reference, never evidence.** Nothing in this crate consults
    /// it to decide anything; it exists so a run can label its own verdict
    /// `reproduces published` or `new` without the caller retyping a table.
    /// A disagreement between this table and a decided instance is an
    /// emergency, and `published_values_are_only_a_label` is the test that says
    /// so.
    ///
    /// Sources:
    ///
    /// * the seven exactly-known diagonal numbers — `W(2,3) = 9`,
    ///   `W(3,3) = 27`, `W(4,3) = 76`, `W(2,4) = 35`, `W(3,4) = 293`,
    ///   `W(2,5) = 178`, `W(2,6) = 1132`;
    /// * the off-diagonal row `w(2; 3, t)` for `t = 3..=19`, completed to
    ///   `t = 19` by Ahmed, Kullmann and Snevily (arXiv:1102.5433).
    pub fn published_value(&self) -> Option<usize> {
        let mut sorted = self.k.clone();
        sorted.sort_unstable();
        match (self.k.len(), sorted.as_slice()) {
            (2, [3, 3]) => Some(9),
            (3, [3, 3, 3]) => Some(27),
            (4, [3, 3, 3, 3]) => Some(76),
            (2, [4, 4]) => Some(35),
            (3, [4, 4, 4]) => Some(293),
            (2, [5, 5]) => Some(178),
            (2, [6, 6]) => Some(1132),
            (2, [3, t]) => W_2_3_T.get(*t).copied().flatten(),
            _ => None,
        }
    }

    /// The problem for `points`, built from the per-colour progression lists.
    ///
    /// Present for symmetry with
    /// [`OffDiagonalSchur::minimal_problem`](crate::offdiag::OffDiagonalSchur::minimal_problem)
    /// and to keep drivers uniform: for this family the *full* list is already
    /// the subsumption-minimal one, so this is exactly
    /// [`ColouringFamily::problem`] and is documented as such rather than
    /// silently differing.
    ///
    /// # Errors
    ///
    /// As [`ColouringFamily::problem`], plus
    /// [`SearchError::PointOutOfRange`] above [`MAX_POINTS`].
    pub fn minimal_problem(&self, points: usize) -> Result<ColouringProblem, SearchError> {
        if points == 0 || points > MAX_POINTS {
            return Err(SearchError::PointOutOfRange {
                point: points,
                points: MAX_POINTS,
            });
        }
        self.problem(points)
    }
}

/// `w(2; 3, t)` for `t = 0..=19`, indexed by `t`; `None` where there is no
/// published value. See [`VanDerWaerden::published_value`].
const W_2_3_T: [Option<usize>; 20] = [
    None,
    None,
    None,
    Some(9),
    Some(18),
    Some(22),
    Some(32),
    Some(46),
    Some(58),
    Some(77),
    Some(97),
    Some(114),
    Some(135),
    Some(160),
    Some(186),
    Some(218),
    Some(238),
    Some(279),
    Some(312),
    Some(349),
];

impl ColouringFamily for VanDerWaerden {
    fn name(&self) -> &'static str {
        "vdw"
    }

    fn label(&self) -> String {
        if self.is_diagonal() {
            return format!("W({},{})", self.k.len(), self.k[0]);
        }
        let mut parameters = String::new();
        for (position, value) in self.k.iter().enumerate() {
            if position > 0 {
                parameters.push(',');
            }
            parameters.push_str(&value.to_string());
        }
        format!("w({};{parameters})", self.k.len())
    }

    fn colours(&self) -> usize {
        self.k.len()
    }

    /// The sets forbidden in **every** colour.
    ///
    /// Diagonal instances forbid the same progressions in every colour, and
    /// this is that list — the uniform encoding path, unchanged, with the full
    /// whole-palette symmetry break.
    ///
    /// For an off-diagonal instance it is **empty**: a progression of length
    /// `k` has exactly `k` points, so no set is forbidden in two colours with
    /// different `k`. That is the honest intersection and it is the weak
    /// direction the trait asks for — a caller that ignores the per-colour
    /// split gets a formula with *fewer* constraints, so its `unsat` still
    /// implies the real `unsat`. It is also useless, and
    /// [`ColouringFamily::colour_dependent`] is `true` in exactly that case, so
    /// [`ColouringFamily::problem`] never routes through here. A caller
    /// building a formula straight from this list would get a vacuous `sat`;
    /// use `problem()`.
    fn constraints(&self, points: usize) -> Vec<Vec<usize>> {
        if self.is_diagonal() {
            Self::progressions(self.k[0], points)
        } else {
            Vec::new()
        }
    }

    fn constraints_for_colour(&self, colour: usize, points: usize) -> Vec<Vec<usize>> {
        match self.k.get(colour - 1) {
            Some(&k) => Self::progressions(k, points),
            None => Vec::new(),
        }
    }

    /// `true` exactly for an off-diagonal instance.
    ///
    /// The diagonal case deliberately keeps the uniform path: the colours are
    /// genuinely interchangeable there, so the stock encoder's whole-palette
    /// symmetry break — a strictly stronger constraint than the block form —
    /// is sound, and it is worth a lot on `W(4,3)`.
    fn colour_dependent(&self) -> bool {
        !self.is_diagonal()
    }

    fn symmetry_blocks(&self) -> Vec<Vec<usize>> {
        self.parameter_blocks()
    }

    /// Brute force straight off the definition of an arithmetic progression,
    /// per colour.
    ///
    /// This shares no code with [`VanDerWaerden::progressions`] and is a
    /// different derivation, not a second copy: the encoder *generates* sets
    /// from a `(first term, common difference)` parameterisation over `[1, n]`,
    /// while this computes, by dynamic programming over **pairs of members of
    /// the colour class**, the length of the longest progression ending in each
    /// ordered pair — `chain(i, j) = chain(p, i) + 1` where
    /// `class[p] = 2·class[i] − class[j]` — and asks whether any reaches `k`.
    /// The encoder has no notion of a longest progression, and this has no
    /// notion of enumerating differences.
    ///
    /// The reported violation is deterministic: the lowest colour, then the
    /// first pair in `(last term, previous term)` order, reported as the final
    /// `k` terms of the progression that pair ends.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        for (index, &k) in self.k.iter().enumerate() {
            let colour = index + 1;
            let class: Vec<usize> = (1..=points)
                .filter(|&point| colouring[point - 1] == colour)
                .collect();
            if class.len() < k {
                continue;
            }
            let width = class.len();
            let mut slot = vec![usize::MAX; points + 1];
            for (position, &value) in class.iter().enumerate() {
                slot[value] = position;
            }
            // chain[i * width + j], for i < j, is the number of terms in the
            // longest progression inside the class whose last two terms are
            // class[i] then class[j]. Filled with j ascending and i ascending,
            // so the entry it reads (p < i < j) is always already written.
            let mut chain = vec![0usize; width * width];
            for j in 0..width {
                for i in 0..j {
                    let step = class[j] - class[i];
                    let mut length = 2usize;
                    if class[i] > step {
                        let previous = slot[class[i] - step];
                        if previous != usize::MAX {
                            length = chain[previous * width + i] + 1;
                        }
                    }
                    chain[i * width + j] = length;
                    if length >= k {
                        let mut members = Vec::with_capacity(k);
                        let mut value = class[j];
                        members.push(value);
                        for _ in 1..k {
                            value -= step;
                            members.push(value);
                        }
                        members.reverse();
                        return Some((members, colour));
                    }
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn progressions_are_enumerated_by_difference_then_start() {
        let sets = VanDerWaerden::progressions(3, 7);
        // d = 1: {1,2,3} .. {5,6,7}; d = 2: {1,3,5} .. {3,5,7}; d = 3: {1,4,7}.
        assert_eq!(sets[0], vec![1, 2, 3]);
        assert_eq!(sets[4], vec![5, 6, 7]);
        assert_eq!(sets[5], vec![1, 3, 5]);
        assert_eq!(sets[7], vec![3, 5, 7]);
        assert_eq!(sets[8], vec![1, 4, 7]);
        assert_eq!(sets.len(), 9);
    }

    #[test]
    fn progression_count_matches_the_enumeration() {
        let mut compared = 0usize;
        for k in 3..=8usize {
            for points in 1..=60usize {
                assert_eq!(
                    VanDerWaerden::progression_count(k, points),
                    VanDerWaerden::progressions(k, points).len(),
                    "closed form disagrees with the enumeration at k={k}, n={points}"
                );
                compared += 1;
            }
        }
        assert_eq!(compared, 6 * 60);
    }

    /// The measurement the off-diagonal Schur family's headline reduction asks
    /// for, run on this family: the answer is that it removes nothing.
    #[test]
    fn progressions_are_already_an_antichain() {
        let mut checked = 0usize;
        for k in 3..=6usize {
            for points in [10usize, 25, 40] {
                assert_eq!(
                    VanDerWaerden::subsumed_pair(k, points),
                    None,
                    "a length-{k} progression inside [1,{points}] contains another"
                );
                let sets = VanDerWaerden::progressions(k, points);
                let mut sorted = sets.clone();
                sorted.sort_unstable();
                sorted.dedup();
                assert_eq!(sorted.len(), sets.len(), "duplicate progressions at k={k}");
                checked += 1;
            }
        }
        assert_eq!(checked, 12);
    }

    #[test]
    fn first_violation_finds_a_progression_per_colour() {
        let family = VanDerWaerden::off_diagonal(3, 4).expect("family");
        // 2,4,6 is a 3-term progression in colour 1.
        let colouring = vec![2, 1, 2, 1, 2, 1, 2];
        assert_eq!(family.first_violation(&colouring), Some((vec![2, 4, 6], 1)));
        // Colour 2 needs four terms. Colour 1 is {5,6,8}, which has no
        // three-term progression, so the reported violation is colour 2's
        // {1,2,3,4}.
        let colouring = vec![2, 2, 2, 2, 1, 1, 2, 1];
        assert_eq!(
            family.first_violation(&colouring),
            Some((vec![1, 2, 3, 4], 2))
        );
    }

    #[test]
    fn first_violation_is_colour_scoped_not_colour_blind() {
        // Colour 2 is {1,2,3,4,7}, whose longest progression is the four-term
        // {1,2,3,4}; colour 1 is {5,6,8}, which has none of length three. So a
        // colour 2 that forbids five-term progressions is not violated...
        let colouring = vec![2, 2, 2, 2, 1, 1, 2, 1];
        let family = VanDerWaerden::off_diagonal(3, 5).expect("family");
        assert_eq!(family.first_violation(&colouring), None);
        // ...and the same colouring under a colour 2 that forbids four-term
        // progressions is. The set is monochromatic either way; what changes is
        // whose constraint it is.
        let stricter = VanDerWaerden::off_diagonal(3, 4).expect("family");
        assert_eq!(
            stricter.first_violation(&colouring),
            Some((vec![1, 2, 3, 4], 2))
        );
    }

    #[test]
    fn independent_and_encoder_views_agree_on_random_colourings() {
        let family = VanDerWaerden::off_diagonal(3, 5).expect("family");
        let problem = family.problem(30).expect("problem");
        let mut state = 0x2026_0813_u64;
        let mut compared = 0usize;
        let mut violations = 0usize;
        for _ in 0..256 {
            let colouring: Vec<usize> = (0..30)
                .map(|_| {
                    state = state
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1);
                    ((state >> 33) % 2) as usize + 1
                })
                .collect();
            let independent = family.first_violation(&colouring).is_none();
            let encoder = problem.first_monochromatic(&colouring).is_none();
            assert_eq!(
                independent, encoder,
                "independent and encoder views disagree on {colouring:?}"
            );
            if !independent {
                violations += 1;
            }
            compared += 1;
        }
        assert_eq!(compared, 256);
        assert!(violations > 0, "every sample was violation-free; vacuous");
    }

    #[test]
    fn diagonal_and_encoder_views_agree_on_random_colourings() {
        let family = VanDerWaerden::diagonal(3, 3).expect("family");
        assert!(
            !family.colour_dependent(),
            "diagonal keeps the uniform path"
        );
        let problem = family.problem(20).expect("problem");
        let mut state = 0x0813_2026_u64;
        let mut violations = 0usize;
        for _ in 0..256 {
            let colouring: Vec<usize> = (0..20)
                .map(|_| {
                    state = state
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1);
                    ((state >> 33) % 3) as usize + 1
                })
                .collect();
            assert_eq!(
                family.first_violation(&colouring).is_none(),
                problem.first_monochromatic(&colouring).is_none(),
                "independent and encoder views disagree on {colouring:?}"
            );
            if family.first_violation(&colouring).is_some() {
                violations += 1;
            }
        }
        assert!(violations > 0, "every sample was violation-free; vacuous");
    }

    #[test]
    fn diagonal_is_uniform_and_off_diagonal_is_not() {
        let diagonal = VanDerWaerden::diagonal(4, 3).expect("family");
        assert_eq!(diagonal.label(), "W(4,3)");
        assert!(!diagonal.colour_dependent());
        assert_eq!(diagonal.symmetry_blocks(), vec![vec![1, 2, 3, 4]]);
        assert!(!diagonal.problem(20).expect("problem").is_off_diagonal());

        let off = VanDerWaerden::off_diagonal(3, 20).expect("family");
        assert_eq!(off.label(), "w(2;3,20)");
        assert!(off.colour_dependent());
        assert_eq!(off.symmetry_blocks(), vec![vec![1], vec![2]]);
        let problem = off.problem(40).expect("problem");
        assert!(problem.is_off_diagonal());
        // Every constraint is scoped, and the two scopes have the right sizes.
        let colour_one = (0..problem.forbidden().len())
            .filter(|&index| problem.scope(index) == Some(1))
            .count();
        assert_eq!(colour_one, VanDerWaerden::progression_count(3, 40));
        let colour_two = problem.forbidden().len() - colour_one;
        assert_eq!(colour_two, VanDerWaerden::progression_count(20, 40));
    }

    #[test]
    fn off_diagonal_constraints_are_the_honest_empty_intersection() {
        let off = VanDerWaerden::off_diagonal(3, 4).expect("family");
        assert!(off.constraints(30).is_empty());
        let diagonal = VanDerWaerden::diagonal(2, 3).expect("family");
        assert_eq!(diagonal.constraints(30), VanDerWaerden::progressions(3, 30));
    }

    #[test]
    fn published_values_are_only_a_label() {
        assert_eq!(
            VanDerWaerden::diagonal(2, 3).expect("f").published_value(),
            Some(9)
        );
        assert_eq!(
            VanDerWaerden::diagonal(4, 3).expect("f").published_value(),
            Some(76)
        );
        assert_eq!(
            VanDerWaerden::off_diagonal(3, 19)
                .expect("f")
                .published_value(),
            Some(349)
        );
        // w(2;3,3) is W(2,3): the two spellings must not disagree.
        assert_eq!(
            VanDerWaerden::off_diagonal(3, 3)
                .expect("f")
                .published_value(),
            VanDerWaerden::diagonal(2, 3).expect("f").published_value()
        );
        // The open cell has no published value, and neither has an unstudied one.
        assert_eq!(
            VanDerWaerden::off_diagonal(3, 20)
                .expect("f")
                .published_value(),
            None
        );
        assert_eq!(
            VanDerWaerden::diagonal(5, 3).expect("f").published_value(),
            None
        );
    }

    #[test]
    fn short_progression_lengths_are_rejected() {
        assert!(VanDerWaerden::new(vec![]).is_err());
        assert!(VanDerWaerden::off_diagonal(2, 5).is_err());
        assert!(VanDerWaerden::diagonal(0, 3).is_err());
        assert!(
            VanDerWaerden::diagonal(2, 3)
                .expect("f")
                .minimal_problem(0)
                .is_err()
        );
        assert!(
            VanDerWaerden::diagonal(2, 3)
                .expect("f")
                .minimal_problem(MAX_POINTS + 1)
                .is_err()
        );
    }
}
