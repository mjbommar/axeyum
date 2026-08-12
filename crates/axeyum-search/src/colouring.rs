//! Colouring instances: the CNF encoding of record, and witnesses over it.
//!
//! Every family in this crate reduces to the same object — colour `1..=points`
//! with `1..=colours` so that no listed set is monochromatic — so there is one
//! encoder, not one per family. That encoder is
//! [`ColouringProblem::encode`], and its output is **byte-identical** to
//! `scripts/gen-rado-instance.py` on the Rado family. The Python script is the
//! generator of record named by the claim ledger; a divergence between the two
//! would silently invalidate every stored certificate, so
//! `tests/encoding_parity.rs` compares them directly.
//!
//! # Variable convention
//!
//! `v(j, i) = (j - 1) * colours + i`, one-based in DIMACS — "point `j` has
//! colour `i`". The encoder emits, as its **first `points` clauses**, the
//! at-least-one clause `{v(j,1) .. v(j,colours)}` for every point `j`. The cover
//! argument in [`crate::cover`] depends on those clauses being present verbatim,
//! and checks it rather than assuming it.
//!
//! # Clause groups, in emission order
//!
//! 1. at-least-one: every point gets a colour;
//! 2. for each forbidden set and each colour: not all of its members take that
//!    colour;
//! 3. at-most-one: no point takes two colours;
//! 4. symmetry breaking: point 1 takes colour 1, and point `j` may take colour
//!    `i > 1` only if some `j' < j` takes colour `i - 1`. Colour classes are
//!    thereby ordered by least element, which is sound because colour names are
//!    interchangeable.

use axeyum_cnf::{CnfClause, CnfFormula, CnfLit, CnfVar};

use crate::SearchError;

/// A finite colouring problem over `1..=points` with `1..=colours`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColouringProblem {
    points: usize,
    colours: usize,
    forbidden: Vec<Vec<usize>>,
}

impl ColouringProblem {
    /// Builds a problem from its forbidden sets.
    ///
    /// The sets are kept in the caller's order — the encoding is order
    /// sensitive by design, because byte-identity with the generator of record
    /// is a property this crate tests.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] when `points` or `colours` is
    /// zero or a forbidden set is empty or not strictly ascending, and
    /// [`SearchError::PointOutOfRange`] when a set names a point outside
    /// `1..=points`.
    pub fn new(
        points: usize,
        colours: usize,
        forbidden: Vec<Vec<usize>>,
    ) -> Result<Self, SearchError> {
        if points == 0 {
            return Err(SearchError::InvalidParameter {
                what: "a colouring problem needs at least one point".to_string(),
            });
        }
        if colours == 0 {
            return Err(SearchError::InvalidParameter {
                what: "a colouring problem needs at least one colour".to_string(),
            });
        }
        for set in &forbidden {
            if set.is_empty() {
                return Err(SearchError::InvalidParameter {
                    what: "a forbidden set must name at least one point".to_string(),
                });
            }
            if set.windows(2).any(|w| w[0] >= w[1]) {
                return Err(SearchError::InvalidParameter {
                    what: format!("forbidden set {set:?} is not strictly ascending"),
                });
            }
            for &point in set {
                if point == 0 || point > points {
                    return Err(SearchError::PointOutOfRange { point, points });
                }
            }
        }
        Ok(Self {
            points,
            colours,
            forbidden,
        })
    }

    /// Number of points, i.e. the `n` of the instance.
    pub fn points(&self) -> usize {
        self.points
    }

    /// Number of colours, i.e. the `k` of the instance.
    pub fn colours(&self) -> usize {
        self.colours
    }

    /// The forbidden sets, in encoding order.
    pub fn forbidden(&self) -> &[Vec<usize>] {
        &self.forbidden
    }

    /// Number of CNF variables, `points * colours`.
    pub fn variable_count(&self) -> usize {
        self.points * self.colours
    }

    /// The variable `v(point, colour)`.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::PointOutOfRange`] or
    /// [`SearchError::ColourOutOfRange`] for out-of-range arguments, and
    /// [`SearchError::Cnf`] when the index does not fit a [`CnfVar`].
    pub fn variable(&self, point: usize, colour: usize) -> Result<CnfVar, SearchError> {
        if point == 0 || point > self.points {
            return Err(SearchError::PointOutOfRange {
                point,
                points: self.points,
            });
        }
        if colour == 0 || colour > self.colours {
            return Err(SearchError::ColourOutOfRange {
                colour,
                colours: self.colours,
            });
        }
        Ok(CnfVar::new((point - 1) * self.colours + colour - 1)?)
    }

    /// The positive literal for `v(point, colour)`.
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::variable`].
    pub fn literal(&self, point: usize, colour: usize) -> Result<CnfLit, SearchError> {
        Ok(CnfLit::positive(self.variable(point, colour)?))
    }

    /// The at-least-one clause `{v(point,1) .. v(point,colours)}`.
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::variable`].
    pub fn at_least_one(&self, point: usize) -> Result<Vec<CnfLit>, SearchError> {
        (1..=self.colours).map(|i| self.literal(point, i)).collect()
    }

    /// Encodes the problem to CNF.
    ///
    /// The result is byte-identical, through
    /// [`to_dimacs`](CnfFormula::to_dimacs), to `scripts/gen-rado-instance.py`
    /// for the Rado family. See the module docs for the clause groups and their
    /// order.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::Cnf`] if the formula rejects a clause, which can
    /// only happen if the variable indices overflow.
    pub fn encode(&self) -> Result<CnfFormula, SearchError> {
        let mut formula = CnfFormula::new(self.variable_count());
        for point in 1..=self.points {
            formula.add_clause(CnfClause::new(self.at_least_one(point)?))?;
        }
        for set in &self.forbidden {
            for colour in 1..=self.colours {
                let lits = set
                    .iter()
                    .map(|&point| Ok(self.literal(point, colour)?.negated()))
                    .collect::<Result<Vec<_>, SearchError>>()?;
                formula.add_clause(CnfClause::new(lits))?;
            }
        }
        for point in 1..=self.points {
            for first in 1..=self.colours {
                for second in (first + 1)..=self.colours {
                    formula.add_clause(CnfClause::new(vec![
                        self.literal(point, first)?.negated(),
                        self.literal(point, second)?.negated(),
                    ]))?;
                }
            }
        }
        self.encode_symmetry_breaking(&mut formula)?;
        Ok(formula)
    }

    /// Clause group 4: colour classes ordered by least element.
    fn encode_symmetry_breaking(&self, formula: &mut CnfFormula) -> Result<(), SearchError> {
        formula.add_clause(CnfClause::new(vec![self.literal(1, 1)?]))?;
        for point in 2..=self.points {
            for colour in 2..=self.colours {
                let mut lits = vec![self.literal(point, colour)?.negated()];
                if point > colour - 1 {
                    for earlier in 1..point {
                        lits.push(self.literal(earlier, colour - 1)?);
                    }
                }
                formula.add_clause(CnfClause::new(lits))?;
            }
        }
        Ok(())
    }

    /// Decodes a CNF model into a colouring, one entry per point.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::WitnessLength`] if the model is shorter than the
    /// variable count and [`SearchError::ModelNotOneHot`] if it does not give
    /// some point exactly one colour.
    pub fn decode_model(&self, values: &[bool]) -> Result<Witness, SearchError> {
        if values.len() < self.variable_count() {
            return Err(SearchError::WitnessLength {
                expected: self.variable_count(),
                found: values.len(),
            });
        }
        let mut colouring = Vec::with_capacity(self.points);
        for point in 1..=self.points {
            let mut chosen = 0usize;
            let mut count = 0usize;
            for colour in 1..=self.colours {
                if values[self.variable(point, colour)?.index()] {
                    chosen = colour;
                    count += 1;
                }
            }
            if count != 1 {
                return Err(SearchError::ModelNotOneHot {
                    point,
                    colours: count,
                });
            }
            colouring.push(chosen);
        }
        Witness::new(self.colours, colouring)
    }

    /// The first forbidden set this colouring makes monochromatic, if any.
    ///
    /// This uses the problem's own constraint list, so it re-checks the
    /// *encoder's* view. A witness must additionally be checked against the
    /// family's independent enumerator — see
    /// [`ColouringFamily::verify_witness`](crate::ColouringFamily::verify_witness).
    pub fn first_monochromatic(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        self.forbidden.iter().find_map(|set| {
            let first = *colouring.get(set[0] - 1)?;
            set.iter()
                .all(|&point| colouring.get(point - 1) == Some(&first))
                .then(|| (set.clone(), first))
        })
    }
}

/// A colouring offered as evidence that an instance is satisfiable.
///
/// A witness is *untrusted* until checked. Nothing in this crate accepts one
/// without running it through an independent enumerator first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    colours: usize,
    colouring: Vec<usize>,
}

impl Witness {
    /// Builds a witness from a colouring, `colouring[j - 1]` being the colour
    /// of point `j`.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] for an empty colouring and
    /// [`SearchError::ColourOutOfRange`] for a colour outside `1..=colours`.
    pub fn new(colours: usize, colouring: Vec<usize>) -> Result<Self, SearchError> {
        if colouring.is_empty() {
            return Err(SearchError::InvalidParameter {
                what: "a witness must colour at least one point".to_string(),
            });
        }
        for &colour in &colouring {
            if colour == 0 || colour > colours {
                return Err(SearchError::ColourOutOfRange { colour, colours });
            }
        }
        Ok(Self { colours, colouring })
    }

    /// Parses a whitespace-separated colouring, the format the search tools
    /// read and write.
    ///
    /// # Errors
    ///
    /// As [`Witness::new`], plus [`SearchError::InvalidParameter`] for a token
    /// that is not a number.
    pub fn parse(colours: usize, text: &str) -> Result<Self, SearchError> {
        let colouring = text
            .split_whitespace()
            .map(|token| {
                token
                    .parse::<usize>()
                    .map_err(|_| SearchError::InvalidParameter {
                        what: format!("witness token {token:?} is not a colour"),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(colours, colouring)
    }

    /// Number of points coloured.
    pub fn points(&self) -> usize {
        self.colouring.len()
    }

    /// Number of colours the witness was built against.
    pub fn colours(&self) -> usize {
        self.colours
    }

    /// The colouring, `colouring()[j - 1]` being the colour of point `j`.
    pub fn colouring(&self) -> &[usize] {
        &self.colouring
    }

    /// Renders the colouring as a single whitespace-separated line.
    pub fn render(&self) -> String {
        let mut out = String::new();
        for (position, colour) in self.colouring.iter().enumerate() {
            if position > 0 {
                out.push(' ');
            }
            out.push_str(&colour.to_string());
        }
        out.push('\n');
        out
    }

    /// A prefix of this witness covering `points` points.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::WitnessLength`] if the witness is shorter.
    pub fn truncated(&self, points: usize) -> Result<Self, SearchError> {
        if points > self.colouring.len() {
            return Err(SearchError::WitnessLength {
                expected: points,
                found: self.colouring.len(),
            });
        }
        Self::new(self.colours, self.colouring[..points].to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn triangle_problem() -> ColouringProblem {
        ColouringProblem::new(3, 2, vec![vec![1, 2, 3]]).expect("valid problem")
    }

    #[test]
    fn variable_convention_is_one_based_row_major() {
        let problem = triangle_problem();
        assert_eq!(problem.variable(1, 1).expect("v(1,1)").dimacs(), 1);
        assert_eq!(problem.variable(1, 2).expect("v(1,2)").dimacs(), 2);
        assert_eq!(problem.variable(2, 1).expect("v(2,1)").dimacs(), 3);
        assert_eq!(problem.variable(3, 2).expect("v(3,2)").dimacs(), 6);
    }

    #[test]
    fn at_least_one_clauses_come_first() {
        let problem = triangle_problem();
        let formula = problem.encode().expect("encode");
        for point in 1..=3 {
            let clause = &formula.clauses()[point - 1];
            assert_eq!(clause.lits(), problem.at_least_one(point).expect("alo"));
        }
    }

    #[test]
    fn out_of_range_points_are_rejected() {
        let error = ColouringProblem::new(3, 2, vec![vec![1, 4]]).expect_err("point 4 of 3");
        assert_eq!(error, SearchError::PointOutOfRange { point: 4, points: 3 });
    }

    #[test]
    fn unsorted_forbidden_sets_are_rejected() {
        let error = ColouringProblem::new(3, 2, vec![vec![3, 1]]).expect_err("descending");
        assert!(matches!(error, SearchError::InvalidParameter { .. }));
    }

    #[test]
    fn decode_model_rejects_a_point_with_two_colours() {
        let problem = triangle_problem();
        let mut values = vec![false; problem.variable_count()];
        values[0] = true;
        values[1] = true;
        values[2] = true;
        values[4] = true;
        let error = problem.decode_model(&values).expect_err("point 1 is two-hot");
        assert_eq!(
            error,
            SearchError::ModelNotOneHot {
                point: 1,
                colours: 2
            }
        );
    }

    #[test]
    fn witness_round_trips_through_text() {
        let witness = Witness::new(3, vec![1, 2, 3, 1]).expect("witness");
        let parsed = Witness::parse(3, &witness.render()).expect("parse");
        assert_eq!(parsed, witness);
        assert_eq!(witness.render(), "1 2 3 1\n");
    }

    #[test]
    fn first_monochromatic_finds_the_encoder_view_violation() {
        let problem = triangle_problem();
        assert_eq!(
            problem.first_monochromatic(&[2, 2, 2]),
            Some((vec![1, 2, 3], 2))
        );
        assert_eq!(problem.first_monochromatic(&[1, 2, 1]), None);
    }
}
