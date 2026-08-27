//! Colouring instances: the CNF encoding of record, and witnesses over it.
//!
//! Every family in this crate reduces to the same object — colour `1..=points`
//! with `1..=colours` so that no listed set is monochromatic — so there is one
//! encoder, not one per family. That encoder is
//! [`ColouringProblem::encode`], and its output is **byte-identical** to
//! `scripts/gen-rado-instance.py` on the Rado family. The Python script is the
//! generator of record named by the claim ledger; a divergence between the two
//! would silently invalidate every stored certificate, so
//! `tests/encoding_parity.rs` compares them directly — in two layers, against
//! `axeyum-cnf`'s encoder and against the Python script itself, the second
//! failing closed if the interpreter is absent.
//!
//! That test did not exist until 2026-08-16. This paragraph described it for
//! weeks while nothing ran; it was the last of the four prose-only guards found
//! on 2026-08-14. The encoders did agree, byte for byte, on the first run — the
//! invariant held and only the check was missing, which is the good version of
//! that discovery and not a reason to have left it unwritten.
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
//!
//! # Off-diagonal instances
//!
//! Group 2 above replays every forbidden set for every colour, and group 4 is
//! justified *only* by colour names being interchangeable. Neither holds for an
//! **off-diagonal** instance, where each colour forbids a different relation —
//! `S(3; s,t,u)` forbids `L(s)` in colour 1, `L(t)` in colour 2 and `L(u)` in
//! colour 3. [`ColouringProblem::per_colour`] builds such an instance: every
//! forbidden set carries the single colour it applies to, and symmetry breaking
//! is restricted to caller-supplied **blocks** of colours that really are
//! interchangeable (for `S(3;4,4,8)` that is `{1,2}` and `{3}`). The uniform
//! constructor [`ColouringProblem::new`] is unchanged and still emits the
//! byte-identical generator-of-record encoding.

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, WeightedAtMostEncoding, WeightedAtMostLimits,
    encode_weighted_at_most,
};

use crate::SearchError;

/// A finite colouring problem over `1..=points` with `1..=colours`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColouringProblem {
    points: usize,
    colours: usize,
    forbidden: Vec<Vec<usize>>,
    /// `scopes[i]` is the single colour forbidden set `i` applies to.
    ///
    /// `None` is the uniform case: every set applies to every colour. The
    /// distinction is not cosmetic — it decides both what
    /// [`ColouringProblem::encode`] emits and what counts as a violation.
    scopes: Option<Vec<usize>>,
    /// Blocks of mutually interchangeable colours, each ascending and disjoint.
    ///
    /// `None` means the legacy whole-palette breaking, which is what every
    /// uniform family wants and what the stored Rado certificates were produced
    /// with.
    symmetry_blocks: Option<Vec<Vec<usize>>>,
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
            scopes: None,
            symmetry_blocks: None,
        })
    }

    /// Builds an **off-diagonal** problem: `per_colour[c - 1]` is the list of
    /// sets that must not be monochromatic *in colour `c` only*.
    ///
    /// The sets are flattened colour-major — every set of colour 1, then every
    /// set of colour 2, and so on — and that order is the encoding order.
    ///
    /// `symmetry_blocks` names the groups of colours that are genuinely
    /// interchangeable, so that the least-element ordering is only imposed
    /// inside a group. Passing one block per colour disables symmetry breaking
    /// entirely; passing a single block containing every colour is only correct
    /// when every colour forbids the same sets. **Getting this wrong produces a
    /// wrong `unsat`,** so the argument for the blocks belongs with the family
    /// that supplies them.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] when `per_colour` does not
    /// have one entry per colour, when a set is empty or not strictly
    /// ascending, or when the blocks are not disjoint ascending subsets of
    /// `1..=colours`; [`SearchError::PointOutOfRange`] for a set naming a point
    /// outside `1..=points`; and [`SearchError::ColourOutOfRange`] for a block
    /// naming a colour outside `1..=colours`.
    pub fn per_colour(
        points: usize,
        colours: usize,
        per_colour: Vec<Vec<Vec<usize>>>,
        symmetry_blocks: Vec<Vec<usize>>,
    ) -> Result<Self, SearchError> {
        if per_colour.len() != colours {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "per-colour problem has {} constraint lists for {colours} colours",
                    per_colour.len()
                ),
            });
        }
        let mut flattened = Vec::new();
        let mut scopes = Vec::new();
        for (index, sets) in per_colour.into_iter().enumerate() {
            for set in sets {
                flattened.push(set);
                scopes.push(index + 1);
            }
        }
        let mut seen = vec![false; colours];
        for block in &symmetry_blocks {
            if block.windows(2).any(|w| w[0] >= w[1]) {
                return Err(SearchError::InvalidParameter {
                    what: format!("symmetry block {block:?} is not strictly ascending"),
                });
            }
            for &colour in block {
                if colour == 0 || colour > colours {
                    return Err(SearchError::ColourOutOfRange { colour, colours });
                }
                if seen[colour - 1] {
                    return Err(SearchError::InvalidParameter {
                        what: format!("colour {colour} appears in two symmetry blocks"),
                    });
                }
                seen[colour - 1] = true;
            }
        }
        // Validation of points/sets is shared with the uniform constructor.
        let mut problem = Self::new(points, colours, flattened)?;
        problem.scopes = Some(scopes);
        problem.symmetry_blocks = Some(symmetry_blocks);
        Ok(problem)
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

    /// The colour forbidden set `index` applies to, or `None` when it applies
    /// to every colour.
    ///
    /// Callers that decide whether a colouring violates a constraint must
    /// consult this — a set scoped to colour 2 is *not* violated by being
    /// monochromatic in colour 1. Use [`ColouringProblem::constraint_violated`]
    /// rather than re-deriving the rule.
    pub fn scope(&self, index: usize) -> Option<usize> {
        self.scopes
            .as_ref()
            .and_then(|scopes| scopes.get(index))
            .copied()
    }

    /// Whether this problem scopes any constraint to a single colour.
    pub fn is_off_diagonal(&self) -> bool {
        self.scopes.is_some()
    }

    /// The blocks of interchangeable colours symmetry breaking is imposed
    /// inside, or `None` for the whole palette.
    pub fn symmetry_blocks(&self) -> Option<&[Vec<usize>]> {
        self.symmetry_blocks.as_deref()
    }

    /// Whether `colouring` violates forbidden set `index`: every member shares
    /// a colour, and that colour is one the set applies to.
    ///
    /// Returns `false` for an out-of-range index or a colouring that does not
    /// cover every member.
    pub fn constraint_violated(&self, colouring: &[usize], index: usize) -> bool {
        let Some(set) = self.forbidden.get(index) else {
            return false;
        };
        let Some(&first) = colouring.get(set[0] - 1) else {
            return false;
        };
        if let Some(scope) = self.scope(index)
            && scope != first
        {
            return false;
        }
        set.iter()
            .all(|&point| colouring.get(point - 1) == Some(&first))
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
        for (index, set) in self.forbidden.iter().enumerate() {
            let mut emit = |colour: usize| -> Result<(), SearchError> {
                let lits = set
                    .iter()
                    .map(|&point| Ok(self.literal(point, colour)?.negated()))
                    .collect::<Result<Vec<_>, SearchError>>()?;
                formula.add_clause(CnfClause::new(lits))?;
                Ok(())
            };
            match self.scope(index) {
                Some(colour) => emit(colour)?,
                None => {
                    for colour in 1..=self.colours {
                        emit(colour)?;
                    }
                }
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
        match self.symmetry_blocks.clone() {
            None => self.encode_symmetry_breaking(&mut formula)?,
            Some(blocks) => self.encode_block_symmetry_breaking(&blocks, &mut formula)?,
        }
        Ok(formula)
    }

    /// Encodes the canonical problem and fixes the first `prefix_points` to a
    /// supplied witness's colours.
    ///
    /// This is a search restriction, not an equivalent encoding: UNSAT proves
    /// only that this particular prefix cannot extend. A SAT model remains a
    /// model of the canonical formula because this method only adds unit
    /// clauses. Callers promoting a model should still replay it against
    /// [`Self::encode`] without these units.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::WitnessLength`] when either the problem or the
    /// witness is shorter than `prefix_points`, and
    /// [`SearchError::InvalidParameter`] when the palettes differ.
    pub fn encode_with_witness_prefix(
        &self,
        witness: &Witness,
        prefix_points: usize,
    ) -> Result<CnfFormula, SearchError> {
        if prefix_points > self.points {
            return Err(SearchError::WitnessLength {
                expected: prefix_points,
                found: self.points,
            });
        }
        if prefix_points > witness.points() {
            return Err(SearchError::WitnessLength {
                expected: prefix_points,
                found: witness.points(),
            });
        }
        if witness.colours() != self.colours {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "witness has {} colours, problem has {}",
                    witness.colours(),
                    self.colours
                ),
            });
        }

        let mut formula = self.encode()?;
        for (offset, &colour) in witness.colouring().iter().take(prefix_points).enumerate() {
            formula.add_clause(CnfClause::new(vec![self.literal(offset + 1, colour)?]))?;
        }
        Ok(formula)
    }

    /// Encodes the canonical problem within a bounded Hamming distance of a
    /// supplied witness on its first `compared_points`.
    ///
    /// A point differs from the witness exactly when its witnessed-colour
    /// literal is false, because the canonical formula enforces one-hot
    /// colours. The generic weighted-at-most encoder therefore counts negated
    /// witnessed-colour literals with unit weights. Points after the compared
    /// prefix remain unrestricted.
    ///
    /// Like [`Self::encode_with_witness_prefix`], this is a search restriction.
    /// Restricted UNSAT is not an upper bound. Promote a SAT model only after
    /// projecting it with [`WeightedAtMostEncoding::project_source_model`] and
    /// replaying that projection against [`Self::encode`].
    ///
    /// # Errors
    ///
    /// Rejects an overlong comparison, a short witness, a palette mismatch,
    /// or weighted-cardinality resource exhaustion.
    pub fn encode_with_witness_hamming_ball(
        &self,
        witness: &Witness,
        compared_points: usize,
        max_changes: u64,
        limits: WeightedAtMostLimits,
    ) -> Result<WeightedAtMostEncoding, SearchError> {
        if compared_points > self.points {
            return Err(SearchError::WitnessLength {
                expected: compared_points,
                found: self.points,
            });
        }
        if compared_points > witness.points() {
            return Err(SearchError::WitnessLength {
                expected: compared_points,
                found: witness.points(),
            });
        }
        if witness.colours() != self.colours {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "witness has {} colours, problem has {}",
                    witness.colours(),
                    self.colours
                ),
            });
        }
        let canonical = self.encode()?;
        let terms = witness
            .colouring()
            .iter()
            .copied()
            .take(compared_points)
            .enumerate()
            .map(|(offset, colour)| Ok((self.literal(offset + 1, colour)?.negated(), 1)))
            .collect::<Result<Vec<_>, SearchError>>()?;
        Ok(encode_weighted_at_most(
            &canonical,
            &terms,
            max_changes,
            limits,
        )?)
    }

    /// Clause group 4, restricted to blocks of interchangeable colours.
    ///
    /// For a block `[c_0 < c_1 < … < c_{m-1}]` this orders the block's colour
    /// classes by least element: point `j` may take `c_idx` (`idx >= 1`) only
    /// if some `j' < j` takes `c_{idx-1}`. Colours outside every block are left
    /// unconstrained. A one-colour block emits nothing, so `blocks` of
    /// singletons is "no symmetry breaking at all".
    ///
    /// This differs from [`ColouringProblem::encode_symmetry_breaking`] in
    /// exactly one way when the block is the whole palette: point 1 is pinned
    /// to colour 1 by the `colours - 1` unit clauses `-v(1, i)` plus
    /// at-least-one, rather than by the single unit `v(1,1)`. Same models,
    /// different bytes — which is why the uniform path is kept verbatim.
    fn encode_block_symmetry_breaking(
        &self,
        blocks: &[Vec<usize>],
        formula: &mut CnfFormula,
    ) -> Result<(), SearchError> {
        for block in blocks {
            for (idx, &colour) in block.iter().enumerate().skip(1) {
                let previous = block[idx - 1];
                for point in 1..=self.points {
                    let mut lits = vec![self.literal(point, colour)?.negated()];
                    if point > idx {
                        for earlier in 1..point {
                            lits.push(self.literal(earlier, previous)?);
                        }
                    }
                    formula.add_clause(CnfClause::new(lits))?;
                }
            }
        }
        Ok(())
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

    /// Encode a complete witness as the one-hot assignment for this problem.
    ///
    /// This is the reverse of [`Self::decode_model`]. It does not silently
    /// rename colours: callers importing a witness whose palette is freely
    /// permutable may first use [`Witness::canonicalize_palette`].
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::WitnessLength`] unless the witness covers this
    /// exact domain, and rejects a witness built for a different palette.
    pub fn witness_assignment(&self, witness: &Witness) -> Result<Vec<bool>, SearchError> {
        if witness.points() != self.points {
            return Err(SearchError::WitnessLength {
                expected: self.points,
                found: witness.points(),
            });
        }
        if witness.colours() != self.colours {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "witness has {} colours, problem has {}",
                    witness.colours(),
                    self.colours
                ),
            });
        }
        let mut values = vec![false; self.variable_count()];
        for (offset, &colour) in witness.colouring().iter().enumerate() {
            values[self.variable(offset + 1, colour)?.index()] = true;
        }
        Ok(values)
    }

    /// The first forbidden set this colouring makes monochromatic, if any.
    ///
    /// This uses the problem's own constraint list, so it re-checks the
    /// *encoder's* view. A witness must additionally be checked against the
    /// family's independent enumerator — see
    /// [`ColouringFamily::verify_witness`](crate::ColouringFamily::verify_witness).
    pub fn first_monochromatic(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        (0..self.forbidden.len())
            .find(|&index| self.constraint_violated(colouring, index))
            .map(|index| {
                let set = self.forbidden[index].clone();
                let colour = colouring[set[0] - 1];
                (set, colour)
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

    /// Rename colours by order of first occurrence.
    ///
    /// The first observed colour becomes 1, the next previously unseen colour
    /// becomes 2, and so on. This is semantics-preserving only when the whole
    /// palette is interchangeable, as it is for uniform Rado, Schur, and van
    /// der Waerden instances. It must not be applied across distinct roles in
    /// an off-diagonal colouring problem.
    #[must_use]
    pub fn canonicalize_palette(&self) -> Self {
        let mut names = vec![0usize; self.colours + 1];
        let mut next = 1usize;
        let colouring = self
            .colouring
            .iter()
            .map(|&colour| {
                if names[colour] == 0 {
                    names[colour] = next;
                    next += 1;
                }
                names[colour]
            })
            .collect();
        Self {
            colours: self.colours,
            colouring,
        }
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
        assert_eq!(
            error,
            SearchError::PointOutOfRange {
                point: 4,
                points: 3
            }
        );
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
        let error = problem
            .decode_model(&values)
            .expect_err("point 1 is two-hot");
        assert_eq!(
            error,
            SearchError::ModelNotOneHot {
                point: 1,
                colours: 2
            }
        );
    }

    #[test]
    fn witness_palette_canonicalization_and_assignment_round_trip() {
        let witness = Witness::new(3, vec![3, 3, 1, 2]).unwrap();
        let canonical = witness.canonicalize_palette();
        assert_eq!(canonical.colouring(), &[1, 1, 2, 3]);

        let problem = ColouringProblem::new(4, 3, Vec::new()).unwrap();
        let assignment = problem.witness_assignment(&canonical).unwrap();
        assert_eq!(problem.decode_model(&assignment), Ok(canonical));
        assert_eq!(problem.encode().unwrap().evaluate(&assignment), Ok(true));
    }

    #[test]
    fn witness_prefix_encoding_only_appends_the_requested_units() {
        let problem = ColouringProblem::new(4, 3, Vec::new()).unwrap();
        let witness = Witness::new(3, vec![1, 2, 3, 1]).unwrap();
        let canonical = problem.encode().unwrap();
        let guided = problem.encode_with_witness_prefix(&witness, 2).unwrap();

        assert_eq!(
            &guided.clauses()[..canonical.clauses().len()],
            canonical.clauses()
        );
        assert_eq!(guided.clauses().len(), canonical.clauses().len() + 2);
        assert_eq!(
            guided.clauses()[canonical.clauses().len()].lits(),
            &[problem.literal(1, 1).unwrap()]
        );
        assert_eq!(
            guided.clauses()[canonical.clauses().len() + 1].lits(),
            &[problem.literal(2, 2).unwrap()]
        );
        let assignment = problem.witness_assignment(&witness).unwrap();
        assert_eq!(guided.evaluate(&assignment), Ok(true));
    }

    #[test]
    fn witness_prefix_encoding_rejects_bad_lengths_and_palette() {
        let problem = ColouringProblem::new(4, 3, Vec::new()).unwrap();
        let short = Witness::new(3, vec![1, 2]).unwrap();
        assert_eq!(
            problem.encode_with_witness_prefix(&short, 3),
            Err(SearchError::WitnessLength {
                expected: 3,
                found: 2
            })
        );
        assert!(matches!(
            problem.encode_with_witness_prefix(&Witness::new(2, vec![1, 2]).unwrap(), 2),
            Err(SearchError::InvalidParameter { .. })
        ));
        assert_eq!(
            problem.encode_with_witness_prefix(&short, 5),
            Err(SearchError::WitnessLength {
                expected: 5,
                found: 4
            })
        );
    }

    #[test]
    fn witness_hamming_ball_counts_changed_points_and_projects() {
        use axeyum_cnf::{ProofSolveOutcome, solve_with_drat_proof};

        let problem = ColouringProblem::new(4, 3, Vec::new()).unwrap();
        let witness = Witness::new(3, vec![1, 2, 3, 1]).unwrap();
        let exact = problem
            .encode_with_witness_hamming_ball(&witness, 4, 0, WeightedAtMostLimits::default())
            .unwrap();
        let ProofSolveOutcome::Sat(model) = solve_with_drat_proof(exact.formula()) else {
            panic!("the center of a zero-radius ball must remain satisfiable")
        };
        let source = exact.project_source_model(model.values()).unwrap();
        assert_eq!(problem.decode_model(&source), Ok(witness.clone()));
        assert_eq!(problem.encode().unwrap().evaluate(&source), Ok(true));

        let changed = Witness::new(3, vec![1, 2, 3, 2]).unwrap();
        let changed_assignment = problem.witness_assignment(&changed).unwrap();
        let mut pinned = exact.formula().clone();
        for (index, value) in changed_assignment.iter().copied().enumerate() {
            let literal = CnfLit::positive(CnfVar::new(index).unwrap());
            pinned
                .add_clause(CnfClause::new(vec![if value {
                    literal
                } else {
                    literal.negated()
                }]))
                .unwrap();
        }
        assert!(matches!(
            solve_with_drat_proof(&pinned),
            ProofSolveOutcome::Unsat(_)
        ));
        let radius_one = problem
            .encode_with_witness_hamming_ball(&witness, 4, 1, WeightedAtMostLimits::default())
            .unwrap();
        let mut pinned = radius_one.formula().clone();
        for (index, value) in changed_assignment.iter().copied().enumerate() {
            let literal = CnfLit::positive(CnfVar::new(index).unwrap());
            pinned
                .add_clause(CnfClause::new(vec![if value {
                    literal
                } else {
                    literal.negated()
                }]))
                .unwrap();
        }
        assert!(matches!(
            solve_with_drat_proof(&pinned),
            ProofSolveOutcome::Sat(_)
        ));
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
